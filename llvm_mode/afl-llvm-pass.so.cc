/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <fstream>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Demangle/Demangle.h"

using namespace llvm;


namespace {
  class stringStruct {
    public:
      std::vector<int> idx;
      int structCount;
      std::vector<int> structIdx;
      std::vector<stringStruct*> structs;
      bool isStringRelated;
      
      stringStruct(bool isString,int count=0): isStringRelated(isString),structCount(count) {}

      bool isStruct();
  };
}

bool stringStruct::isStruct(){//检查vector是否都为空,都为空不是为struct。
  if(!idx.empty()) return true;
  if(structCount != 0) return true;
  if(!structIdx.empty()) return true;
  if(!structs.empty()) return true;

  return false;
}



namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      std::unordered_map<BasicBlock *, u32> basicBlockMap;
      std::unordered_map<u32,u32> passSet;
      std::unordered_set<std::string> handledFunc;
      std::unordered_map<Value*, std::unordered_set<std::string>> stringValue;
      std::unordered_map<Value*, stringStruct*> valueStringStruct;
      std::unordered_map<DIType*,stringStruct*> processedTypes;
       // 用于存储文件路径
      std::unordered_set<std::string> SourceFiles;
     
      AFLCoverage() : ModulePass(ID) { }

      bool doInitialization(Module &M) override;
      bool runOnModule(Module &M) override;

      std::string isInterceptedFunction(std::string &calledName); 
      void saveToXml(const std::string &filename, const std::unordered_map<unsigned int, std::unordered_set<std::string>> &mapping);
      void handleInst(Instruction *inst,  std::unordered_map<Value*, std::unordered_set<std::string>> &localStringValue);
      void handleFunc(Function *func);
      std::unordered_set<std::string> isOprendStringRelated(Value* value,std::unordered_map<Value*, std::unordered_set<std::string>> &localStringValue);
      bool isMetadateStringRelated(Value* scope,Value* value);
      stringStruct* isTypeStringRelated(DIType* dtype);
      bool isI8Related(Type *type);
      void isHandleTargetFunc(std::string &funcName,Instruction * inst,  std::unordered_map<Value*, std::unordered_set<std::string>> &localStringValue);
      Value* getValue(Value * value);
      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

char AFLCoverage::ID = 0;

bool AFLCoverage::doInitialization(Module &M) {
  /* Initialize id for each basic block */
  u32 rand_seed;
  char *rand_seed_str = getenv("AFL_RAND_SEED");

  if (rand_seed_str && sscanf(rand_seed_str, "%u", &rand_seed))
    srand(rand_seed);

  for (auto &F : M)
    for (auto &BB : F) {
      u32 cur_loc = AFL_R(MAP_SIZE);
      basicBlockMap.insert(std::pair<BasicBlock *, u32>(&BB, cur_loc));
    }

  for (GlobalVariable &gvar : M.globals()) {

    Metadata* md = gvar.getMetadata("dbg");
    
    if(md){
      if(isa<DIGlobalVariableExpression>(md)){
      
        DIGlobalVariableExpression *divExpr = dyn_cast<DIGlobalVariableExpression>(md);
        DIGlobalVariable *divGvar = divExpr->getVariable();
      
        stringStruct *res = isTypeStringRelated(divGvar->getType());

        if(res->isStringRelated){
          // 是结构体就认为和string无关，同时保留了结构体内和string相关的成员记录。
          if(res->isStruct()) valueStringStruct[&gvar] = res;
          else stringValue[&gvar].insert("unknown");
        }

        // if(isTypeStringRelated(divGvar->getType(),&gvar)){
        //   stringValue[&gvar].insert("unknown");        
        // }
      }
    }
  }

  return true;
}


std::string AFLCoverage::isInterceptedFunction(std::string &calledName) {
  static const std::unordered_set<std::string> CFunctions = {
    "isalnum",  "isalpha",  "islower",  "isupper",  "isdigit",  "isxdigit",
    "iscntrl",  "isgraph",  "isspace", "isblank", "isprint", "ispunct",
    "tolower", "toupper", "atof", "atoi", "atol", "atoll",
    "strfromf", "strfromd", "strfroml", "strtoimax", "strtoumax", "strcpy",
    "strcpy_s", "stncpy", "strcat", "strcat_s", "strncat", "strxfrm",
    "strdup", "strndup", "strlen", "strlen_s", "strcmp", "strncmp",
    "strcoll", "strchr", "strrchr", "strspn", "strcspn", "strpbrk",
    "strstr", "strtok", "strtok_s", "memchr", "memcmp", "memset",
    "memcpy", "memcpy_s", "memmove", "memmove_s","memccpy", "strerror",
    "strerror_s", "strerrorlen_s", };
    
  static const std::unordered_set<std::string> CppFunctions = {
    "at","front", "back", "data", "empty", "length", "size","assign",
    "max_size", "clear", "insert", "insert_range", "erase", "erase_if",
    "push_back", "pop_back", "append", "append_range", "replace",
    "replace_with_range", "copy", "resize", "resize_and_overwrite", "swap", "find",
    "rfind", "find_first_of", "find_first_not_of", "find_last_of", "find_last_not_of", "compare",
    "starts_with", "ends_with", "contains", "substr", "stoi", "stol",
    "stoll", "stoul", "stoull", "stof", "stod", "stold","operator>","operator<",
    "operator<=","operator>=","operator==","operator!=","operator=","operator<=>",
    "operator+","operator+=","operator[]","to_string",
  };

  std::string ans = "" ;
  for (const auto& func : CFunctions) {
    if (calledName.find(func) != std::string::npos) {
      if(func.length() > ans.length()) ans = func;
    }
  }
  if(ans !="") return ans;

  if (calledName.find("basic_string") == std::string::npos) {
    return ""; // 如果不包含，返回空字符串
  }

  // 检查是否包含 "char_traits"
  if (calledName.find("char_traits") == std::string::npos) {
    return ""; // 如果不包含，返回空字符串
  }

  // 遍历 kInterceptedFunctions，查找是否存在任何一个函数名
  for (const auto& func : CppFunctions) {
    if (calledName.find(func) != std::string::npos) {
      if(func.length() > ans.length()) ans = func;
    }
  }
  return ans; // 找到匹配的函数名，返回它
}

void AFLCoverage::saveToXml(const std::string &filename, 
  const std::unordered_map<unsigned int, std::unordered_set<std::string>> &mapping) {
  std::unordered_map<std::string,unsigned int> typeMap; 

  std::ofstream outFile(filename);
  if (outFile.is_open()) {

    outFile << "<mapping>\n";
    for (const auto &pair : mapping) {
      outFile << "  <entry>\n";
      outFile << "    <Index>" << pair.first << "</Index>\n";
      
      for (std::string type : pair.second) {
        outFile << "    <Type>" << type << "</Type>\n";
        typeMap[type]++;
      }
      outFile << "  </entry>\n";
    }
    outFile << "</mapping>\n";
    
    outFile << "<The BrType>\n";
    
    for(auto typeNum : typeMap){
      outFile << "  Type: "<<typeNum.first<<",  Num: "<<typeNum.second<<"\n";
    }
    outFile << "</The BrType>\n";
    
    outFile.close();
    std::cout << "Data saved to XML file." << std::endl;
  
  } else {
    std::cerr << "Unable to open file for writing." << std::endl;
  }
}

std::unordered_set<std::string> AFLCoverage::isOprendStringRelated
  (Value *value,std::unordered_map<Value*, std::unordered_set<std::string>> &localStringValue){

  if(localStringValue.find(value) != localStringValue.end()){
    return localStringValue[value];
  }else if(stringValue.find(value) != stringValue.end()){
    return stringValue[value];
  }else if(isa<ConstantExpr>(value)){
    
    ConstantExpr* constExpr = dyn_cast<ConstantExpr>(value);
    if(constExpr->getOpcode() == Instruction::GetElementPtr){
      Value *basePtr =constExpr->getOperand(0);
      return isOprendStringRelated(basePtr,localStringValue);
    }
  }

  return std::unordered_set<std::string>();
}

bool AFLCoverage::isMetadateStringRelated(Value* scope,Value *value){

  if(isa<MetadataAsValue>(scope)){

    Metadata* md = cast<MetadataAsValue>(*scope).getMetadata();
    
    if (isa<DILocalVariable>(*md)) {
      
      DIType* dtype = cast<DILocalVariable>(*md).getType();
      if(dtype==nullptr) return false;
      stringStruct *res = isTypeStringRelated(dtype);

      if(res->isStringRelated){
        if(res->isStruct()){ // 认为是和结构体字符串无关，但是有valueStringStruct进行记录：结构体属性可能和string有关。
          valueStringStruct[value] = res;
          return false;
        }
        return true;
      }
    }
  }
  return false;
}

stringStruct* AFLCoverage::isTypeStringRelated(DIType* dtype){

  if(processedTypes.find(dtype) != processedTypes.end()){
    
    return processedTypes[dtype];
  }

  processedTypes[dtype] = new stringStruct(false);
  
  /* handle dtype because compositeType */
  if(isa<DICompositeType>(dtype)){
    
    DICompositeType* dctype = dyn_cast<DICompositeType>(dtype);

    if(!dctype->getName().empty() && (0==dctype->getName().str().compare("basic_string<char, std::char_traits<char>, std::allocator<char> >"))){
      processedTypes[dctype] = new stringStruct(true);
      return processedTypes[dctype];
    }

    if(dctype->getBaseType()!= nullptr){
      processedTypes[dctype] = isTypeStringRelated(dctype->getBaseType());
      return processedTypes[dctype];  
    }
       
    DINodeArray es = dctype->getElements();
    int idx = 0;
    stringStruct* res = new stringStruct(false);

    for (auto *element : es) {
      
      if(isa<DIType>(element)){  
        DIType *e = dyn_cast<DIType>(element);
        
        stringStruct* eStruct = isTypeStringRelated(e);
        if(eStruct->isStringRelated){

          if(!res->isStringRelated) res->isStringRelated = true;
          if(eStruct->isStruct()){
            res->structCount++;
            res->structIdx.push_back(idx);
            res->structs.push_back(eStruct);
          }else{
            res->idx.push_back(idx);
          }
        }    
      }
      idx++;
    }   
    processedTypes[dtype] = res;
    return res;

  }else if(isa<DIDerivedType>(dtype)){

    DIDerivedType * ddtype = dyn_cast<DIDerivedType>(dtype);
    DIType *baseType = ddtype->getBaseType();

    if(baseType != nullptr){
      stringStruct* res = isTypeStringRelated(baseType);
      
      if(res->isStringRelated){
        processedTypes[dtype] = res;
      }

      return res;
    } 

  }else if(isa<DIBasicType>(dtype)){
    DIBasicType *btype = dyn_cast<DIBasicType>(dtype);
    
    if(!dtype->getName().empty()){
      if(!dtype->getName().str().compare("char")) {
        stringStruct* res = new stringStruct(true);
        processedTypes[dtype] = res;
        return res;
      }
    }
  }

  return new stringStruct(false);
}

// 类型是否是I8类型相关
bool AFLCoverage::isI8Related(Type *type){

  if (type->isIntegerTy(8)) 
    return true;
  else if (type->isPointerTy()) {

    Type *elementType = type->getPointerElementType();
    return isI8Related(elementType);

  } else if (ArrayType *arrType = dyn_cast<ArrayType>(type))   
    return isI8Related(arrType);
  
  return false;
}

//  获取 实际需要进行类别跟踪的Value
Value* AFLCoverage::getValue(Value * value){
  
  if(isa<GetElementPtrInst>(value)){
    
    GetElementPtrInst* getPtrInst = dyn_cast<GetElementPtrInst>(value);
    return getPtrInst->getPointerOperand();

  }else if(isa<LoadInst>(value)){
    
    LoadInst* loadInst = dyn_cast<LoadInst>(value);
    return loadInst->getPointerOperand();
  }
}


// 处理 函数调用指令中设计 赋值，复制，等操作的类别跟踪，即单纯返回值类别跟踪无法跟踪的部分。
void AFLCoverage::isHandleTargetFunc(std::string &funcName,Instruction *inst,  std::unordered_map<Value*, std::unordered_set<std::string>> &localStringValue){

  CallBase *callBase = dyn_cast<CallBase>(inst);
  
  if(!funcName.compare("substr")    ||!funcName.compare("assign")
    ||!funcName.compare("insert")   ||!funcName.compare("replace")
    ||!funcName.compare("append")   ||!funcName.compare("copy")
    ||!funcName.compare("to_string")||!funcName.compare("operator=")){
    
    Value *target = callBase->getArgOperand(0);
    Value *src = callBase->getArgOperand(1);

    if(target != nullptr && src != nullptr){
      std::unordered_set<std::string> typeSet = localStringValue[src];
      localStringValue[target].insert(typeSet.begin(),typeSet.end());
      localStringValue[target].insert(funcName);
    }
    
  }else if(!funcName.compare("swap")){
    
    Value *arg1 = callBase->getArgOperand(0);
    Value *arg2 = callBase->getArgOperand(1);

    if(arg1 != nullptr && arg2 !=nullptr){
      std::unordered_set<std::string> typeSet1 = localStringValue[arg1];
      std::unordered_set<std::string> typeSet2 = localStringValue[arg2];
      localStringValue[arg1] = typeSet2;
      localStringValue[arg2] = typeSet1;
      localStringValue[arg1].insert(funcName);
      localStringValue[arg2].insert(funcName);
    }
     
  }else if(!funcName.compare("pop_back")||!funcName.compare("push_back")
    ||!funcName.compare("clear") ||!funcName.compare("resize")
    ||!funcName.compare("erase")){
    
    Value *obj = callBase->getArgOperand(0);
    if(obj != nullptr)  localStringValue[obj].insert(funcName);

  }else if( !funcName.compare("strcat_s") ||!funcName.compare("strcpy_s")
    ||!funcName.compare("memcpy_s") ){
    
    Value *dest = callBase->getArgOperand(0);
    Value *src = callBase->getArgOperand(2);
    dest = getValue(dest);src = getValue(src);
    
    if( dest != nullptr && src != nullptr){
      std::unordered_set<std::string> typeSet = localStringValue[src];
      localStringValue[dest].insert(typeSet.begin(),typeSet.end());
      localStringValue[dest].insert(funcName);
    }

  }else if(!funcName.compare("strcpy") 
    ||!funcName.compare("strncpy")  ||!funcName.compare("strcat ")
    ||!funcName.compare("strncat")  ||!funcName.compare("memcpy ")
    ||!funcName.compare("memccpy")){

    Value *arg1 = callBase->getArgOperand(0);
    Value *arg2 = callBase->getArgOperand(1);
    arg1 = getValue(arg1); arg2 = getValue(arg2);
    
    if(arg1 != nullptr && arg2 != nullptr){
      std::unordered_set<std::string> typeSet1 = localStringValue[arg1];
      std::unordered_set<std::string> typeSet2 = localStringValue[arg2];
      localStringValue[arg1] = typeSet2;
      localStringValue[arg2] = typeSet1;
      localStringValue[arg1].insert(funcName);
      localStringValue[arg2].insert(funcName);
    }
    
  }else if(!funcName.compare("memset")){

    Value *src = callBase->getArgOperand(0);
    src = getValue(src);
    if(src != nullptr)
      localStringValue[src].insert(funcName);

  }else if(!funcName.compare("memmove")){

    Value *src = callBase->getArgOperand(1);
    src = getValue(src);
    if(src != nullptr)
      localStringValue[src].insert(funcName);

  }else if(!funcName.compare("memmove_s")){
    
    Value *src = callBase->getArgOperand(2);
    src = getValue(src);
    if(src != nullptr)
      localStringValue[src].insert(funcName);
  }
}

void AFLCoverage::handleInst(Instruction *inst, std::unordered_map<Value*, std::unordered_set<std::string>> &localStringValue){
  /* check the oprends of the Instruction is in the string related table ?
    yes: check which king of the Instruction:
      -Call: handleFunc(calledFunc) while inserting the string related arguments into the table;
      -Store: insert the second oprend value into the table;
      -Load: insert ...   return true;
    no: return false;
  */
  if(inst == nullptr) return ;

  if(isa<CallInst>(inst)){

    CallInst* calle = dyn_cast<CallInst>(inst);
    Function* calledFunc = calle->getCalledFunction();
    std::unordered_set<Value*> args;
    /* if the function name is dbg.declare 
      insert the variable into stringValue 
    */
    if(calledFunc && !calledFunc->getName().empty()){
      /* if function arguments is string related, insert the responsitive 
      argument into stringValue 
      if function is string api (fucntion name is strcmp ...), then insert
      the the call result value into stringValue.
      */
      /* Avoid repeating, insert the handled function into handledFunc */
      int argIndex = 0;
      bool isHandle = false;
      
      std::string funcName = calledFunc->getName().str();
      funcName = llvm::demangle(calledFunc->getName().str());
      
      // default str api not need to trace function args
      for (Argument &arg : calledFunc->args()) {

        Value *actualArg = calle->getArgOperand(argIndex);
        auto res = isOprendStringRelated(actualArg,localStringValue);
        
        if(!res.empty()){//应该是这里出了问题
          isHandle = true;
          localStringValue[calle].insert(res.begin(),res.end());
        }
        args.insert(actualArg);
        argIndex++;
      }
   
      if(isHandle){  
        //识别对应的str api 然后插入对应类别，删除unknown
        std::string result = isInterceptedFunction(funcName);

        if (!result.empty()){
          localStringValue[calle].insert(result);
          localStringValue[calle].erase("unknown");
          
          isHandleTargetFunc(result,inst,localStringValue);
        }
      }

      if(handledFunc.find(funcName)==handledFunc.end()){   
        handledFunc.insert(funcName);
        handleFunc(calledFunc);
      }
   }
  }
  else if(isa<StoreInst>(inst)){

    StoreInst* storeInst = dyn_cast<StoreInst>(inst);
    
    Value* value = storeInst->getValueOperand();
    Value* address = storeInst->getPointerOperand();

    auto res = isOprendStringRelated(value,localStringValue);
    if(!res.empty()){
      localStringValue[address] = res;
    }

  }else if(isa<LoadInst>(inst)){

    LoadInst* loadInst = dyn_cast<LoadInst>(inst);
    Value* address = loadInst->getPointerOperand();

    auto res = isOprendStringRelated(address,localStringValue);
    if(!res.empty()){
      localStringValue[loadInst] = res;
    }
    
  }else if(isa<ICmpInst>(inst)||isa<BinaryOperator>(inst)){   
    
    Value* op1 = inst->getOperand(0);
    Value* op2 = inst->getOperand(1);

    auto res1 = isOprendStringRelated(op1,localStringValue);
    if(!res1.empty()){
      localStringValue[inst].insert(res1.begin(),res1.end());
    }

    auto res2 = isOprendStringRelated(op2, localStringValue);
    if(!res2.empty()){
      
      localStringValue[inst].insert(res2.begin(),res2.end());
    }

    Type *type1 = op1->getType();
    Type *type2 = op2->getType();
    //如果 op1 op2 都是string或者一个string一个null，则看icmp类型来判断
    // string相关且是i8相关类型,认为是strcmp类型，其他不考虑。
    if(isa<ICmpInst>(inst) && 
    ( (!res1.empty() && isI8Related(type1) && isa<ConstantPointerNull>(op2)) ||
      (!res2.empty() && isI8Related(type2) && isa<ConstantPointerNull>(op1) )||
      (!res1.empty() && isI8Related(type1) && !res2.empty() &&  isI8Related(type2)) ) ){
      localStringValue[inst].erase("unknown");
      localStringValue[inst].insert("strcmp");// 加入一个strcmp类型
    }
        
  }else if(isa<BranchInst>(inst)){
    
    BranchInst* brInst = dyn_cast<BranchInst>(inst);
    
    if(brInst->isConditional()){
      Value* cond = brInst->getCondition();

      auto res = isOprendStringRelated(cond,localStringValue);
      if(!res.empty()){
        localStringValue[brInst] = res;
      }
    }

  }else if(isa<GetElementPtrInst>(inst)){

    GetElementPtrInst *gepInst = dyn_cast<GetElementPtrInst>(inst);

    Value *basePtr = gepInst->getPointerOperand();
    
    if(valueStringStruct.find(basePtr)!=valueStringStruct.end()){//结构体,嵌套结构体,，但是结构体需要看是哪个索引     
      //查看对应索引位置是否为 string idx 或是 string struct idx
      unsigned operandCount = gepInst->getNumIndices();
      stringStruct* vss = valueStringStruct[basePtr];
      
      if(operandCount>=2) {
        Value *idx = gepInst->getOperand(2);

        if(auto *CI = dyn_cast<ConstantInt>(idx)){
          int selectIdx = CI->getSExtValue();
          //selectIdx == 结构体中，string相关的非结构体成员idx,记录
      
          for(auto index: vss->idx){      
            if(selectIdx == index){
              localStringValue[inst].insert("unknown");// 因为刚开始跟踪，所以unknown
            }
          }
          //selectIdx == 结构体中，string相关的结构体成员structIdx如下处理
          for(int index = 0;index < vss->structCount;index++){
            if(selectIdx == vss->structIdx[index]){
              valueStringStruct[inst] = vss->structs[index]; // 记录对应的[value*, stringStruct*]映射关系
              break;
            }
          }
        }
      }
    }else{
      //非结构体，正常操作
      auto res = isOprendStringRelated(basePtr,localStringValue); // char数组 getelement直接ok
      if(!res.empty()){
        localStringValue[inst] = res;
      }
    }

      
  }else if(isa<SExtInst>(inst)){

    SExtInst *sextInst = dyn_cast<SExtInst>(inst);

    auto res = isOprendStringRelated(sextInst->getOperand(0),localStringValue);
    if(!res.empty()){
      localStringValue[inst] = res;
    }

  }else if(isa<ZExtInst>(inst)){
    
    ZExtInst *zextInst = dyn_cast<ZExtInst>(inst);

    auto res = isOprendStringRelated(zextInst->getOperand(0),localStringValue);
    if(!res.empty()){
      localStringValue[inst] = res;
    }

  }else if(isa<TruncInst>(inst)){

    TruncInst *truncInst = dyn_cast<TruncInst>(inst);

    auto res = isOprendStringRelated(truncInst->getOperand(0),localStringValue);
    if(!res.empty()){
      localStringValue[inst] = res;
    }

  }else if(isa<InvokeInst>(inst)){
    
    InvokeInst *invokeInst = dyn_cast<InvokeInst>(inst);
    Function* calledFunc = invokeInst->getCalledFunction();  
    bool isHandle = false;
    std::unordered_set<Value*> args;

    for (unsigned i = 0; i < invokeInst->getNumArgOperands(); i++) {
      
      Value *arg = invokeInst->getArgOperand(i);
      auto res = isOprendStringRelated(arg, localStringValue);
      args.insert(arg);

      if(!res.empty()){
        isHandle = true;
        localStringValue[invokeInst].insert(res.begin(),res.end());
      }
    }

    if(calledFunc){

      if(isHandle&&!calledFunc->getName().empty()){  
        std::string funcName = calledFunc->getName().str();
        funcName = llvm::demangle(calledFunc->getName().str());  
        //识别对应的str api 然后插入对应类别，删除unknown

        std::string result = isInterceptedFunction(funcName);
      
        if (!result.empty()){
          localStringValue[invokeInst].insert(result);
          localStringValue[invokeInst].erase("unknown");

          isHandleTargetFunc(result,inst,localStringValue);
        } 

        if(handledFunc.find(funcName)==handledFunc.end()){

          handledFunc.insert(funcName);
          handleFunc(calledFunc);
        }
      }
    }

  }else if(isa<PHINode>(inst)){
    
    PHINode *phiNode = dyn_cast<PHINode>(inst);

    for (unsigned i = 0; i < phiNode->getNumIncomingValues(); ++i) {

      Value *incomingValue = phiNode->getIncomingValue(i);

      auto res = isOprendStringRelated(incomingValue,localStringValue);
      if(!res.empty()){
        localStringValue[phiNode] = res;
      }
    }
  }else if(isa<IntToPtrInst>(inst)){
    IntToPtrInst *iToPtr = dyn_cast<IntToPtrInst>(inst);
    Value *srcValue = iToPtr->getOperand(0);

    auto res = isOprendStringRelated(srcValue,localStringValue);
    if(!res.empty()){
      localStringValue[inst] = res;
    }
  }else if(isa<BitCastInst>(inst)){
    BitCastInst *bCastI = dyn_cast<BitCastInst>(inst);
    Value *value = bCastI->getOperand(0);
    
    auto res = isOprendStringRelated(value,localStringValue);
    if(!res.empty()){
      localStringValue[inst] = res;
    }
  }else{

    for(Use &u: inst->operands()){
      Value *operand = u.get();

      auto res = isOprendStringRelated(operand,localStringValue);
      if(!res.empty()){
        localStringValue[inst].insert(res.begin(),res.end());
      }
    }
  }
}

void AFLCoverage::handleFunc(Function *func){

  std::unordered_map<Value*, std::unordered_set<std::string>> localStringValue;

  for(BasicBlock &blk:*func){
    for(Instruction &inst:blk){
      if(isa<CallInst>(inst)){

        CallInst* calle = dyn_cast<CallInst>(&inst);
        Function* calledFunc = calle->getCalledFunction(); 

        if(calledFunc&&!calledFunc->getName().empty()){
          
          if(calledFunc->getName() == "llvm.dbg.declare"||
            calledFunc->getName() == "llvm.dbg.value"){
            
            Value* value = calle->getArgOperand(0);
            Value *scope = calle->getArgOperand(1);

            MetadataAsValue *mav = dyn_cast<MetadataAsValue>(value);
            ValueAsMetadata* vam = dyn_cast<ValueAsMetadata>(mav->getMetadata());
            Value* val = nullptr;
            if(vam != nullptr)
              val = vam->getValue();

            if(val!=nullptr && isMetadateStringRelated(scope,val))
              localStringValue[val].insert("unknown");
          }
        } 
      }
    }
  }

  for(BasicBlock &blk: *func){
    for(Instruction &inst: blk){
      handleInst(&inst,localStringValue);
    }
  }

  for(auto pair:localStringValue){
    Value *value = pair.first;
    if(nullptr != value && isa<BranchInst>(value)){
      stringValue[dyn_cast<BranchInst>(value)] = pair.second;
    }
  }
}


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  Type *voidType = Type::getVoidTy(C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  FunctionCallee TraceBB = (&M)->getOrInsertFunction(
      "__trace_visit_string",
      FunctionType::get(voidType, {Int32Ty,Int32Ty}, false));

  FunctionCallee PassFunc = (&M)->getOrInsertFunction(
      "__trace_pass_string",
      FunctionType::get(voidType, {Int32Ty,Int32Ty,Int32Ty}, false));


  /* Instrument all the things! */
  errs() << "Module Name: " << M.getName() << "\n";
  int instBrNum = 0;
  int brNum = 0 ;
  Function* mainFunc =  M.getFunction("main");


  
  /* handleFunc ：handle BasicBlocks of the Function A Set keep handledFunction avoid repeating
    finish, get a table about the string related values.
  */  
  handleFunc(mainFunc);

  
  // FILE* file = freopen("output.log", "w", stderr);
  // if (!file) {
  //   errs() << "Failed to open log file\n";
  //   return 1;
  // }
  
  std::unordered_map<unsigned int, std::unordered_set<std::string>> mapping;

  for (auto &F : M){
    
    // if (DISubprogram *SP = F.getSubprogram()) {
    //   // 获取文件名
    //   StringRef FileName = SP->getFilename();
    //   if (FileName.startswith("./")) FileName = FileName.drop_front(2); 
    //   StringRef Directory = SP->getDirectory();

    //   errs() << "File: " << Directory << "/" << FileName << "\n";
    // } 

    for (auto &BB : F) {
      
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */
      
      unsigned int cur_loc = basicBlockMap[&BB];
      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);
      Instruction *lastInst = BB.getTerminator();
      
      /* Insert string related counter:
      Check brInst, If is string related, insert couter */
      if(nullptr != lastInst){
        if(isa<BranchInst>(lastInst)){

          BranchInst *brInst = dyn_cast<BranchInst>(lastInst);

          if (brInst->isConditional()){

            /* If brInst is string related, insert visit couter, insert pass_loc */
            if(stringValue.find(brInst)!=stringValue.end()){

              unsigned int next_loc;
              
              /* Debug Msg */
              Metadata *md = brInst->getMetadata("dbg");
              if(md){
                if(isa<DILocation>(md)){

                  DILocation *loc = dyn_cast<DILocation>(md);

                  
                  // if(instAllFlag || soureceFileName == loc->getFilename()){

                    errs() << loc->getFilename() << "    Line: " << loc->getLine() <<"\n";

                    /* Visit */
                    BasicBlock *trueBB = brInst->getSuccessor(0);
                    next_loc = basicBlockMap[trueBB];
                    ConstantInt *Pass_Loc = ConstantInt::get(Int32Ty,next_loc );    
                    IRB.CreateCall(TraceBB,{Pass_Loc,CurLoc});
                  
                    /* Pass */
                    passSet.insert(std::pair<u32,u32>(next_loc,cur_loc));
                    instBrNum++;

                  // 索引为cur_loc>>1^next_loc,建立对应的插桩string分支索引及其对应的类别
                    mapping[(cur_loc>>1)^next_loc]=stringValue[brInst];
                  // }

                }
              }
            }
            brNum++;
          } 
        }
      }

      /* Load prev_loc */
      
      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      /* If pass, insert the pass string counter */
      if(passSet.find(cur_loc)!=passSet.end()){
        IRB.CreateCall(PassFunc,{ConstantInt::get(Int32Ty, cur_loc),PrevLoc,ConstantInt::get(Int32Ty, passSet[cur_loc])});
        passSet.erase(cur_loc);
      }
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    }

    //一些循环分支,由于block的遍历顺序，第一遍遍历的时候不是passSet，所以需要额外处理一遍。
    if(!passSet.empty()){
      //最保险的做法，再遍历一次block ，并将passSet清空为止。
      for (auto &BB : F) {

        BasicBlock::iterator IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));
        unsigned int cur_loc = basicBlockMap[&BB];
        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
        /* If pass, insert the pass string counter */
        if(passSet.find(cur_loc)!=passSet.end()){
          IRB.CreateCall(PassFunc,{ConstantInt::get(Int32Ty, cur_loc),PrevLoc,ConstantInt::get(Int32Ty, passSet[cur_loc])});
          passSet.erase(cur_loc);
        }
      }
    }
  }

  errs()<<"Instrumented "<< instBrNum <<" locations, the number of all conditional branch "<<brNum<<"\n";
  saveToXml("Index-Type.xml",mapping);

  // 关闭文件
  // fclose(file);
  
  /* Say something nice. */
  if (!be_quiet) {

    if (!brNum) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations, the number of all conditional branch %u  (%s mode, ratio %u%%).",
             instBrNum,brNum, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
