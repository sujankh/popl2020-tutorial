#include "Extractor.h"

#include "llvm/IR/Instruction.h"

void Extractor::initialize() {
  /* Relations for Def and Use */
  Solver->register_relation(Def);
  Solver->register_relation(Use);

  /* Relations for Reaching Definition Analysis */
  Solver->register_relation(Kill);
  Solver->register_relation(Gen);
  Solver->register_relation(Next);
  Solver->register_relation(In);
  Solver->register_relation(Out);

  /* Relations for Taint Analysis */
  Solver->register_relation(Taint);
  Solver->register_relation(Edge);
  Solver->register_relation(Path);
  Solver->register_relation(Sanitizer);
  Solver->register_relation(Div);
  Solver->register_relation(Alarm);

  /*
   * Add your code here:
   * Define your analysis rules for taint analysis and add the rules to the
   * solver.
   */

  z3::expr X = C.bv_const("X", 32);
  //z3::expr Y = C.bv_const("Y", 32);
  
  z3::expr I = C.bv_const("I", 32);
  z3::expr J = C.bv_const("J", 32);
  z3::expr K = C.bv_const("K", 32);

  // Reaching def rules  
  z3::expr kill_rule = z3::forall(X, I, J, z3::implies(Def(X, I) && Def(X, J), Kill(X, J)));
  Solver->add_rule(kill_rule, C.str_symbol("kill_rule"));

  z3::expr out_rule1 = z3::forall(X, I, z3::implies(Gen(X, I), Out(X, I)));
  Solver->add_rule(out_rule1, C.str_symbol("out_rule1"));

  z3::expr out_rule2 = z3::forall(X, I, z3::implies(In(X, I) && !Kill(X, I), Out(X, I)));
  Solver->add_rule(out_rule2, C.str_symbol("out_rule2"));

  z3::expr in_rule = z3::forall(X, I, J, z3::implies(Out(X, I) && Next(I, J), In(X, J)));
  Solver->add_rule(in_rule, C.str_symbol("in_rule"));

  // Taint analysis rules
  z3::expr edge_rule = z3::forall(X, I, J, z3::implies(Def(X, I) && Use(X, J) && Next(I, J), Edge(I, J)));
  Solver->add_rule(edge_rule, C.str_symbol("edge_rule"));

  z3::expr path_rule1 = z3::forall(I, J, z3::implies(Edge(I, J) && Taint(I), Path(I, J)));
  Solver->add_rule(path_rule1, C.str_symbol("path_rule1"));

  z3::expr path_rule2 = z3::forall(I, J, K, z3::implies(Path(I,J) && Edge(J,K) && !Sanitizer(J), Path(I, K)));
  Solver->add_rule(path_rule2, C.str_symbol("path_rule2"));

  z3::expr alarm_rule = z3::forall(X, I, J, z3::implies(Path(I, J) && Div(X, J), Alarm(J)));
  Solver->add_rule(alarm_rule, C.str_symbol("alarm_rule"));
}

void Extractor::addDef(const InstMapTy &InstMap, Value *X, Instruction *I) {
  if (InstMap.find(X) == InstMap.end())
    return;
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(I)};
  Solver->add_fact(Def, Arr);
}

void Extractor::addUse(const InstMapTy &InstMap, Value *X, Instruction *I) {
  if (Constant *C = dyn_cast<Constant>(X))
    return;
  if (InstMap.find(X) == InstMap.end())
    return;
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(I)};
  Solver->add_fact(Use, Arr);
}

void Extractor::addDiv(const InstMapTy &InstMap, Value *X, Instruction *I) {
  if (Constant *C = dyn_cast<Constant>(X))
    return;
  if (InstMap.find(X) == InstMap.end())
    return;
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(I)};
  Solver->add_fact(Div, Arr);
}

void Extractor::addTaint(const InstMapTy &InstMap, Instruction *I) {
  unsigned int Arr[1] = {InstMap.at(I)};
  Solver->add_fact(Taint, Arr);
}

void Extractor::addSanitizer(const InstMapTy &InstMap, Instruction *I) {
  unsigned int Arr[1] = {InstMap.at(I)};
  Solver->add_fact(Sanitizer, Arr);
}

void Extractor::addGen(const InstMapTy &InstMap, Instruction *X, Instruction *I) {
  unsigned int Arr[2] = {InstMap.at(X), InstMap.at(I)};
  Solver->add_fact(Gen, Arr);
}

void Extractor::addNext(const InstMapTy &InstMap, Instruction *I,
                        Instruction *J) {
  unsigned int Arr[2] = {InstMap.at(I), InstMap.at(J)};
  Solver->add_fact(Next, Arr);
};

/*
 * Implement the following function that collects Datalog facts for each
 * instruction.
 */
void Extractor::extractConstraints(const InstMapTy &InstMap, Instruction *I) {
  /* Add your code here */

  // Different kind of instructions
  // http://llvm.org/doxygen/classllvm_1_1Instruction.html

  if(StoreInst *si = dyn_cast<StoreInst>(I))
  {
    std::cout << "Storing " << si->getValueOperand()->getValueName() << " to " << si->getPointerOperand()->getName().str() << "("  << si->getPointerOperand() << ")" << std::endl;
    std::cout << "Store Instr " << si << std::endl;
    //store i32 %call, i32* %x
    //store i32 0, i32* %retval

    addDef(InstMap, si->getPointerOperand(), si);
    addUse(InstMap, si->getValueOperand(), si);
    addGen(InstMap, si, si);
  }
  else if(LoadInst *li = dyn_cast<LoadInst>(I))
  {
    std::cout << "Loading " << li->getPointerOperand()->getName().str() << "(" <<  li->getPointerOperand() << ") to " << li << std::endl;    
  }
  else if(CallInst *call = dyn_cast<CallInst>(I))
  {
    std::cout << "Calling " << call->getCalledFunction()->getName().str() << "(";
    for(const auto & arg : call->arg_operands())
    {
      std::cout << arg;
    }
    std::cout << ") at " << call << std::endl;
  }
  else if(BinaryOperator *binary = dyn_cast<BinaryOperator>(I))
  {
    
    if (binary->getOpcode() == Instruction::SDiv)
    {    
      std::cout << "Division: " << binary << std::endl;
      std::cout << binary->getOperand(0) << "/" << binary->getOperand(1) << std::endl;      
    }
  }

  std::cout << "---" << std::endl;
}