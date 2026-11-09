-- Prove2me | Definitions.Def_OddPermSum_Evaluation_machineExecution
-- name    : OddPermSum_Evaluation_machineExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:33.004247+00:00
-- url     : https://prove2.me/theorems/3ec4e9e3-2d13-4b23-8026-db38c0b03684
-- title:
--   Execution and primitive field-operation accounting
-- statement:
--   A machine state contains integer and field memories, an output list, and separate counters for arithmetic and zero tests. The fuel interpreter executes the finite syntax; exhausted fuel or inversion of zero produces no successful run. A successful run starts from zero memories and empty output.
--
--   $$\operatorname{cost}(s)=\operatorname{arithmetic}(s)+\operatorname{tests}(s).$$
--
--   Each addition, subtraction, multiplication or inversion contributes one arithmetic operation. An explicit zero test contributes one test; the guard on every successful inversion contributes another test. Input, copy, constants, output and integer control contribute no field operation. Fuel is only a termination witness, not the reported cost. Primitive exact equality is implemented classically and imposes no enumeration or bit representation on the field.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 5, Linear algebra cost convention; p. 2, Theorem 1.1 (operational encoding)

import Definitions.Def_OddPermSum_Evaluation_machineSyntax

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Machine storage and accumulated counts; field memory never feeds integer
control except through the explicit zeroTest instruction. -/
structure MachineState (F : Type*) where
  indices : ℕ → ℕ
  registers : ℕ → F
  outputs : List F
  arithmetic : ℕ
  tests : ℕ

def IndexExpr.eval (n : ℕ) (r : ℕ → ℕ) : IndexExpr → ℕ
  | .literal v => v
  | .dimension => n
  | .read a => r (a.eval n r)
  | .add a b => a.eval n r + b.eval n r
  | .sub a b => a.eval n r - b.eval n r
  | .mul a b => a.eval n r * b.eval n r
  | .div a b => a.eval n r / b.eval n r
  | .mod a b => a.eval n r % b.eval n r
  | .less a b => if a.eval n r < b.eval n r then 1 else 0
  | .equal a b => if a.eval n r = b.eval n r then 1 else 0

/-- Fuel bounds interpreter recursion, not field-operation cost. An exhausted run
or inversion of zero fails. Every successful inversion charges one zero test and
one inversion. Branching on integer registers is free integer control. -/
def execute {F : Type*} [Field F] [DecidableEq F] (n : ℕ) (inputs : List F) :
    ℕ → AlgebraicProgram F → MachineState F → Option (MachineState F)
  | 0, _, _ => none
  | fuel+1, p, s =>
    let ix := fun a : IndexExpr => a.eval n s.indices
    match p with
    | .skip => some s
    | .setIndex d a => some { s with indices := Function.update s.indices (ix d) (ix a) }
    | .constant d a => some { s with registers := Function.update s.registers (ix d) a }
    | .input d a => some { s with registers := Function.update s.registers (ix d) (inputs.getD (ix a) 0) }
    | .copy d a => some { s with registers := Function.update s.registers (ix d) (s.registers (ix a)) }
    | .add d a b => some { s with
        registers := Function.update s.registers (ix d) (s.registers (ix a) + s.registers (ix b))
        arithmetic := s.arithmetic + 1 }
    | .sub d a b => some { s with
        registers := Function.update s.registers (ix d) (s.registers (ix a) - s.registers (ix b))
        arithmetic := s.arithmetic + 1 }
    | .mul d a b => some { s with
        registers := Function.update s.registers (ix d) (s.registers (ix a) * s.registers (ix b))
        arithmetic := s.arithmetic + 1 }
    | .inverse d a =>
        if s.registers (ix a) = 0 then none
        else some { s with
          registers := Function.update s.registers (ix d) ((s.registers (ix a))⁻¹)
          arithmetic := s.arithmetic + 1
          tests := s.tests + 1 }
    | .zeroTest d a => some { s with
        indices := Function.update s.indices (ix d) (if s.registers (ix a) = 0 then 1 else 0)
        tests := s.tests + 1 }
    | .output a => some { s with outputs := s.outputs ++ [s.registers (ix a)] }
    | .sequence a b => do
        let t ← execute n inputs fuel a s
        execute n inputs fuel b t
    | .branch c a b => execute n inputs fuel (if ix c = 0 then b else a) s
    | .loop c a =>
        if ix c = 0 then some s
        else do
          let t ← execute n inputs fuel a s
          execute n inputs fuel (.loop c a) t

/-- Canonical zero-initialized run. Classical equality implements the primitive
field zero test; no computable enumeration or bit representation of F is assumed. -/
noncomputable def run {F : Type*} [Field F] (p : AlgebraicProgram F)
    (n : ℕ) (inputs : List F) (fuel : ℕ) : Option (MachineState F) :=
  letI : DecidableEq F := Classical.decEq F
  execute n inputs fuel p
    { indices := fun _ => 0, registers := fun _ => 0,
      outputs := [], arithmetic := 0, tests := 0 }

/-- Actual charged cost of a successful run, including field zero tests. -/
def MachineState.cost {F : Type*} (s : MachineState F) : ℕ := s.arithmetic + s.tests

end OddPermSum.Evaluation


