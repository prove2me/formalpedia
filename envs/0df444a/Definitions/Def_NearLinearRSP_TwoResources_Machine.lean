-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Machine
-- name    : NearLinearRSP_TwoResources_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:57.468547+00:00
-- url     : https://prove2.me/theorems/da7bc5aa-f2c4-4a06-ab03-7569cf26ee8f
-- title:
--   Deterministic real RAM with primitive unit costs and exact exponential
-- statement:
--   A program is a finite list of instructions on real registers, natural registers, real and natural memories, and read-only real and natural input cells. Real instructions load constants, copy registers, perform exact $+,-,\times,\div$, evaluate $\exp$, or branch on $<$ and $=$. Natural instructions load constants, copy, add, subtract with truncation at zero, or compare. Individual indirect loads, stores, input reads, jumps and halt each have their own instruction. Every executed instruction costs one; access to fixed operand registers is included in its instruction cost. There is no floor, real-to-integer conversion, logarithm, Poisson, priority-queue or whole-DP primitive.
--
--   Writing $\operatorname{step}_{p,x}$ for one independent operational transition of program $p$ on input $x$, the state after $k$ instructions is
--   $$
--   S_k=\operatorname{step}_{p,x}^{\,k}(S_0).
--   $$
--   An execution of cost $k$ must first halt at $S_k$; every earlier state is active. Work memory and registers initially contain zero. Division is Lean's total real division, including $x/0=0$; the mathematical algorithm's normalized calls separately guard its intended divisors. A missing instruction halts with one charged step.
--
--   This reusable machine model supplies operational meaning to deterministic execution and time without building correctness, termination or a complexity bound into a program type.
--
--   **Formalization Note** Exact unit-cost exponential evaluation is the disclosed reading of the paper's infinite-precision real-RAM computation of exact Poisson coefficients and generating functions. The problem-specific input and output layouts are defined separately.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.3, real-RAM model; p.7, update (✣); pp.10–11, exact generating functions

import Mathlib

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

inductive RealOp where
  | add | sub | mul | div
inductive NatOp where
  | add | sub
inductive Test where
  | lt | eq

/-- Every constructor is one instruction of cost one. Registers are operands;
indirect memory and input access require their own load/store instructions.
There is no floor, logarithm, real-to-integer conversion, or algorithm oracle. -/
inductive RAMInstr where
  | realConst (dst : ℕ) (c : ℝ)
  | natConst (dst c : ℕ)
  | realCopy (dst src : ℕ)
  | natCopy (dst src : ℕ)
  | realOp (op : RealOp) (dst lhs rhs : ℕ)
  | natOp (op : NatOp) (dst lhs rhs : ℕ)
  | exp (dst src : ℕ)
  | realBranch (test : Test) (lhs rhs yes no : ℕ)
  | natBranch (test : Test) (lhs rhs yes no : ℕ)
  | loadReal (dst addressRegister : ℕ)
  | loadNat (dst addressRegister : ℕ)
  | storeReal (addressRegister src : ℕ)
  | storeNat (addressRegister src : ℕ)
  | inputReal (dst addressRegister : ℕ)
  | inputNat (dst addressRegister : ℕ)
  | jump (pc : ℕ)
  | halt

abbrev Program := List RAMInstr

structure RAMState where
  pc : ℕ
  halted : Bool
  nr : ℕ → ℕ
  rr : ℕ → ℝ
  nm : ℕ → ℕ
  rm : ℕ → ℝ

structure RAMInput where
  naturals : ℕ → ℕ
  reals : ℕ → ℝ

noncomputable def evalReal (op : RealOp) (x y : ℝ) : ℝ :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .div => x / y

def evalNat (op : NatOp) (x y : ℕ) : ℕ :=
  match op with
  | .add => x + y
  | .sub => x - y

noncomputable def realTest (test : Test) (x y : ℝ) : Bool :=
  match test with
  | .lt => decide (x < y)
  | .eq => decide (x = y)

def natTest (test : Test) (x y : ℕ) : Bool :=
  match test with
  | .lt => decide (x < y)
  | .eq => decide (x = y)

noncomputable def ramStep (p : Program) (input : RAMInput) (S : RAMState) : RAMState :=
  if S.halted then S else
  let U := { S with pc := S.pc + 1 }
  match p[S.pc]?.getD .halt with
  | .realConst d c => { U with rr := Function.update S.rr d c }
  | .natConst d c => { U with nr := Function.update S.nr d c }
  | .realCopy d s => { U with rr := Function.update S.rr d (S.rr s) }
  | .natCopy d s => { U with nr := Function.update S.nr d (S.nr s) }
  | .realOp op d a b => { U with rr := Function.update S.rr d (evalReal op (S.rr a) (S.rr b)) }
  | .natOp op d a b => { U with nr := Function.update S.nr d (evalNat op (S.nr a) (S.nr b)) }
  | .exp d s => { U with rr := Function.update S.rr d (Real.exp (S.rr s)) }
  | .realBranch test a b yes no => { S with pc := if realTest test (S.rr a) (S.rr b) then yes else no }
  | .natBranch test a b yes no => { S with pc := if natTest test (S.nr a) (S.nr b) then yes else no }
  | .loadReal d a => { U with rr := Function.update S.rr d (S.rm (S.nr a)) }
  | .loadNat d a => { U with nr := Function.update S.nr d (S.nm (S.nr a)) }
  | .storeReal a s => { U with rm := Function.update S.rm (S.nr a) (S.rr s) }
  | .storeNat a s => { U with nm := Function.update S.nm (S.nr a) (S.nr s) }
  | .inputReal d a => { U with rr := Function.update S.rr d (input.reals (S.nr a)) }
  | .inputNat d a => { U with nr := Function.update S.nr d (input.naturals (S.nr a)) }
  | .jump pc => { S with pc := pc }
  | .halt => { S with halted := true }

noncomputable def execute (p : Program) (input : RAMInput) : ℕ → RAMState → RAMState
  | 0, S => S
  | k + 1, S => ramStep p input (execute p input k S)

/-- An exact active trace, including the halting instruction, has cost k. -/
noncomputable def Execution (p : Program) (input : RAMInput) (initial final : RAMState) (k : ℕ) : Prop :=
  execute p input k initial = final ∧ final.halted = true ∧
    ∀ j < k, (execute p input j initial).halted = false

/-- Work/output memory begins zero; the input is read-only and accessed by charged instructions. -/
noncomputable def initialState : RAMState := ⟨0, false, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

end NearLinearRSP.TwoResources


