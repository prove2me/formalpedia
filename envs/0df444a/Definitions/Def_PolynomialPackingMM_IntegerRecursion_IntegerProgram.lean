-- Prove2me | Definitions.Def_PolynomialPackingMM_IntegerRecursion_IntegerProgram
-- name    : PolynomialPackingMM_IntegerRecursion_IntegerProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:29.077228+00:00
-- url     : https://prove2.me/theorems/7362601b-35e2-43fb-9aeb-37813bb20235
-- title:
--   Integer straight-line instructions, checked exact division and actual execution cost
-- statement:
--   An integer program is a finite list of instructions with output-register selections. It supports integer constants, matrix-entry inputs, addition, subtraction, multiplication, and exact division by a fixed positive integer. Constants and inputs cost zero; every arithmetic instruction costs one, including multiplication by a constant and exact division.
--
--   $$\operatorname{execute}(P,A,B)=\operatorname{some}(C,t)$$
--
--   means that every referenced register exists, every division encountered is divisible, the output is $C$, and exactly $t$ arithmetic instructions were executed. A nondivisible division returns failure. Well-formedness separately requires operands to refer to earlier registers and outputs to existing registers.
--
--   This is the integer computation model used by the recursive algorithm. **Formalization Note** Input padding is zero-valued input selection, and output cropping is register selection; both are free. The linear-form builder emits a multiplication and an addition for every term, including zero coefficients, so no uncharged arithmetic is hidden in a linear-map primitive.
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 19 (PDF 20), §4.3, proof of Theorem 1.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Mathlib

namespace PolynomialPackingMM.IntegerRecursion

/-- The computation model of §4.3: division is by a fixed positive integer. -/
inductive IntegerGate where
  | constant (z : ℤ)
  | input (side : Bool) (row col : ℕ)
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | mul (a b : ℕ)
  | exactDiv (a : ℕ) (denominator : ℕ+)
  deriving DecidableEq

def IntegerGate.cost : IntegerGate → ℕ
  | .constant _ | .input _ _ _ => 0
  | _ => 1

def IntegerGate.RefsBelow (k : ℕ) : IntegerGate → Prop
  | .constant _ | .input _ _ _ => True
  | .add a b | .sub a b | .mul a b => a < k ∧ b < k
  | .exactDiv a _ => a < k

/-- Failure is observable: a non-exact division never silently returns an integer quotient. -/
def IntegerGate.evaluate (inputs : Bool → ℕ → ℕ → ℤ) (regs : List ℤ) :
    IntegerGate → Option ℤ
  | .constant z => some z
  | .input s i j => some (inputs s i j)
  | .add a b => do return (← regs[a]?) + (← regs[b]?)
  | .sub a b => do return (← regs[a]?) - (← regs[b]?)
  | .mul a b => do return (← regs[a]?) * (← regs[b]?)
  | .exactDiv a d => do
      let x ← regs[a]?
      if (d : ℤ) ∣ x then some (x / (d : ℤ)) else none

structure IntegerProgram where
  gates : List IntegerGate
  outputs : List ℕ

def IntegerProgram.WellFormed (P : IntegerProgram) : Prop :=
  (∀ (k : Fin P.gates.length), (P.gates.get k).RefsBelow k.val) ∧
    ∀ o ∈ P.outputs, o < P.gates.length

def executeGates (inputs : Bool → ℕ → ℕ → ℤ) :
    List IntegerGate → List ℤ → ℕ → Option (List ℤ × ℕ)
  | [], regs, cost => some (regs, cost)
  | g :: gs, regs, cost => do
      let x ← g.evaluate inputs regs
      executeGates inputs gs (regs ++ [x]) (cost + g.cost)

def IntegerProgram.execute (P : IntegerProgram) (inputs : Bool → ℕ → ℕ → ℤ) :
    Option (List ℤ × ℕ) := do
  let (regs, cost) ← executeGates inputs P.gates [] 0
  let outputs ← P.outputs.mapM (fun o => regs[o]?)
  return (outputs, cost)

def IntegerProgram.cost (P : IntegerProgram) : ℕ := (P.gates.map IntegerGate.cost).sum

/-- Input padding and register selection cost zero. No arithmetic is hidden in this function. -/
def integerInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ)
    (side : Bool) (i j : ℕ) : ℤ :=
  if hi : i < n then if hj : j < n then
    if side then B ⟨i, hi⟩ ⟨j, hj⟩ else A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

def serializeMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : List ℤ :=
  (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => A i j))

/-- A concrete builder: gates are appended, and every emitted gate returns its register. -/
abbrev IntegerBuilder := StateM (List IntegerGate)

def emitIntegerGate (g : IntegerGate) : IntegerBuilder ℕ := do
  let gs ← get
  set (gs ++ [g])
  return gs.length

/-- Every coefficient multiplication and accumulation is an arithmetic gate, including zeros. -/
def compileLinearForm (coefficients : List ℤ) (registers : List ℕ) : IntegerBuilder ℕ := do
  let z ← emitIntegerGate (.constant 0)
  (coefficients.zip registers).foldlM (fun acc cr => do
    let c ← emitIntegerGate (.constant cr.1)
    let t ← emitIntegerGate (.mul c cr.2)
    emitIntegerGate (.add acc t)) z

end PolynomialPackingMM.IntegerRecursion


