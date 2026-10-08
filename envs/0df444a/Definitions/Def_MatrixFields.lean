-- Prove2me | Definitions.Def_MatrixFields
-- name    : MatrixFields
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.590891+00:00
-- url     : https://prove2.me/theorems/c94ec58e-eee1-49a9-a911-af5ee8f44fdb
-- statement:
--   This block builds a model of arithmetic circuits for matrix multiplication over a field F. A Gate over inputs and registers is one of five forms: a constant in F, an input variable, or the sum, difference or product of two registers; evaluating a gate reads inputs and register values in the obvious way, and its cost is 0 for constants and inputs and 1 for each addition, subtraction or multiplication. A Program with r registers is a straight-line program built from the empty program by appending, as register r, a gate that may refer only to the earlier r registers; its evaluation yields the value of every register, and its cost is the sum of the gate costs. For dimensions a, b, c, the inputs are the entries of an a-by-b matrix A and a b-by-c matrix B, indexed by the disjoint union of the two index sets. A MatrixAlgorithm consists of a number of registers, a program on those inputs, and a choice of output register for each entry (i,k) of the a-by-c result; its evaluation on (A,B) returns the matrix of the chosen register values. It is Correct if its evaluation equals the matrix product A*B for all A and B over F, and its cost is the program cost. AdmissibleExponent(F,τ) is the defined proposition that for every ε>0 there exists a constant C>0 such that for every n≥1 some correct algorithm for n-by-n matrices has cost at most C·n^(τ+ε). The quantity omega(F) is defined as the real infimum of all admissible exponents τ, with the usual convention of sInf in the reals if that set is empty or unbounded below. No theorem is stated; the final namespace is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatrixFields.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatrixFields.lean; bytes 16..3027
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped BigOperators Topology Polynomial

namespace MatrixAllFields

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

inductive Gate (F Input Register : Type*) where
  | constant : F → Gate F Input Register
  | input : Input → Gate F Input Register
  | add : Register → Register → Gate F Input Register
  | sub : Register → Register → Gate F Input Register
  | mul : Register → Register → Gate F Input Register

namespace Gate

variable {F Input Register : Type*}

def eval [Field F] (inputs : Input → F) (registers : Register → F) :
    Gate F Input Register → F
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate F Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (F Input : Type*) : ℕ → Type _ where
  | nil : Program F Input 0
  | step {r : ℕ} : Program F Input r → Gate F Input (Fin r) → Program F Input (r + 1)

namespace Program

variable {F Input : Type*}

def eval [Field F] : {r : ℕ} → Program F Input r → (Input → F) → Fin r → F
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

end Program

abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

def matrixInputs {F : Type*} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    MatrixInput a b c → F
  | .inl (i, j) => A i j
  | .inr (j, k) => B j k

structure MatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : Program F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

def eval (P : MatrixAlgorithm F a b c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    Matrix (Fin a) (Fin c) F :=
  fun i k => P.program.eval (matrixInputs A B) (P.output i k)

def Correct (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F), P.eval A B = A * B

def cost (P : MatrixAlgorithm F a b c) : ℕ := P.program.cost

end MatrixAlgorithm

/-- Positive slack, one uniform constant, and a correct program at every size. -/
def AdmissibleExponent (F : Type*) [Field F] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n n n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def omega (F : Type*) [Field F] : ℝ := sInf {τ : ℝ | AdmissibleExponent F τ}

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

namespace MatrixAllFields.MatrixMultiplication.AllFieldMain

universe u



end MatrixAllFields.MatrixMultiplication.AllFieldMain
end OAI


