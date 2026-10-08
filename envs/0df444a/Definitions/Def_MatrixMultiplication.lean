-- Prove2me | Definitions.Def_MatrixMultiplication
-- name    : MatrixMultiplication
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.654102+00:00
-- url     : https://prove2.me/theorems/dd5823f3-c9ef-4419-9fea-53c6de8f85fb
-- statement:
--   This block formalizes arithmetic-circuit complexity of matrix multiplication over a field F. A Gate is either a constant, an input, or the sum, difference, or product of two earlier registers; constants and inputs cost 0 and each addition, subtraction or multiplication costs 1. A Program with r registers is built by appending gates, where each new gate may refer only to the previously computed registers (indexed by Fin r), and its cost is the total gate cost. For a×b by b×c matrices, the inputs are the entries of A and B, and a MatrixAlgorithm consists of a register count, a program, and a choice of output register for each entry (i,k) of the a×c result. Its evaluation produces the matrix of those output registers, it is Correct when it equals the product A*B for all matrices over F, and its cost is the program cost. AdmissibleExponent(F,τ) says that for every ε>0 there is a constant C>0 such that for every n≥1 some correct n×n by n×n algorithm has cost at most C·n^(τ+ε); omega(F) is the infimum of admissible exponents. For rectangular products, innerSize(n,k) is the ceiling of n^k, RectangularAdmissibleExponent(F,k,τ) is the same condition for n×⌈n^k⌉ times ⌈n^k⌉×n multiplication, and rectangularOmega(F,k) is the infimum of such exponents. Finally complexAlpha is the supremum of those k in [0,1] for which rectangularOmega over the complex numbers equals 2, the dual exponent of matrix multiplication. These are definitions only, with no bounds proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatrixMultiplication.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatrixMultiplication.lean; bytes 16..3684
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! The three main complex matrix multiplication bounds, checked independently. -/

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

/-- The inner dimension of an `n × n^k` by `n^k × n` multiplication. -/
def innerSize (n : ℕ) (k : ℝ) : ℕ := ⌈(n : ℝ) ^ k⌉₊

def RectangularAdmissibleExponent (F : Type*) [Field F] (k τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def rectangularOmega (F : Type*) [Field F] (k : ℝ) : ℝ :=
  sInf {τ : ℝ | RectangularAdmissibleExponent F k τ}

/-- The dual exponent is a supremum of exact exponent-two rectangular shapes. -/
def complexAlpha : ℝ :=
  sSup {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2}

end MatrixMultiplication.Arithmetic

end

namespace MatrixMultiplication



end MatrixMultiplication
end OAI


