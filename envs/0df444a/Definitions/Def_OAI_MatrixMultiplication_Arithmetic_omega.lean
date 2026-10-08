-- Prove2me | Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
-- name    : OAI_MatrixMultiplication_Arithmetic_omega
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-07T03:58:50.102011+00:00
-- url     : https://prove2.me/theorems/503d0a5f-898c-4acd-b62a-35447f4c303d
-- title:
--   Arithmetic programs and the matrix multiplication exponent
-- statement:
--   A matrix multiplication algorithm over a field is a finite straight-line program whose inputs are the entries of the two matrices and whose outputs select registers. Constants and input gates have zero cost; each addition, subtraction, or multiplication costs one operation. Correctness means that the output equals the matrix product for every pair of input matrices. A real exponent τ is admissible if for every ε > 0 there is one positive constant C such that every positive size n has a correct square-matrix algorithm costing at most C n^(τ + ε). The arithmetic exponent ω is the real infimum of the admissible exponents. The original block also supplies rectangular exponents and their complex dual exponent, preserving OpenAI’s definitions.
-- source:
--   OpenAI, An Upper Bound of 9/4 for the Matrix Multiplication Exponent, October 2, 2026, p. 1, Theorem 1.1 and the preceding definition of omega. https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatrixMultiplication.lean; bytes 16..3684
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

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


