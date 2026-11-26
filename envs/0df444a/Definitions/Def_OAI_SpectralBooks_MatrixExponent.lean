-- Prove2me | Definitions.Def_OAI_SpectralBooks_MatrixExponent
-- name    : OAI_SpectralBooks_MatrixExponent
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T02:41:01.461865+00:00
-- url     : https://prove2.me/theorems/075d8574-32c4-5329-9ce2-c04310157b73
-- title:
--   Division-free formal matrix-multiplication exponent
-- statement:
--   These declarations fix the division-free straight-line model in which the exact matrix-multiplication exponents are stated.
--
--   A **gate** is one of five things: a constant from the coefficient type, an input index, or a binary addition, subtraction, or multiplication of two earlier registers. There is no division. A constant or an input costs $0$; an addition, a subtraction, or a multiplication costs $1$. A **program** is a finite sequence of gates, each allowed to read only registers already created. Its cost is the number of addition, subtraction, and multiplication gates.
--
--   For dimensions $a,b,c$, the input indeterminates are the entries of an $a\times b$ matrix and a $b\times c$ matrix, kept as disjoint families. A **matrix algorithm** is a program together with a choice, for every output position $(i,k)$, of one register. It is **formally correct** when the polynomial in that register is identically
--   $$
--   \sum_j X^{\mathrm L}_{i,j}\, X^{\mathrm R}_{j,k}
--   $$
--   in the polynomial ring. Agreement as functions on the ground field is not enough, including when the field is finite.
--
--   The **wire dimension** at scale $N$ and weight $w$ is the natural-number ceiling of the real power $N^w$. That ceiling is $0$ when the power is not positive. A real number $\tau$ is a **formally admissible exponent** at weights $(w_{12},w_{23},w_{31})$ when, for every $\varepsilon>0$, some constant $C>0$ has the following property: for every integer $N\ge 1$ there is a formally correct algorithm of shape
--   $$
--   \bigl(\lceil N^{w_{31}}\rceil,\ \lceil N^{w_{12}}\rceil,\ \lceil N^{w_{23}}\rceil\bigr)
--   $$
--   whose cost is at most $C\, N^{\tau+\varepsilon}$.
--
--   The exponent $\omega(F;w_{12},w_{23},w_{31})$ is the infimum of all such $\tau$. On $\mathbb{R}$ this infimum equals $0$ when the set is empty or is not bounded below. The **dual exponent** of a function $\omega:\mathbb{R}\to\mathbb{R}$ is the supremum of $\{t\in[0,1]:\omega(t)=2\}$, and that supremum equals $0$ when no such $t$ exists. **Formal alpha** of a field $F$ is the dual exponent of $t\mapsto \omega(F;1,1,t)$.
--
--   **Formalization note.** In the register-polynomial map, the gate just appended is stored at index $0$ and every earlier register moves up by one, which is the comparator's indexing. The new gate still reads registers in the numbering from before that shift.
-- source:
--   OpenAI math comparator lean/ComparatorChallenges/MatrixExponent.lean, the definitions preceding the three sorry theorems, and the model described in lean/docs/107.md. https://github.com/openai/math/blob/main/lean/ComparatorChallenges/MatrixExponent.lean . https://github.com/openai/math/blob/main/lean/docs/107.md .

import Mathlib

set_option autoImplicit false

/-!
Comparator definitions for the exact matrix-multiplication exponents.
Source: openai/math `lean/ComparatorChallenges/MatrixExponent.lean`.
-/

namespace OAI

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

def cost : {r : ℕ} → Program F Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

end Program

abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

structure MatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : Program F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

def cost (P : MatrixAlgorithm F a b c) : ℕ := P.program.cost

end MatrixAlgorithm

end MatrixMultiplication.Arithmetic

end

namespace LinearAlgebra.SpectralBooks

open OAI.MatrixMultiplication.Arithmetic MvPolynomial
open scoped BigOperators

noncomputable section

section

variable {F I R : Type*} [CommRing F]

/-- The polynomial produced at one gate from the polynomials in its registers. -/
def gatePolynomial (g : Gate F I R) (v : R → MvPolynomial I F) : MvPolynomial I F :=
  g.casesOn (fun c => C c) (fun i => X i)
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

/-- Formal polynomial in each register of a straight-line program. -/
def registerPolynomial : {r : ℕ} → Program F I r → Fin r → MvPolynomial I F
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gatePolynomial g (registerPolynomial p)) (registerPolynomial p)

/-- Formal correctness in the paper, including over a finite ground field. -/
def FormalCorrect {a b c : ℕ} (P : MatrixAlgorithm F a b c) : Prop :=
  ∀ i k, registerPolynomial P.program (P.output i k) =
    ∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k))

end

/-- The integer wire dimension at scale `N` and weight `w`. -/
def wireDimension (N : ℕ) (w : ℝ) : ℕ := ⌈(N : ℝ) ^ w⌉₊

/-- Admissible exponents for the rounded rectangular formats, with positive slack. -/
def FormalAdmissibleExponent (F : Type*) [Field F] (w12 w23 w31 τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ P : MatrixAlgorithm F (wireDimension N w31) (wireDimension N w12) (wireDimension N w23),
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)

/-- The arithmetic exponent in base size `N` at three prescribed wire weights. -/
def formalOmega (F : Type*) [Field F] (w12 w23 w31 : ℝ) : ℝ :=
  sInf {τ : ℝ | FormalAdmissibleExponent F w12 w23 w31 τ}

/-- The supremum of the weights in `[0, 1]` at which the cost exponent is two. -/
def dualExponent (ω : ℝ → ℝ) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc 0 1 ∧ ω t = 2}

/-- The dual exponent for formal arithmetic matrix multiplication at weights `(1,1,t)`. -/
def formalAlpha (F : Type*) [Field F] : ℝ := dualExponent (formalOmega F 1 1)

end

end LinearAlgebra.SpectralBooks

end OAI


