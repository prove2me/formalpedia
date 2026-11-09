-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_QuantumModel
-- name    : InvariantMoneySecurity_Decomposition_QuantumModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:51:26.288025+00:00
-- url     : https://prove2.me/theorems/36d7c3ea-78f1-4916-8a5a-b62f5dd94732
-- title:
--   Finite quantum registers, Born probabilities, and negligible functions
-- statement:
--   A register with $n$ qubits has computational basis $\{0,1\}^n$ and complex amplitude vectors. For a vector $v$, its rank-one operator has entries $v_x\overline{v_y}$. The uniform vector on a nonempty finite set $F$ has amplitude $|F|^{-1/2}$ on $F$ and zero elsewhere. Its value on the empty set is the zero vector and is never used as a minted state.
--
--   For an effect $E$ and density matrix $\rho$, the Born probability is
--   $$\operatorname{Born}(E,\rho)=\operatorname{Re}\operatorname{Tr}(E\rho).$$
--   The module supplies the two partial traces and unrecorded computational-basis measurement. Actual states in theorem statements are positive semidefinite matrices of trace one; the matrix operations also act on subnormalized branches without renormalizing them.
--
--   A function $\mu$ is negligible if, for every real polynomial $q$ positive on the nonnegative integers, there is $N$ such that $\mu(n)<1/q(n)$ for every $n\ge N$. This is the source's eventually inverse-polynomial definition, with positivity made explicit. In applications the functions being bounded are nonnegative. These general register operations are independent of the money construction.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 6, §2 Notation; p. 9, Definition 2.4

import Mathlib
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition

/-- Finite qubit registers; the empty register has its unique basis state. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Rank-one operator, without assuming normalization. -/
def ketbra {α : Type} (v : α → ℂ) : Matrix α α ℂ :=
  fun x y => v x * star (v y)

/-- Computational-basis vector. -/
def basisVector {α : Type} [DecidableEq α] (x : α) : α → ℂ :=
  fun y => if y = x then 1 else 0

/-- Uniform vector; the empty-set value is the zero vector, never a minted note. -/
def uniformVector {α : Type} [DecidableEq α] (F : Finset α) : α → ℂ :=
  fun x => if x ∈ F then (Real.sqrt (F.card : ℝ) : ℂ)⁻¹ else 0

/-- Born pairing, extended linearly to raw operators. -/
def born {α : Type} [Fintype α] (E ρ : Matrix α α ℂ) : ℝ :=
  (E * ρ).trace.re

/-- Partial trace over the second tensor factor, with no renormalization. -/
def discardRight {α β : Type} [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  fun x y => ∑ b, ρ (x, b) (y, b)

/-- Discarding the first register. -/
def discardLeft {α β : Type} [Fintype α]
    (ρ : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  fun x y => ∑ a, ρ (a, x) (a, y)

/-- Unrecorded computational-basis measurement. -/
def dephase {α : Type} [DecidableEq α] (ρ : Matrix α α ℂ) : Matrix α α ℂ :=
  fun x y => if x = y then ρ x x else 0

/-- Positive polynomials; restricting negligibility to these avoids division by zero. -/
def PositivePolynomial (q : Polynomial ℝ) : Prop :=
  ∀ n : ℕ, 0 < q.eval (n : ℝ)

/-- The source's strict, eventually inverse-polynomial bound. No fixed exponent is chosen. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  ∀ q : Polynomial ℝ, PositivePolynomial q →
    ∃ N : ℕ, ∀ n ≥ N, μ n < 1 / q.eval (n : ℝ)

end InvariantMoneySecurity.Decomposition


