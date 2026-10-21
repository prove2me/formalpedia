-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38
-- name    : QAlgorithms_Papers_Independent_Renew46_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:05:44.944247+00:00
-- url     : https://prove2.me/theorems/7538ebea-3754-4137-bfca-ea1f60b0d940
-- title:
--   Definitions for Jensen's Operator Inequality
-- statement:
--   The objects the formalized statements of *Jensen's Operator Inequality* (arXiv:math/0204049) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Operators`: Bounded operators on a complex Hilbert space (PDF pp. 1--2).
--   - `InInterval`: The source's calculus domain: self-adjoint, with real spectrum in I (PDF p. 1).
--   - `combination`: A finite noncommutative combination, with adjoints on the left (PDF p. 2).
--   - `columnSquares`: The column sum of squares (PDF p. 4).
--   - `ConvexOnOperators`: Convexity of the operator function on this particular B(H) (PDF pp. 2--3).
--   - `UnitalJensenOn`: Unital Jensen inequality at a fixed tuple size on this B(H) (PDF p. 3, (5)).
--   - `ContractiveJensenOn`: Contractive Jensen inequality at a fixed tuple size on B(H) (PDF p. 3).
--   - `HilbertPower`: The finite Hilbert direct sum, equipped with the Hilbert norm (PDF p. 5).
--   - `columnAdjoint`: The actual row adjoint of the column: ξ ↦ ∑ a_i* ξ_i (PDF p. 5).
--   - `ColumnCokernel`: The cokernel Hilbert space, as the kernel of the computed row adjoint (PDF p. 5).
--   - `IntervalOperatorConvex`: Operator convexity on arbitrary infinite-dimensional complex Hilbert spaces (PDF p. 2). No separability or finite-dimensional restriction is imposed; u is arbitrary. The accepted Information100.P50.OperatorConvex is restricted to positive-definite finite matrices, so it cannot represent this arbitrary-interval concept.
--   - `AllUnitalJensen`: Fixed positive tuple size, uniformly over Hilbert spaces (PDF p. 3).
--   - `AllContractiveJensen`: Fixed positive tuple size, uniformly over Hilbert spaces (PDF p. 3).
--   - `IsometryJensen`: Condition (iii) of Theorem 2.1, on all infinite-dimensional H (PDF p. 3).
--   - `PinchingJensen`: The fourth condition, printed (vi), of Theorem 2.1 (PDF p. 3).
--   - `MatrixTraceJensen`: Matrix trace Jensen at fixed dimension and tuple size (PDF p. 3, (7)). The real part is the ordinary, unnormalized trace on the self-adjoint expressions.
--   - `AlgebraPositive`: Positivity in an abstract C*-algebra, without selecting an arbitrary order (PDF p. 4). Every positive element has a square root, so these are exactly A_+.
--   - `FiniteTrace`: A finite positive tracial functional; neither faithful nor normalized (PDF p. 4).
--   - `TraceWeight`: A trace weight on A_+, allowing +∞ (PDF p. 4). The total function's values off A_+ are immaterial. Homogeneity uses 0 * ∞ = 0. Norm density is stated for the usual square-integrable left ideal.
--   - `IsUnitaryMatrix`: A genuinely unitary operator block matrix on the finite Hilbert sum (PDF pp. 4--5).
--   - `IsUnitaryColumn`: A column of an actual square unitary, not just an isometric column (PDF p. 4).
--   - `dilatedColumn`: The computed defect-square-root extension; none labels the last coordinate (PDF p. 5).
--   - `columnRangeComplement`: The projection p = 1-aa* in B(H^n) (PDF p. 5, (11)).
--   - `columnCanonicalDilation`: The explicit dilation (11)--(12), in block order H^n ⊕ H (PDF p. 5). The printed a_m* in the first row of (12) is a_n*: (11) fixes that entry. This block unitary differs from the accepted Frontier30.P26.canonicalDilation, which is a real linear map on a Lie algebra.
--   - `cyclicRoot`: The positive-sign primitive root from Lemma 3.1 (PDF p. 6).
--   - `cyclicE`: E = diag(θ, θ², ..., θ^n); Fin indices are shifted by one (PDF p. 6).
--   - `operatorCyclicE`: The scalar diagonal E amplified to operator blocks on H^n (PDF p. 6).
--   - `uniformProjection`: The uniform scalar projection P, computed from n (PDF p. 6).
--   - `cyclicProjection`: The translate with source index k.val+1 in {1,...,n} (PDF p. 6).
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, https://arxiv.org/abs/math/0204049v1

import Mathlib

/-!
Statements from Hansen--Pedersen, Jensen's Operator Inequality,
arXiv:math/0204049v1. All new definitions are local to this paper.
The two continuous-field assertions are deferred in HARD.md.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Bounded operators on a complex Hilbert space (PDF pp. 1--2). -/
abbrev Operators (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →L[ℂ] H

/-- The source's calculus domain: self-adjoint, with real spectrum in I (PDF p. 1). -/
def InInterval {A : Type*} [CStarAlgebra A] (I : Set ℝ) (x : A) : Prop :=
  IsSelfAdjoint x ∧ spectrum ℝ x ⊆ I

/-- A finite noncommutative combination, with adjoints on the left (PDF p. 2). -/
def combination {A : Type*} [Ring A] [StarRing A] {ι : Type*} [Fintype ι]
    (a x : ι → A) : A :=
  ∑ i, star (a i) * x i * a i

/-- The column sum of squares (PDF p. 4). -/
def columnSquares {A : Type*} [Ring A] [StarRing A] {ι : Type*} [Fintype ι]
    (a : ι → A) : A :=
  ∑ i, star (a i) * a i

section Hilbert

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Convexity of the operator function on this particular B(H) (PDF pp. 2--3). -/
def ConvexOnOperators (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : Operators H, InInterval I x → InInterval I y →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      cfc f (t • x + (1 - t) • y) ≤ t • cfc f x + (1 - t) • cfc f y

/-- Unital Jensen inequality at a fixed tuple size on this B(H) (PDF p. 3, (5)). -/
def UnitalJensenOn (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∀ x a : Fin n → Operators H, (∀ i, InInterval I (x i)) →
    columnSquares a = 1 →
      cfc f (combination a x) ≤ combination a (fun i => cfc f (x i))

/-- Contractive Jensen inequality at a fixed tuple size on B(H) (PDF p. 3). -/
def ContractiveJensenOn (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∀ x a : Fin n → Operators H, (∀ i, InInterval I (x i)) →
    columnSquares a ≤ 1 →
      cfc f (combination a x) ≤ combination a (fun i => cfc f (x i))

/-- The finite Hilbert direct sum, equipped with the Hilbert norm (PDF p. 5). -/
abbrev HilbertPower (n : ℕ) := PiLp 2 (fun _ : Fin n => H)

/-- The actual row adjoint of the column: ξ ↦ ∑ a_i* ξ_i (PDF p. 5). -/
def columnAdjoint {n : ℕ} (a : Fin n → Operators H) : HilbertPower H n →L[ℂ] H :=
  ∑ i, (star (a i)).comp (PiLp.proj 2 (fun _ : Fin n => H) i)

/-- The cokernel Hilbert space, as the kernel of the computed row adjoint (PDF p. 5). -/
def ColumnCokernel {n : ℕ} (a : Fin n → Operators H) :=
  LinearMap.ker (columnAdjoint H a).toLinearMap

end Hilbert

/-- Operator convexity on arbitrary infinite-dimensional complex Hilbert spaces (PDF p. 2).
No separability or finite-dimensional restriction is imposed; u is arbitrary.
The accepted Information100.P50.OperatorConvex is restricted to positive-definite
finite matrices, so it cannot represent this arbitrary-interval concept. -/
def IntervalOperatorConvex (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (¬ FiniteDimensional ℂ H) → ConvexOnOperators H I f

/-- Fixed positive tuple size, uniformly over Hilbert spaces (PDF p. 3). -/
def AllUnitalJensen (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    UnitalJensenOn H I f n

/-- Fixed positive tuple size, uniformly over Hilbert spaces (PDF p. 3). -/
def AllContractiveJensen (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ContractiveJensenOn H I f n

/-- Condition (iii) of Theorem 2.1, on all infinite-dimensional H (PDF p. 3). -/
def IsometryJensen (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (¬ FiniteDimensional ℂ H) → ∀ v x : Operators H,
      star v * v = 1 → InInterval I x →
        cfc f (star v * x * v) ≤ star v * cfc f x * v

/-- The fourth condition, printed (vi), of Theorem 2.1 (PDF p. 3). -/
def PinchingJensen (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    (¬ FiniteDimensional ℂ H) → ∀ p x : Operators H,
      IsStarProjection p → InInterval I x → ∀ s ∈ I,
        p * cfc f (p * x * p + s • (1 - p)) * p ≤ p * cfc f x * p

/-- Matrix trace Jensen at fixed dimension and tuple size (PDF p. 3, (7)).
The real part is the ordinary, unnormalized trace on the self-adjoint expressions. -/
def MatrixTraceJensen (I : Set ℝ) (f : ℝ → ℝ) (m n : ℕ) (contractive : Bool) : Prop :=
  ∀ x a : Fin n → Matrix (Fin m) (Fin m) ℂ,
    (∀ i, InInterval I (x i)) →
    (if contractive then (1 - columnSquares a).PosSemidef else columnSquares a = 1) →
      (Matrix.trace (cfc f (combination a x))).re ≤
        (Matrix.trace (combination a (fun i => cfc f (x i)))).re

/-- Positivity in an abstract C*-algebra, without selecting an arbitrary order (PDF p. 4).
Every positive element has a square root, so these are exactly A_+. -/
def AlgebraPositive {A : Type*} [CStarAlgebra A] (x : A) : Prop :=
  ∃ b : A, x = star b * b

/-- A finite positive tracial functional; neither faithful nor normalized (PDF p. 4). -/
structure FiniteTrace (A : Type*) [CStarAlgebra A] where
  value : A →L[ℂ] ℂ
  real_on_squares : ∀ b : A, (value (star b * b)).im = 0
  nonneg_on_squares : ∀ b : A, 0 ≤ (value (star b * b)).re
  cyclic : ∀ x y : A, value (x * y) = value (y * x)

/-- A trace weight on A_+, allowing +∞ (PDF p. 4).
The total function's values off A_+ are immaterial. Homogeneity uses 0 * ∞ = 0.
Norm density is stated for the usual square-integrable left ideal. -/
structure TraceWeight (A : Type*) [CStarAlgebra A] where
  value : A → ℝ≥0∞
  map_zero : value 0 = 0
  map_add : ∀ x y : A, AlgebraPositive x → AlgebraPositive y →
    value (x + y) = value x + value y
  map_smul : ∀ (r : ℝ≥0) (x : A), AlgebraPositive x →
    value ((r : ℝ) • x) = (r : ℝ≥0∞) * value x
  tracial : ∀ x : A, value (star x * x) = value (x * star x)
  lower_semicontinuous : LowerSemicontinuousOn value {x | AlgebraPositive x}
  densely_defined : Dense {x : A | value (star x * x) < ⊤}

/-- A genuinely unitary operator block matrix on the finite Hilbert sum (PDF pp. 4--5). -/
def IsUnitaryMatrix {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
    (U : Matrix ι ι A) : Prop :=
  star U * U = 1 ∧ U * star U = 1

/-- A column of an actual square unitary, not just an isometric column (PDF p. 4). -/
def IsUnitaryColumn {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
    (a : ι → A) : Prop :=
  ∃ U : Matrix ι ι A, IsUnitaryMatrix U ∧ ∃ j : ι, ∀ i, U i j = a i

/-- The computed defect-square-root extension; none labels the last coordinate (PDF p. 5). -/
def dilatedColumn {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (a : Fin n → Operators H) : Option (Fin n) → Operators H
  | some i => a i
  | none => cfc Real.sqrt (1 - columnSquares a)

/-- The projection p = 1-aa* in B(H^n) (PDF p. 5, (11)). -/
def columnRangeComplement {A : Type*} [Ring A] [StarRing A] {n : ℕ}
    (a : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  1 - Matrix.of (fun i j => a i * star (a j))

/-- The explicit dilation (11)--(12), in block order H^n ⊕ H (PDF p. 5).
The printed a_m* in the first row of (12) is a_n*: (11) fixes that entry.
This block unitary differs from the accepted Frontier30.P26.canonicalDilation,
which is a real linear map on a Lie algebra. -/
def columnCanonicalDilation {A : Type*} [Ring A] [StarRing A] {n : ℕ}
    (a : Fin n → A) : Matrix (Option (Fin n)) (Option (Fin n)) A
  | some i, some j => columnRangeComplement a i j
  | some i, none => a i
  | none, some j => -star (a j)
  | none, none => 0

/-- The positive-sign primitive root from Lemma 3.1 (PDF p. 6). -/
def cyclicRoot (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- E = diag(θ, θ², ..., θ^n); Fin indices are shifted by one (PDF p. 6). -/
def cyclicE (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => cyclicRoot n ^ (i.val + 1))

/-- The scalar diagonal E amplified to operator blocks on H^n (PDF p. 6). -/
def operatorCyclicE (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (n : ℕ) : Matrix (Fin n) (Fin n) (Operators H) :=
  Matrix.diagonal (fun i => (cyclicRoot n ^ (i.val + 1)) • (1 : Operators H))

/-- The uniform scalar projection P, computed from n (PDF p. 6). -/
def uniformProjection (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun _ _ => (n : ℂ)⁻¹

/-- The translate with source index k.val+1 in {1,...,n} (PDF p. 6). -/
def cyclicProjection (n : ℕ) (k : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (star (cyclicE n)) ^ (k.val + 1) * uniformProjection n * (cyclicE n) ^ (k.val + 1)

/-- Sanity: the empty finite combination has its literal empty-sum value. -/
example {A : Type*} [Ring A] [StarRing A] (a x : Fin 0 → A) : combination a x = 0 := by
  simp [combination]

/-- Sanity: real zero functional calculus is zero, including at bad inputs. -/
example {A : Type*} [CStarAlgebra A] (x : A) : cfc (fun _ : ℝ => 0) x = 0 := by
  exact cfc_const_zero ℝ x

/-- Sanity: zero is positive in the abstract cone. -/
example {A : Type*} [CStarAlgebra A] : AlgebraPositive (0 : A) := by
  exact ⟨0, by simp⟩

/-- Sanity: finite traces are not required to be faithful or normalized. -/
example {A : Type*} [CStarAlgebra A] : Nonempty (FiniteTrace A) := by
  exact ⟨{ value := 0
           real_on_squares := by intro b; simp
           nonneg_on_squares := by intro b; simp
           cyclic := by intro x y; simp }⟩

/-- Sanity: the zero trace weight meets the continuity and density clauses. -/
example {A : Type*} [CStarAlgebra A] : Nonempty (TraceWeight A) := by
  exact ⟨{ value := fun _ => 0
           map_zero := rfl
           map_add := by intro x y hx hy; simp
           map_smul := by intro r x hx; simp
           tracial := by intro x; rfl
           lower_semicontinuous := lowerSemicontinuousOn_const
           densely_defined := by
             change Dense { x : A | (0 : ℝ≥0∞) < ⊤ }
             simpa using (dense_univ : Dense (Set.univ : Set A)) }⟩

/-- Sanity: the computed row adjoint for an empty column is the zero operator. -/
example (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : Fin 0 → Operators H) : columnAdjoint H a = 0 := by
  simp [columnAdjoint]

/-- Sanity: the canonical last column is exactly (a,0). -/
example {A : Type*} [Ring A] [StarRing A] {n : ℕ} (a : Fin n → A) :
    columnCanonicalDilation a none none = 0 ∧
      ∀ i, columnCanonicalDilation a (some i) none = a i := by
  exact ⟨rfl, fun _ => rfl⟩

/-- Sanity: P in dimension one is the identity scalar matrix. -/
example : uniformProjection 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  simp [uniformProjection, Matrix.one_apply, Subsingleton.elim i j]

/-- Sanity: the last eigenvalue at n=1 is θ=exp(2πi)=1. -/
example : cyclicRoot 1 = 1 := by
  simpa [cyclicRoot] using Complex.exp_two_pi_mul_I

end QAlgorithms.Papers.Independent.Renew46.P38


