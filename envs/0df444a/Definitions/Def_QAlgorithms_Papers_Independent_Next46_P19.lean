-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P19
-- name    : QAlgorithms_Papers_Independent_Next46_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:32:01.213177+00:00
-- url     : https://prove2.me/theorems/4da05264-1e4e-4588-9fe1-8701d95b0da2
-- title:
--   Definitions for The Unique Pure Gaussian State Determined by the Partial Saturation of the Uncertainty Relations of a Mixed Gaussian State
-- statement:
--   The objects the formalized statements of *The Unique Pure Gaussian State Determined by the Partial Saturation of the Uncertainty Relations of a Mixed Gaussian State* (arXiv:1205.5222) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `closedPhaseBall`: The closed Euclidean ball of nonnegative radius r, PDF pp.3–5. The sum is the Euclidean squared norm, not the function-space supremum norm.
--   - `covarianceEllipsoid`: The centered covariance ellipsoid (1/2) z^T Sigma^(-1) z <= 1, PDF p.4, equation (11). The theorem guards the inverse by PosDef.
--   - `affineSymplecticBall`: An affine symplectic image a + S(B_r), PDF p.3 and pp.4–5. Mathlib's symplecticGroup uses S J S^T = J, equivalent to the source's S^T J S = J; its opposite sign for J does not change this group.
--   - `linearSymplecticCapacity`: Supremum of pi r^2 over contained affine symplectic balls, PDF pp.4–5. The extended nonnegative codomain preserves unbounded suprema; on the positive-definite ellipsoids in the theorem the capacity is finite.
-- source:
--   The Unique Pure Gaussian State Determined by the Partial Saturation of the Uncertainty Relations of a Mixed Gaussian State, arXiv:1205.5222v1, https://arxiv.org/abs/1205.5222v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

/-!
Source: Maurice A. de Gosson, arXiv:1205.5222v1, PDF pp.3–8.
Only the valid first-step capacity implication is stated. Theorem 1, the
second-step uniqueness claim, and Proposition 2 have explicit source-error
deferrals in HARD.md. No operator-realizability result is asserted here.
Accepted grouped indices, real matrices, complexification and canonical J are
imported without modifying their modules. The local geometric definitions use
grouped coordinates (x_1,...,x_n,p_1,...,p_n).
Compilation is pending the batch handoff.
-/

noncomputable section

open scoped ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)
open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

namespace QAlgorithms.Papers.Independent.Next46.P19

/-- The closed Euclidean ball of nonnegative radius r, PDF pp.3–5.
The sum is the Euclidean squared norm, not the function-space supremum norm. -/
def closedPhaseBall (n : ℕ) (r : ℝ) : Set (Phase n → ℝ) :=
  {z | ∑ i, (z i) ^ 2 ≤ r ^ 2}

/-- The centered covariance ellipsoid (1/2) z^T Sigma^(-1) z <= 1,
PDF p.4, equation (11). The theorem guards the inverse by PosDef. -/
def covarianceEllipsoid {n : ℕ} (Sigma : PhaseMatrix n) : Set (Phase n → ℝ) :=
  {z | (1 / 2 : ℝ) * (∑ i, z i * ((Sigma⁻¹).mulVec z) i) ≤ 1}

/-- An affine symplectic image a + S(B_r), PDF p.3 and pp.4–5.
Mathlib's symplecticGroup uses S J S^T = J, equivalent to the source's
S^T J S = J; its opposite sign for J does not change this group. -/
def affineSymplecticBall {n : ℕ}
    (S : Matrix.symplecticGroup (Fin n) ℝ) (a : Phase n → ℝ) (r : ℝ) :
    Set (Phase n → ℝ) :=
  (fun z => a + (S : PhaseMatrix n).mulVec z) '' closedPhaseBall n r

/-- Supremum of pi r^2 over contained affine symplectic balls, PDF pp.4–5.
The extended nonnegative codomain preserves unbounded suprema; on the
positive-definite ellipsoids in the theorem the capacity is finite. -/
def linearSymplecticCapacity {n : ℕ} (Omega : Set (Phase n → ℝ)) : ℝ≥0∞ :=
  sSup {v | ∃ r : ℝ, 0 ≤ r ∧
    ∃ S : Matrix.symplecticGroup (Fin n) ℝ, ∃ a : Phase n → ℝ,
      affineSymplecticBall S a r ⊆ Omega ∧ v = ENNReal.ofReal (Real.pi * r ^ 2)}

/-- Sanity check of the positive upper-right block of the source's J. -/
example : sigma 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  simp [sigma]

/-- Sanity check of the negative lower-left block of the source's J. -/
example : sigma 1 (Sum.inr 0) (Sum.inl 0) = -1 := by
  simp [sigma]

/-- The uncertainty correction vanishes when hbar is zero (outside the theorem). -/
example {n : ℕ} (Sigma : PhaseMatrix n) :
    complexify Sigma + (((0 / 2 : ℝ) : ℂ) * Complex.I) •
      complexify (sigma n) = complexify Sigma := by
  simp

/-- The zero vector belongs to the radius-zero closed ball. -/
example (n : ℕ) : (0 : Phase n → ℝ) ∈ closedPhaseBall n 0 := by
  simp [closedPhaseBall]

/-- The covariance ellipsoid is centered, independently of the inverse's value. -/
example {n : ℕ} (Sigma : PhaseMatrix n) :
    (0 : Phase n → ℝ) ∈ covarianceEllipsoid Sigma := by
  simp [covarianceEllipsoid]

/-- The identity affine symplectic image is the original Euclidean ball. -/
example (n : ℕ) (r : ℝ) :
    affineSymplecticBall (1 : Matrix.symplecticGroup (Fin n) ℝ) 0 r =
      closedPhaseBall n r := by
  simp [affineSymplecticBall]

/-- No affine symplectic ball, including radius zero, is contained in the
empty set; its capacity is the empty nonnegative supremum, namely zero. -/
example (n : ℕ) :
    linearSymplecticCapacity (∅ : Set (Phase n → ℝ)) = 0 := by
  apply le_antisymm ?_ bot_le
  apply sSup_le
  rintro v ⟨r, hr, S, a, hsubset, hv⟩
  have hz : (0 : Phase n → ℝ) ∈ closedPhaseBall n r := by
    simp [closedPhaseBall, sq_nonneg]
  have hempty : a + (S : PhaseMatrix n).mulVec 0 ∈ (∅ : Set (Phase n → ℝ)) :=
    hsubset ⟨0, hz, rfl⟩
  exact False.elim hempty

end QAlgorithms.Papers.Independent.Next46.P19


