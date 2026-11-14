-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BlockFock
-- name    : InfoLossLAR_Native_AFT_BlockFock
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:19:35.731546+00:00
-- url     : https://prove2.me/theorems/1f076583-41cc-4838-8664-8be7dc4cb235
-- title:
--   Coordinate tensors and Gaussian fields for block estimates
-- statement:
--   For a finite coordinate set $I$ and degree $k$, tensors are real arrays indexed by $I^k$, with squared energy $$\mathcal E(T)=\sum_{a\in I^k}T(a)^2.$$ The construction includes tensor products, permutation symmetrization, normalized linear averages, and the finite standard real Gaussian field. These objects support the block tensor estimates used in the affine construction.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BlockFock.lean; migrated source SHA256 4e3e4c84af9bd7f6dfe41d4b1a1368ceb8ae80bb401e402e384efef5455218f3; byte-range skeleton from Lean AST, with original retained definitions and proofs.

import Definitions.Def_InfoLossLAR_Native_AFT_FiniteProbability
import Mathlib


/-!
# Concrete finite symmetric tensors for the block Fock estimate

Tensors are coordinate arrays in an orthonormal basis, indexed by actual
finite tuples. Tensor products and symmetrization are defined explicitly.
Their Hilbert contraction and factorial estimates are proved from finite sums.
-/

namespace AFT
namespace BlockFock

open scoped BigOperators Classical

variable {State Index Index₁ Index₂ Color : Type*}

/-- Jensen's square inequality for an actual finite probability law. -/
theorem mean_square_le [Fintype State] (law : FiniteDist State) (value : State → ℝ) :
    (∑ state, law.weight state * value state) ^ 2 ≤
      ∑ state, law.weight state * value state ^ 2 := by
  let mean := ∑ state, law.weight state * value state
  have hvariance : 0 ≤ ∑ state, law.weight state * (value state - mean) ^ 2 :=
    Finset.sum_nonneg fun state _ => mul_nonneg (law.nonneg state) (sq_nonneg _)
  have hexpand : (∑ state, law.weight state * (value state - mean) ^ 2) =
      (∑ state, law.weight state * value state ^ 2) - mean ^ 2 := by
    calc
      _ = ∑ state, (law.weight state * value state ^ 2 -
          2 * mean * (law.weight state * value state) + law.weight state * mean ^ 2) := by
        apply Finset.sum_congr rfl
        intro state _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, law.sum_one]
        change _ - 2 * mean * mean + 1 * mean ^ 2 = _
        ring
  rw [hexpand] at hvariance
  exact sub_nonneg.mp hvariance

/-- A finite coordinate array for a tensor with slots indexed by `Index`. -/
abbrev Tensor (Index Color : Type*) := (Index → Color) → ℝ

/-- Squared Hilbert norm in the orthonormal tensor basis. -/
noncomputable def tensorEnergy [Fintype Index] [Fintype Color]
    (tensor : Tensor Index Color) : ℝ := ∑ point, tensor point ^ 2

/-- The actual uniform average over slot permutations. -/
noncomputable def symmetrize [Fintype Index] (tensor : Tensor Index Color) :
    Tensor Index Color := fun point =>
  ∑ permutation : Equiv.Perm Index,
    (FiniteDist.uniform (Equiv.Perm Index)).weight permutation * tensor (point ∘ permutation)





/-- Tensor multiplication before projection onto symmetric arrays. -/
def tensorProduct (first : Tensor Index₁ Color) (second : Tensor Index₂ Color) :
    Tensor (Index₁ ⊕ Index₂) Color :=
  fun point => first (point ∘ Sum.inl) * second (point ∘ Sum.inr)



















section GaussianSquare

open MeasureTheory ProbabilityTheory
open scoped NNReal





/-- Actual independent Gaussian coordinates used in the Fock representation. -/
noncomputable def realGaussianField [Fintype Index] : Measure (Index → ℝ) :=
  Measure.pi (fun _ : Index => gaussianReal 0 (1 / 2))



instance realGaussianField_probability [Fintype Index] :
    IsProbabilityMeasure (realGaussianField (Index := Index)) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Index => gaussianReal 0 (1 / 2))))



















/-- A linear factor whose squared coefficient norm is `energy * law.weight`.
The two actual independent real Gaussian fields form the circular field. -/
noncomputable def normalizedLinearValue [Fintype Index] [Fintype State]
    (law : FiniteDist State) (direction : State → Index → ℝ) (energy : ℝ)
    (state : State) (point : (Index → ℝ) × (Index → ℝ)) : ℂ :=
  (Real.sqrt (energy * law.weight state) : ℂ) *
    (((∑ index, direction state index * point.1 index : ℝ) : ℂ) +
      ((∑ index, direction state index * point.2 index : ℝ) : ℂ) * Complex.I)

/-- The aggregate mean vector, with its cancellations preserved. -/
noncomputable def normalizedLinearMean [Fintype State]
    (law : FiniteDist State) (direction : State → Index → ℝ) (energy : ℝ) (index : Index) : ℝ :=
  ∑ state, Real.sqrt (energy * law.weight state) * direction state index



end GaussianSquare

end BlockFock
end AFT


