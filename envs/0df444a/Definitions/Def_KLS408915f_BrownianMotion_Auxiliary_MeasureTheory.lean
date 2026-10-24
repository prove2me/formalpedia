-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
-- name    : KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:06:00.767591+00:00
-- url     : https://prove2.me/theorems/93452af2-eef6-4d64-90fc-507d0a8440b7
-- title:
--   Measure-theoretic auxiliary lemmas
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. The bundle includes covariance, Haar-measure, parallelepiped, and finite-dimensional volume lemmas, including the ratio formula for volumes of closed balls in `ENNReal`: $\operatorname{vol}(\overline B(x,r))/\operatorname{vol}(\overline B(y,s))=(r/s)^{\operatorname{finrank}}$. It also records equality of left-invariant measures on equal-radius balls and identifies the relevant `MeasurableEquiv.toLp` coercion.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/MeasureTheory.lean#L83-L237 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.MeasureTheory`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_MeasureTheory`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Topology.MetricSpace.MetricSeparated

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/MeasureTheory.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory WithLp
open scoped ENNReal NNReal ProbabilityTheory RealInnerProductSpace
attribute [fun_prop] aemeasurable_id'
namespace ProbabilityTheory
section covariance
lemma centralMoment_of_integral_id_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} (p : ℕ) (hX : μ[X] = 0) :
    centralMoment X p μ = ∫ ω, X ω ^ p ∂μ := by
  rw [centralMoment]
  simp [hX]
end covariance
end ProbabilityTheory
lemma MeasurableEquiv.coe_toLp_symm_eq {ι : Type*} :
    ⇑(MeasurableEquiv.toLp 2 (ι → ℝ)).symm = ⇑(EuclideanSpace.equiv ι ℝ) := rfl
@[simp]
lemma zero_mem_parallelepiped {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {v : ι → E} :
    0 ∈ parallelepiped v := ⟨0, by simp, by simp⟩
@[simp]
lemma nonempty_parallelepiped {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {v : ι → E} :
    (parallelepiped v).Nonempty := ⟨0, zero_mem_parallelepiped⟩
@[simp, nontriviality]
lemma volume_of_nonempty_of_subsingleton {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [Subsingleton E] {s : Set E} (hs : s.Nonempty) :
    volume s = 1 := by
  rw [Subsingleton.eq_univ_of_nonempty hs,
    ← Subsingleton.eq_univ_of_nonempty (nonempty_parallelepiped (v := stdOrthonormalBasis ℝ E))]
  exact (stdOrthonormalBasis ℝ E).toBasis.addHaar_self
@[to_additive]
lemma MeasureTheory.Measure.IsMulLeftInvariant.measure_closedBall_const'
    {G : Type*} [Group G] [PseudoEMetricSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsIsometricSMul G G]
    [MeasurableMul G] (a b : G) (r : ℝ≥0∞) :
    μ (Metric.closedEBall a r) = μ (Metric.closedEBall b r) := by
  rw [show a = (b / a)⁻¹ * b by simp, ← Metric.preimage_mul_left_closedEBall, ← Measure.map_apply,
    map_mul_left_eq_self]
  · fun_prop
  · exact Metric.isClosed_closedEBall.measurableSet
open Metric
lemma InnerProductSpace.volume_closedBall_div {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    volume (closedBall x r) / volume (closedBall y s) =
      ENNReal.ofReal (r / s) ^ (Module.finrank ℝ E) := by
  obtain _ | _ := subsingleton_or_nontrivial E
  · simp [hr.le, hs.le]
  rw [InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall,
    ENNReal.mul_div_mul_right _ _ (by positivity) (by simp)]
  simp_rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.div_rpow_of_nonneg _ _ (by simp), ENNReal.ofReal_div_of_pos hs]
lemma InnerProductSpace.volume_closedBall_div' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) (r s : ℝ≥0∞) :
    volume (Metric.closedEBall x r) / volume (Metric.closedEBall y s) =
      (r / s) ^ (Module.finrank ℝ E) := by
  nontriviality E
  obtain rfl | hr := eq_top_or_lt_top r <;> obtain rfl | hs := eq_top_or_lt_top s
  · simp
  · lift s to ℝ≥0 using hs.ne
    simp [ENNReal.top_div, closedEBall_coe, (isCompact_closedBall _ _).measure_ne_top]
  · simp
  · obtain rfl | hr' := eq_zero_or_pos r <;> obtain rfl | hs' := eq_zero_or_pos s
    · simp
    · simp
    · simp [ENNReal.div_zero, hr'.ne', Metric.measure_closedEBall_pos volume x hr'.ne' |>.ne']
    lift r to ℝ≥0 using hr.ne
    lift s to ℝ≥0 using hs.ne
    simp_rw [closedEBall_coe]
    rw [volume_closedBall_div, ENNReal.ofReal_div_of_pos]
    · simp
    all_goals simp_all


