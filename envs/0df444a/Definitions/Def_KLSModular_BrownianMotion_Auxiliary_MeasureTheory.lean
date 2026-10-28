-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_MeasureTheory
-- name    : KLSModular_BrownianMotion_Auxiliary_MeasureTheory
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:35:30.176444+00:00
-- url     : https://prove2.me/theorems/3312c2d9-e816-4bec-9802-c908ff00df00
-- title:
--   Measure-theoretic auxiliary lemmas
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. The bundle includes covariance, Haar-measure, parallelepiped, and finite-dimensional volume lemmas, including the ratio formula for volumes of closed balls in `ENNReal`: $\operatorname{vol}(\overline B(x,r))/\operatorname{vol}(\overline B(y,s))=(r/s)^{\operatorname{finrank}}$. It also records equality of left-invariant measures on equal-radius balls and identifies the relevant `MeasurableEquiv.toLp` coercion.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.Algebra
--   public import BrownianMotion.Auxiliary.Metric
--   public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
--   public import Mathlib.Probability.Distributions.Gaussian.Real
--   public import Mathlib.Probability.Independence.Integration
--   public import Mathlib.Probability.Independence.ZeroOne
--   import Mathlib.MeasureTheory.Function.Holder
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   lemma centralMoment_of_integral_id_eq_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
--       {μ : Measure Ω} {X : Ω → ℝ} (p : ℕ) (hX : μ[X] = 0) :
--       centralMoment X p μ = ∫ ω, X ω ^ p ∂μ := by
--     rw [centralMoment]
--     simp [hX]
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/Algebra`](https://prove2.me/theorems/04959ec9-aef2-4820-b562-f262499c17bc), [`BrownianMotion/Auxiliary/Metric`](https://prove2.me/theorems/c17c58dc-3947-47ec-a39f-329acb5b644d).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/MeasureTheory.lean) · `BrownianMotion.Auxiliary.MeasureTheory` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/MeasureTheory.lean#L83-L237 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.MeasureTheory`, definition bundle `KLSModular_BrownianMotion_Auxiliary_MeasureTheory`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Metric
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.MeasureTheory.Function.Holder

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


