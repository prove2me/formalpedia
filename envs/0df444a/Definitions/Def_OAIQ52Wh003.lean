-- Prove2me | Definitions.Def_OAIQ52Wh003
-- name    : OAIQ52Wh003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:43:17.502637+00:00
-- url     : https://prove2.me/theorems/3145e6b8-0d82-4e37-9b57-272ae6a426aa
-- title:
--   Definitions bundle OAIQ52Wh003 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 4 definitions and 140 theorems. The definitions and types are `OAI.WeakHessianTransport.IsFarthestHopfMinimizer`, `OAI.WeakHessianTransport.boundedHopfLp`, `OAI.WeakHessianTransport.boundedHopfMap`, `OAI.WeakHessianTransport.hopfLax`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_CompactAnchoredControl`, `WeakHessian_Calculus_ControlNorm`, `WeakHessian_Calculus_NormSqLintegralEnorm`, `WeakHessian_Entropy_IntegralDensityMeasureLp'`, `WeakHessian_LocalBounds_AbsolutelyContinuousDistDom`, `WeakHessian_LocalBounds_AffineTime`, `WeakHessian_LocalBounds_ClampTimeVal`, `WeakHessian_LocalBounds_ContinuousTimeMarginals`, `WeakHessian_LocalBounds_DyadicTimes`, `WeakHessian_LocalBounds_HalfTime`, `WeakHessian_LocalBounds_ReLp`, `WeakHessian_LocalBounds_RelaxedDomain`, `WeakHessian_LocalBounds_SpeedApprox`, `WeakHessian_LocalBounds_SquareControl`, `WeakHessian_LocalBounds_SubConst`, `WeakHessian_LocalBounds_SuperpositionProper`, `WeakHessian_LocalBounds_Young`, `WeakHessian_Measure_InlinedFile0`, `WeakHessian_Measure_LocalSlopeNotMem`, `WeakHessian_Measure_TimeMeasure`, `WeakHessian_Sobolev_AeEndpointGlobal`, `WeakHessian_Sobolev_CheegerEnergyCongrAe`, `WeakHessian_Sobolev_CheegerEnergySlope`, `WeakHessian_Sobolev_CongrAeLeft`, `WeakHessian_Sobolev_CutoffCheegerEnergy`, `WeakHessian_Sobolev_EndpointPairingBoundGlobal`, `WeakHessian_Sobolev_UpperGradientTendstoNorm`, `WeakHessian_Transport_AeActionData`, `WeakHessian_Transport_BoundedHopfLpDual`, `WeakHessian_Transport_BoundedHopfLpPairing`, `WeakHessian_Transport_BoundedHopfMap`, `WeakHessian_Transport_DynamicActionBound`, `WeakHessian_Transport_DynamicActionBoundProper`, `WeakHessian_Transport_HopfMap`, `WeakHessian_Transport_HopfObjective`, `WeakHessian_Transport_JoinControl`, `WeakHessian_Transport_JoinPlanPolish`, `WeakHessian_Transport_KineticAction`, `WeakHessian_Transport_LiftBoundedCoupling`, `WeakHessian_Transport_ProbabilityTightMarginals`, `WeakHessian_Transport_RestrictCurve`, `WeakHessian_Transport_TestPlanCostReference`, `WeakHessian_Transport_TruncatedQuadraticCost`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`; the bundles `OAIQ52Wh000` and `OAIQ52Wh001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ52Wh005` and `OAIQ52Wh006`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh000
import Definitions.Def_OAIQ52Wh001

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SquareControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

lemma IsSquareControl.intervalIntegrable {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) : IntervalIntegrable a volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  exact ha.2.1.integrable (by norm_num)

lemma IsSquareControl.dist_le_primitive {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) :
    dist (evalReal γ s) (evalReal γ t) ≤
      |(∫ r in (0:ℝ)..s, a r) - ∫ r in (0:ℝ)..t, a r| := by
  have hInt (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : IntervalIntegrable a volume 0 r :=
    ha.intervalIntegrable.mono_set (by
      simpa only [uIcc_of_le zero_le_one, uIcc_of_le hr.1] using
        (Icc_subset_Icc le_rfl hr.2))
  have hdom (s t : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
      (hst : s ≤ t) : dist (evalReal γ s) (evalReal γ t) ≤
        (∫ r in (0:ℝ)..t, a r)-(∫ r in (0:ℝ)..s, a r) := by
    rw [evalReal_of_mem hs, evalReal_of_mem ht,
      intervalIntegral.integral_interval_sub_left (hInt t ht) (hInt s hs)]
    exact ha.2.2.2 ⟨s,hs⟩ ⟨t,ht⟩ hst
  rcases le_total s t with hst | hts
  · exact (hdom s t hs ht hst).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have H := hdom t s ht hs hts
    rw [dist_comm] at H
    exact H.trans (le_abs_self _)

lemma IsSquareControl.metricSpeed_le {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) :
    ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), metricSpeed γ t ≤ ENNReal.ofReal (a t) := by
  have hder := ha.intervalIntegrable.ae_hasDerivAt_integral
  have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae h0, ae_restrict_of_ae h1, ha.2.2.1] with t htder ht ht0 ht1 hta
  have hti : t ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  have H := metricSpeed_le_of_deriv_control
    (htder (by simpa only [uIcc_of_le zero_le_one] using ht) 0 (by simp))
    (show ∀ᶠ s in 𝓝[≠] t, dist (evalReal γ s) (evalReal γ t) ≤
      |(∫ r in (0:ℝ)..s, a r) - ∫ r in (0:ℝ)..t, a r| from by
      have hnear : ∀ᶠ s in 𝓝[≠] t, s ∈ Ioo (0:ℝ) 1 :=
        nhdsWithin_le_nhds (Ioo_mem_nhds hti.1 hti.2)
      filter_upwards [hnear] with s hs
      exact ha.dist_le_primitive ⟨hs.1.le,hs.2.le⟩ ht)
  simpa only [abs_of_nonneg hta] using H

lemma IsSquareControl.isAC2 {γ : Curve X} {a : ℝ → ℝ}
    (ha : IsSquareControl γ a) : IsAC2 γ := by
  refine ⟨fun t => ENNReal.ofReal (a t), ENNReal.measurable_ofReal.comp ha.1, ?_, ?_⟩
  · have H := ha.2.1.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at H
    simp only [ENNReal.toReal_ofNat, one_div] at H
    have Hfin : (∫⁻ t in Icc (0:ℝ) 1, ‖a t‖ₑ ^ (2:ℝ)) < ∞ := by
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)).mp H
    apply lt_of_le_of_lt _ Hfin
    apply lintegral_mono
    intro t
    change (ENNReal.ofReal (a t))^2 ≤ ‖a t‖ₑ ^ (2:ℝ)
    rw [ENNReal.rpow_two]
    exact pow_le_pow_left₀ (by positivity) (by
      simpa only [← ofReal_norm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (le_abs_self (a t))) 2
  · intro s t hst
    have hsub : Icc (s:ℝ) (t:ℝ) ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc s.2.1 t.2.2
    have hint := (ha.2.1.integrable (by norm_num)).mono_measure (Measure.restrict_mono hsub le_rfl)
    have hnon := ae_mono (Measure.restrict_mono hsub le_rfl) ha.2.2.1
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnon,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst]
    simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (ha.2.2.2 s t hst)

end WeakHessian

open Set Filter Topology Bornology
open scoped InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_TimeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

lemma norm_intervalVector_sq (s t : Time) (hst : s ≤ t) :
    ‖intervalVector s t‖^2 = (t:ℝ)-(s:ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [intervalVector, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    inter_self, Measure.real]
  rw [Measure.restrict_apply measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc s.2.1 t.2.2), Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]

variable {X : Type*} [MetricSpace X]

lemma HasControlBound.dist_sq_le {γ : Curve X} {B : ℝ} (h : HasControlBound γ B)
    (s t : Time) : dist (γ s) (γ t)^2 ≤ |(s:ℝ)-(t:ℝ)| * B^2 := by
  have H (s t : Time) (hst : s ≤ t) :
      dist (γ s) (γ t)^2 ≤ ((t:ℝ)-(s:ℝ))*B^2 := by
    obtain ⟨u, hu, hud⟩ := h
    have hd := hud s t hst
    have hn := norm_inner_le_norm (𝕜 := ℝ) (intervalVector s t) u
    have hI : intervalFunctional s t u ≤ ‖intervalVector s t‖*B := by
      exact (le_abs_self _).trans (hn.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _)))
    have hsq := sq_le_sq₀ dist_nonneg (mul_nonneg (norm_nonneg _) ((norm_nonneg u).trans hu)) |>.mpr (hd.trans hI)
    simpa only [mul_pow, norm_intervalVector_sq s t hst] using hsq
  rcases le_total s t with hst | hts
  · simpa only [abs_sub_comm (s:ℝ), abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ (t:ℝ) from hst))] using H s t hst
  · simpa only [dist_comm (γ t), abs_of_nonneg (sub_nonneg.mpr (show (t:ℝ) ≤ (s:ℝ) from hts))] using H t s hts

lemma HasControlBound.squareControl {γ : Curve X} {B : ℝ} (h : HasControlBound γ B) :
    ∃ a : ℝ → ℝ, IsSquareControl γ a ∧
      (∫ r in Icc (0:ℝ) 1, (a r)^2) ≤ B^2 := by
  obtain ⟨u,hu,hud⟩ := h
  have habs : MemLp (fun r => |u r|) 2 timeMeasure := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp u).norm
  refine ⟨fun r => |u r|, ⟨(Lp.stronglyMeasurable u).measurable.abs, habs,
    ae_of_all _ (fun r => abs_nonneg _), ?_⟩, ?_⟩
  · intro s t hst
    have HD := hud s t hst
    rw [intervalFunctional_apply s t u hst] at HD
    exact HD.trans (intervalIntegral.integral_mono_on hst
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
        (((Lp.memLp u).integrable (by norm_num)).mono_measure
          (Measure.restrict_mono (Icc_subset_Icc s.2.1 t.2.2) le_rfl)))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr
        ((habs.integrable (by norm_num)).mono_measure
          (Measure.restrict_mono (Icc_subset_Icc s.2.1 t.2.2) le_rfl)))
      (fun r _ => le_abs_self _))
  · have heq : (∫ r in Icc (0:ℝ) 1, |u r|^2) = ‖u‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      congr 1
      ext r
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs]
    rw [heq]
    exact (sq_le_sq₀ (norm_nonneg u) ((norm_nonneg u).trans hu)).mpr hu

lemma isClosed_hasControlBound (B : ℝ) : IsClosed {γ : Curve X | HasControlBound γ B} := by
  apply isSeqClosed_iff_isClosed.mp
  intro γ g hγ hg
  let K : ℕ → Set ControlSpace := fun n => Metric.closedBall 0 B ∩
    ⋂ (s : Time) (t : Time) (_ : s ≤ t),
      {u | dist (g s) (g t) - 1/(n+1:ℝ) ≤ intervalFunctional s t u}
  have hKcl : ∀ n, IsClosed (K n) := fun n => Metric.isClosed_closedBall.inter
    (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le continuous_const (intervalFunctional s t).continuous)
  have hKconv : ∀ n, Convex ℝ (K n) := fun n => (convex_closedBall (0:ControlSpace) B).inter
    (convex_iInter fun s => convex_iInter fun t => convex_iInter fun _ =>
      (convex_Ici _).linear_preimage (intervalFunctional s t).toLinearMap)
  have hKanti : Antitone K := by
    intro n k hnk u hu
    refine ⟨hu.1, mem_iInter.mpr fun s => mem_iInter.mpr fun t => mem_iInter.mpr fun hst => ?_⟩
    have H := mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hu.2 s) t) hst
    have heps : 1/(k+1:ℝ) ≤ 1/(n+1:ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnk 1
    dsimp at H ⊢
    linarith
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨k,hk⟩ := (Metric.tendsto_atTop.mp hg (1/(2*(n+1:ℝ))) (by positivity))
    obtain ⟨u,hu,hud⟩ := hγ k
    refine ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu,
      mem_iInter.mpr fun s => mem_iInter.mpr fun t => mem_iInter.mpr fun hst => ?_⟩
    have hs := ContinuousMap.dist_apply_le_dist s (f := γ k) (g := g)
    have ht := ContinuousMap.dist_apply_le_dist t (f := γ k) (g := g)
    have he := hk k le_rfl
    have hd := (dist_triangle (g s) (γ k s) (g t)).trans
      (add_le_add le_rfl (dist_triangle (γ k s) (γ k t) (g t)))
    rw [dist_comm (g s) (γ k s)] at hd
    have heps : 1/(n+1:ℝ) = 2*(1/(2*(n+1:ℝ))) := by
      field_simp [show (n:ℝ)+1 ≠ 0 by positivity]
    have hi := hud s t hst
    dsimp
    linarith
  obtain ⟨u,hu⟩ := WeakHessianFunctional.nonempty_iInter_closed_convex hKne hKcl hKconv hKanti
    (Metric.isBounded_closedBall.subset inter_subset_left)
  refine ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using (mem_iInter.mp hu 0).1,
    fun s t hst => ?_⟩
  have Hall : ∀ n : ℕ, dist (g s) (g t) - 1/(n+1:ℝ) ≤ intervalFunctional s t u :=
    fun n => mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hu n).2 s) t) hst
  have htend : Tendsto (fun n : ℕ => dist (g s) (g t)-1/(n+1:ℝ)) atTop
      (𝓝 (dist (g s) (g t))) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := dist (g s) (g t))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto htend (Eventually.of_forall Hall)

end WeakHessian

open scoped BoundedContinuousFunction

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_ControlNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

lemma HasControlBound.dist_le_modulus {γ : Curve X} {B : ℝ} (h : HasControlBound γ B)
    (s t : Time) : dist (γ s) (γ t) ≤ Real.sqrt (dist s t)*|B| := by
  have H := h.dist_sq_le s t
  have hd : dist s t = |(s:ℝ)-(t:ℝ)| := rfl
  rw [← hd] at H
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt dist_nonneg, sq_abs] using H

lemma hasControlBound_of_forall_gt {γ : Curve X} {B : ℝ}
    (h : ∀ C : ℝ, B < C → HasControlBound γ C) : HasControlBound γ B := by
  let K : ℕ → Set ControlSpace := fun n => Metric.closedBall 0 (B+1/(n+1:ℝ)) ∩
    ⋂ (s : Time) (t : Time) (_ : s ≤ t),
      {u | dist (γ s) (γ t) ≤ intervalFunctional s t u}
  have hKcl : ∀ n, IsClosed (K n) := fun n => Metric.isClosed_closedBall.inter
    (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le continuous_const (intervalFunctional s t).continuous)
  have hKconv : ∀ n, Convex ℝ (K n) := fun n => (convex_closedBall (0:ControlSpace) _).inter
    (convex_iInter fun s => convex_iInter fun t => convex_iInter fun _ =>
      (convex_Ici _).linear_preimage (intervalFunctional s t).toLinearMap)
  have hKanti : Antitone K := by
    intro n k hnk u hu
    refine ⟨?_, hu.2⟩
    apply Metric.closedBall_subset_closedBall _ hu.1
    have heps : 1/(k+1:ℝ) ≤ 1/(n+1:ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnk 1
    linarith
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨u,hu,hud⟩ := h (B+1/(n+1:ℝ)) (by
      have he : 0 < 1/(n+1:ℝ) := by positivity
      linarith)
    exact ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu,
      mem_iInter.mpr fun s => mem_iInter.mpr fun t => mem_iInter.mpr fun hst => hud s t hst⟩
  obtain ⟨u,hu⟩ := WeakHessianFunctional.nonempty_iInter_closed_convex hKne hKcl hKconv hKanti
    (Metric.isBounded_closedBall.subset inter_subset_left)
  refine ⟨u, ?_, fun s t hst =>
    mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hu 0).2 s) t) hst⟩
  have Hall : ∀ n : ℕ, ‖u‖ ≤ B+1/(n+1:ℝ) := fun n => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (mem_iInter.mp hu n).1
  apply ge_of_tendsto (by simpa only [add_zero] using
    (tendsto_const_nhds (x := B)).add tendsto_one_div_add_atTop_nhds_zero_nat)
  exact Eventually.of_forall Hall

lemma controlNorm_le_iff {γ : Curve X} {B : ℝ} (hB : 0 ≤ B) :
    controlNorm γ ≤ ENNReal.ofReal B ↔ HasControlBound γ B := by
  refine ⟨fun h => hasControlBound_of_forall_gt fun C hC => ?_, controlNorm_le⟩
  have hlt : controlNorm γ < ENNReal.ofReal C :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hB.trans_lt hC)).mpr hC)
  obtain ⟨D,hD⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hD,hdlt⟩ := iInf_lt_iff.mp hD
  have hDC : D < C := (ENNReal.ofReal_lt_ofReal_iff (hB.trans_lt hC)).mp hdlt
  obtain ⟨u,hu,hud⟩ := hD
  exact ⟨u,hu.trans hDC.le,hud⟩

lemma lowerSemicontinuous_controlNorm : LowerSemicontinuous (controlNorm (X := X)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  by_cases ha : a = ∞
  · simp [ha]
  · have heq : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    rw [heq]
    change IsClosed {γ : Curve X | controlNorm γ ≤ ENNReal.ofReal a.toReal}
    simp_rw [controlNorm_le_iff ENNReal.toReal_nonneg]
    exact isClosed_hasControlBound _

lemma controlNorm_lt_top_iff {γ : Curve X} :
    controlNorm γ < ∞ ↔ ∃ B : ℝ, HasControlBound γ B := by
  refine ⟨fun h => ⟨(controlNorm γ).toReal, ?_⟩, ?_⟩
  · apply (controlNorm_le_iff ENNReal.toReal_nonneg).mp
    rw [ENNReal.ofReal_toReal h.ne]
  · rintro ⟨B,hB⟩
    exact lt_of_le_of_lt (controlNorm_le hB) ENNReal.ofReal_lt_top

lemma controlNorm_finite_isAC2 {γ : Curve X} (h : controlNorm γ < ∞) : IsAC2 γ := by
  obtain ⟨B,hB⟩ := controlNorm_lt_top_iff.mp h
  obtain ⟨a,ha,_⟩ := hB.squareControl
  exact ha.isAC2

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_KineticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

lemma lowerSemicontinuous_kineticAction : LowerSemicontinuous (kineticAction (X := X)) :=
  (ENNReal.continuous_pow 2).comp_lowerSemicontinuous lowerSemicontinuous_controlNorm
    (fun _ _ h => pow_le_pow_left₀ (bot_le) h 2)

lemma kineticAction_finite_controlNorm {γ : Curve X} (h : kineticAction γ < ∞) :
    controlNorm γ < ∞ := by
  by_contra hn
  have heq : controlNorm γ = ∞ := top_unique (not_lt.mp hn)
  simp [kineticAction, heq] at h

lemma speed_energy_le_kineticAction (γ : Curve X) :
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤ kineticAction γ := by
  by_cases h : kineticAction γ = ∞
  · simp [h]
  have hn := kineticAction_finite_controlNorm (lt_top_iff_ne_top.mpr h)
  have hB : HasControlBound γ (controlNorm γ).toReal :=
    (controlNorm_le_iff ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hn.ne])
  obtain ⟨a,ha,haB⟩ := hB.squareControl
  calc
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤
        ∫⁻ t in Icc (0:ℝ) 1, (ENNReal.ofReal (a t))^2 :=
      lintegral_mono_ae (ha.metricSpeed_le.mono fun t ht => pow_le_pow_left₀ (bot_le) ht 2)
    _ = ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal ((a t)^2) := by
      apply lintegral_congr_ae
      filter_upwards [ha.2.2.1] with t ht
      exact (ENNReal.ofReal_pow ht 2).symm
    _ = ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, (a t)^2) :=
      (ofReal_integral_eq_lintegral_ofReal ha.2.1.integrable_sq (ae_of_all _ (fun t => sq_nonneg _))).symm
    _ ≤ ENNReal.ofReal ((controlNorm γ).toReal^2) := ENNReal.ofReal_le_ofReal haB
    _ = kineticAction γ := by rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hn.ne]; rfl

lemma kineticAction_finite_isAC2 {γ : Curve X} (h : kineticAction γ < ∞) : IsAC2 γ :=
  controlNorm_finite_isAC2 (kineticAction_finite_controlNorm h)

end WeakHessian

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactAnchoredControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

lemma isCompact_anchoredControl [ProperSpace X] [Nonempty X]
    {K : Set X} (hK : IsCompact K) (B : ℝ) :
    IsCompact {γ : Curve X | HasControlBound γ B ∧ γ timeZero ∈ K} := by
  let o : X := Classical.arbitrary X
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall o
  let e := ContinuousMap.isometryEquivBoundedOfCompact Time X
  let A : Set (Time →ᵇ X) := e.symm ⁻¹' {γ : Curve X | HasControlBound γ B ∧ γ timeZero ∈ K}
  have hcl : IsClosed A := ((isClosed_hasControlBound B).inter
    (hK.isClosed.preimage (continuous_eval_const timeZero))).preimage e.symm.continuous
  have heq : Equicontinuous ((↑) : A → Time → X) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => Real.sqrt r*|B|)
    · simpa using (Real.continuous_sqrt.tendsto 0).mul_const |B|
    · intro s t γ
      exact γ.2.1.dist_le_modulus s t
  have hin (f : Time →ᵇ X) (t : Time) (hf : f ∈ A) : f t ∈ Metric.closedBall o (R+|B|) := by
    change HasControlBound (e.symm f) B ∧ (e.symm f) timeZero ∈ K at hf
    have H := hf.1.dist_le_modulus t timeZero
    have ht : dist t timeZero ≤ 1 := by
      change |(t:ℝ)-0| ≤ 1
      rw [sub_zero,abs_of_nonneg t.2.1]
      exact t.2.2
    have hd : dist (f t) (f timeZero) ≤ |B| := by
      apply H.trans
      have hh := Real.sqrt_le_sqrt ht
      simpa only [Real.sqrt_one,one_mul] using mul_le_mul_of_nonneg_right hh (abs_nonneg B)
    have hzero : dist (f timeZero) o ≤ R := hR hf.2
    exact (dist_triangle (f t) (f timeZero) o).trans (by linarith)
  have hc := BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall o (R+|B|))
    (isCompact_closedBall o _) A hcl hin heq
  have H := hc.image e.symm.continuous
  have he : e.symm '' A = {γ : Curve X | HasControlBound γ B ∧ γ timeZero ∈ K} :=
    e.symm.toEquiv.image_preimage _
  rwa [he] at H

lemma exists_action_uniform_tail
    (S : Set (ProbabilityMeasure (Curve X))) {C : ℝ≥0∞} (hC : C < ∞)
    (hS : ∀ π ∈ S, (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C) :
    ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ →
      ∃ R : ℝ, ∀ π ∈ S, (π:Measure (Curve X)) {γ | HasControlBound γ R}ᶜ ≤ ε := by
  intro ε hε hεtop
  have hdiv : C/ε ≠ ∞ := ENNReal.div_ne_top hC.ne hε.ne'
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hdiv
  let R : ℝ := (n:ℝ)+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRne : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hRfin : ENNReal.ofReal R ≠ ∞ := ENNReal.ofReal_ne_top
  have hquo : C/ε ≤ (ENNReal.ofReal R)^2 := by
    have h1 : C/ε ≤ ENNReal.ofReal R := by
      apply hn.le.trans
      simp only [R, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one]
      exact le_add_right le_rfl
    have h2 : (1:ℝ≥0∞) ≤ ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      dsimp [R]
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    exact h1.trans (by simpa only [pow_two, mul_one] using mul_le_mul_right h2 (ENNReal.ofReal R))
  have hquot : C/(ENNReal.ofReal R)^2 ≤ ε := by
    apply (ENNReal.div_le_iff (pow_ne_zero _ hRne) (ENNReal.pow_ne_top hRfin)).mpr
    have hc := (ENNReal.div_le_iff hε.ne' hεtop).mp hquo
    simpa only [mul_comm] using hc
  refine ⟨R,?_⟩
  intro π hπ
  calc
    (π:Measure (Curve X)) {γ : Curve X | HasControlBound γ R}ᶜ ≤
        (π:Measure (Curve X)) {γ | (ENNReal.ofReal R)^2 ≤ kineticAction γ} := by
      apply measure_mono
      intro γ hγ
      have hnot : ¬ controlNorm γ ≤ ENNReal.ofReal R :=
        fun h => hγ ((controlNorm_le_iff hR.le).mp h)
      exact pow_le_pow_left₀ (bot_le) (le_of_not_ge hnot) 2
    _ ≤ (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X)))/(ENNReal.ofReal R)^2 :=
      meas_ge_le_lintegral_div lowerSemicontinuous_kineticAction.measurable.aemeasurable
        (pow_ne_zero _ hRne) (ENNReal.pow_ne_top hRfin)
    _ ≤ C/(ENNReal.ofReal R)^2 := ENNReal.div_le_div_right (hS π hπ) _
    _ ≤ ε := hquot

variable [MeasurableSpace X] [BorelSpace X]

lemma probability_isTight_of_action_initial [ProperSpace X] [Nonempty X]
    (S : Set (ProbabilityMeasure (Curve X))) {C : ℝ≥0∞} (hC : C < ∞)
    (hS : ∀ π ∈ S, (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C)
    (ht : IsTightMeasureSet {((π:Measure (Curve X)).map (fun γ => γ timeZero)) | π ∈ S}) :
    IsTightMeasureSet {((π:Measure (Curve X))) | π ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht ⊢
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨∅,isCompact_empty,fun _ _ => by simp [htop]⟩
  have hhalf : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hft : ε/2 ≠ ∞ := ENNReal.div_ne_top htop (by norm_num)
  obtain ⟨R,hR⟩ := exists_action_uniform_tail S hC hS (ε/2) hhalf hft
  obtain ⟨K,hK,hKm⟩ := ht (ε/2) hhalf
  refine ⟨{γ : Curve X | HasControlBound γ R ∧ γ timeZero ∈ K},
    isCompact_anchoredControl hK R,?_⟩
  rintro μ ⟨π,hπ,rfl⟩
  have hi : (π:Measure (Curve X)) ((fun γ => γ timeZero) ⁻¹' K)ᶜ ≤ ε/2 := by
    have H := hKm _ ⟨π,hπ,rfl⟩
    rwa [Measure.map_apply (continuous_eval_const timeZero).measurable hK.measurableSet.compl] at H
  calc
    (π:Measure (Curve X)) {γ | HasControlBound γ R ∧ γ timeZero ∈ K}ᶜ =
        (π:Measure (Curve X)) ({γ | HasControlBound γ R}ᶜ ∪ ((fun γ => γ timeZero) ⁻¹' K)ᶜ) := by
      congr 1
      ext γ
      simp only [mem_compl_iff,mem_ofPred_eq,not_and_or,mem_union,mem_preimage]
    _ ≤ (π:Measure (Curve X)) {γ | HasControlBound γ R}ᶜ +
        (π:Measure (Curve X)) ((fun γ => γ timeZero) ⁻¹' K)ᶜ := measure_union_le _ _
    _ ≤ ε/2+ε/2 := add_le_add (hR π hπ) hi
    _ = ε := ENNReal.add_halves ε

lemma exists_action_limit_initial [ProperSpace X] [Nonempty X]
    (πs : ℕ → ProbabilityMeasure (Curve X)) {C : ℝ≥0∞} (hC : C < ∞)
    (hπs : ∀ n, (∫⁻ γ, kineticAction γ ∂(πs n:Measure (Curve X))) ≤ C)
    (ht : IsTightMeasureSet {((πs n:Measure (Curve X)).map (fun γ => γ timeZero)) | n : ℕ}) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (πs ∘ φ) atTop (𝓝 π) ∧
      (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsAC2 γ) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂(π:Measure (Curve X))) ≤ C := by
  have ht' : IsTightMeasureSet {((π:Measure (Curve X)).map (fun γ => γ timeZero)) | π ∈ range πs} := by
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ext μ
    simp
  have htight := probability_isTight_of_action_initial (range πs) hC
    (by rintro _ ⟨n,rfl⟩; exact hπs n) ht'
  obtain ⟨π,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have hbound : (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ C := by
    have H := WeakHessianTransport.lsc_lintegral_le_liminf_of_tendsto hlim lowerSemicontinuous_kineticAction
    exact H.trans (liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall (fun n => hπs (φ n)))))
  refine ⟨π,φ,hφ,hlim,hbound,?_,?_⟩
  · have hfinite := ae_lt_top lowerSemicontinuous_kineticAction.measurable (hbound.trans_lt hC).ne
    exact hfinite.mono fun γ hγ => kineticAction_finite_isAC2 hγ
  · exact (lintegral_mono speed_energy_le_kineticAction).trans hbound
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_InlinedFile0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

lemma locallyL2_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : LocallyL2 m f ↔ LocallyL2 ν f :=
  ⟨fun h => h.of_measure_le_smul hν, fun h => h.of_measure_le_smul hm⟩

lemma weakGradient_isMinimal {f : X → ℝ}
    (hf : ∃ W, IsMinimalLocalWeakUpperGradient m f W) :
    IsMinimalLocalWeakUpperGradient m f (weakGradient m f) := by
  simpa only [weakGradient, dite_eq_left hf] using Classical.choose_spec hf

lemma weakGradient_ae_eq_of_isMinimal {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) : weakGradient m f =ᵐ[m] D :=
  (weakGradient_isMinimal ⟨D, hD⟩).ae_eq hD

lemma weakGradient_const (c : ℝ) :
    weakGradient m (fun _ => c) =ᵐ[m] (fun _ => 0) :=
  weakGradient_ae_eq_of_isMinimal (isMinimalLocalWeakUpperGradient_const c)

lemma weakGradient_nonneg (f : X → ℝ) : ∀ᵐ x ∂m, 0 ≤ weakGradient m f x := by
  by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact (weakGradient_isMinimal h).1.2.1
  · simp only [weakGradient, dite_eq_right h, Pi.zero_apply, le_refl, eventually_true]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SpeedApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsLocalWeakUpperGradient.ae_endpoint_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  have hfm := ((hπ.aemeasurable_eval hf timeOne).sub
    (hπ.aemeasurable_eval hf timeZero)).abs.ennreal_ofReal
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hfm
  intro S _hS hSfin
  by_cases hS : π S = 0
  · simp only [Measure.restrict_eq_zero.mpr hS, lintegral_zero_measure, le_refl]
  have hSpos : 0 < π S := pos_iff_ne_zero.mpr hS
  let ρ := (π S)⁻¹ • π.restrict S
  have hρdom : ρ ≤ (π S)⁻¹ • π := by
    change (π S)⁻¹ • π.restrict S ≤ (π S)⁻¹ • π
    gcongr
    exact Measure.restrict_le_self
  have hρp : IsProbabilityMeasure ρ := by
    constructor
    simp only [ρ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      ENNReal.inv_mul_cancel hS hSfin.ne]
  have hρt := hπ.of_plan_le_smul hρp (ENNReal.inv_lt_top.mpr hSpos) hρdom
  have hρb := hb.of_plan_le_smul hρdom
  have hh := hD.2.2 ρ hρt hρb
  simp only [ρ, lintegral_smul_measure] at hh
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.mpr hSfin.ne)
    (ENNReal.inv_ne_top.mpr hS)).mp hh

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AbsolutelyContinuousDistDom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessianCalculus

lemma exists_ac_representative {q : ℝ → ℝ} {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    (d : ℕ → Icc (0 : ℝ) 1)
    (hbound : ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |q (d j) - q (d i)| ≤ ∫⁻ t in Icc (d i : ℝ) (d j : ℝ), a t) :
    ∃ q' : ℝ → ℝ, AbsolutelyContinuousOnInterval q' 0 1 ∧
      ∀ i, q' (d i) = q (d i) := by
  classical
  let A : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, (a r).toReal
  have hdom : ∀ i j, dist (q (d i)) (q (d j)) ≤ dist (A (d i)) (A (d j)) := by
    intro i j
    rcases lt_trichotomy (d i : ℝ) (d j : ℝ) with h|h|h
    · exact action_dist_primitive ha hfin (d i).property (d j).property h.le (hbound i j h)
    · simp only [h, dist_self, le_refl]
    · simpa only [dist_comm] using
        action_dist_primitive ha hfin (d j).property (d i).property h.le (hbound j i h)
  let S : Set ℝ := Set.range (fun i => A (d i))
  let Q : ℝ → ℝ := fun x => if hx : x ∈ S then q (d (Classical.choose hx)) else 0
  have hQ : ∀ i, Q (A (d i)) = q (d i) := by
    intro i
    have hi : A (d i) ∈ S := ⟨i,rfl⟩
    dsimp only [Q]
    rw [dite_eq_left hi]
    apply dist_le_zero.mp
    simpa only [Classical.choose_spec hi, dist_self] using hdom (Classical.choose hi) i
  have hLip : LipschitzOnWith 1 Q S := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    simpa only [hQ, NNReal.coe_one, one_mul] using hdom i j
  obtain ⟨Q',hLip',hEq⟩ := hLip.extend_real
  refine ⟨fun t => Q' (A t), ?_, ?_⟩
  · have hA : AbsolutelyContinuousOnInterval A 0 1 :=
      (action_intervalIntegrable ha hfin).absolutelyContinuousOnInterval_intervalIntegral (by simp)
    apply absolutelyContinuous_of_dist_dom hA
    intro s _ t _
    simpa only [NNReal.coe_one, one_mul] using hLip'.dist_le_mul (A s) (A t)
  · intro i
    exact (hEq ⟨i,rfl⟩).symm.trans (hQ i)

end WeakHessianCalculus

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AffineTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X]

lemma clampTime_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (clampTime t : ℝ) = t := by
  simp only [clampTime, min_eq_right ht.2, max_eq_right ht.1]

lemma evalReal_restrictCurve {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (a b : Time) (γ : Curve X) :
    evalReal (restrictCurve a b γ) t = evalReal γ ((a : ℝ) + ((b : ℝ) - a) * t) := by
  have hv : (affineTime a b (clampTime t) : ℝ) = (a : ℝ) + ((b : ℝ) - a) * t := by
    simp only [affineTime, clampTime_of_mem ht]
    ring
  have hh : (a : ℝ) + ((b : ℝ) - a) * t ∈ Set.Icc (0 : ℝ) 1 :=
    hv ▸ (affineTime a b (clampTime t)).property
  change γ (affineTime a b (clampTime t)) = γ (clampTime _)
  congr 1
  apply Subtype.ext
  rw [hv, clampTime_of_mem hh]

lemma metricSpeed_restrictCurve (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    metricSpeed (restrictCurve a b γ) t =
      ENNReal.ofReal ((b : ℝ) - a) * metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t) := by
  let c : ℝ := (b : ℝ) - a
  have hc : 0 < c := sub_pos.mpr hab
  let e := affineHomeomorph (a : ℝ) c hc.ne'
  have hnh : Filter.map e (𝓝[≠] t) = 𝓝[≠] (e t) := e.map_punctured_nhds_eq t
  have heq : (fun s : ℝ => ENNReal.ofReal
      (dist (evalReal (restrictCurve a b γ) s) (evalReal (restrictCurve a b γ) t) / |s - t|))
      =ᶠ[𝓝[≠] t] (fun s => ENNReal.ofReal c * ENNReal.ofReal
        (dist (evalReal γ (e s)) (evalReal γ (e t)) / |e s - e t|)) := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2),
      self_mem_nhdsWithin] with s hs hst
    rw [evalReal_restrictCurve ⟨hs.1.le, hs.2.le⟩,
      evalReal_restrictCurve ⟨ht.1.le, ht.2.le⟩]
    change ENNReal.ofReal (dist (evalReal γ (e s)) (evalReal γ (e t)) / |s - t|) = _
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    have hd : |e s - e t| = c * |s - t| := by
      dsimp [e, affineHomeomorph]
      change |(a : ℝ) + c * s - ((a : ℝ) + c * t)| = c * |s - t|
      rw [show (a : ℝ) + c * s - ((a : ℝ) + c * t) = c * (s - t) by ring,
        abs_mul, abs_of_pos hc]
    rw [hd]
    field_simp
  unfold metricSpeed
  rw [Filter.limsup_congr heq, ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr 1
  change Filter.limsup (fun s => ENNReal.ofReal
    (dist (evalReal γ (e s)) (evalReal γ (e t)) / |e s - e t|)) (𝓝[≠] t) =
    Filter.limsup (fun s => ENNReal.ofReal
      (dist (evalReal γ s) (evalReal γ (e t)) / |s - e t|)) (𝓝[≠] (e t))
  rw [← hnh]
  rfl

lemma coe_affineTime (a b u : Time) :
    (affineTime a b u : ℝ) = (a : ℝ) + ((b : ℝ) - a) * (u : ℝ) := by
  simp only [affineTime]
  ring

lemma IsAC2.restrictCurve {γ : Curve X} (hγ : IsAC2 γ) (a b : Time)
    (hab : (a : ℝ) < b) : IsAC2 (restrictCurve a b γ) := by
  obtain ⟨u, hum, hue, hub⟩ := hγ
  let c : ℝ := (b : ℝ) - a
  have hc : 0 < c := sub_pos.mpr hab
  refine ⟨fun t => ENNReal.ofReal c * u ((a : ℝ) + c * t),
    measurable_const.mul (hum.comp (by fun_prop)), ?_, ?_⟩
  · rw [lintegral_scaled_sq_affine_Icc _ _ hc]
    have hends : (a : ℝ) + c * 0 = a ∧ (a : ℝ) + c * 1 = b := by
      dsimp [c]
      constructor <;> ring
    rw [hends.1, hends.2]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact (lintegral_mono_set (Set.Icc_subset_Icc a.property.1 b.property.2)).trans_lt hue
  · intro s t hst
    have hst' : (affineTime a b s : ℝ) ≤ affineTime a b t := by
      rw [coe_affineTime, coe_affineTime]
      dsimp [c] at hc
      gcongr
    calc
      edist (WeakHessian.restrictCurve a b γ s) (WeakHessian.restrictCurve a b γ t) =
          edist (γ (affineTime a b s)) (γ (affineTime a b t)) := rfl
      _ ≤ ∫⁻ r in Set.Icc (affineTime a b s : ℝ) (affineTime a b t : ℝ), u r :=
        hub _ _ hst'
      _ = ∫⁻ r in Set.Icc (s : ℝ) (t : ℝ), ENNReal.ofReal c * u ((a : ℝ) + c * r) := by
        simpa only [coe_affineTime] using
          (lintegral_scaled_affine_Icc (a : ℝ) c hc (s : ℝ) (t : ℝ) u).symm

lemma ae_metricSpeed_restrictCurve (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X) :
    (fun t => metricSpeed (restrictCurve a b γ) t) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun t => ENNReal.ofReal ((b : ℝ) - a) *
        metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t)) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht =>
    metricSpeed_restrictCurve a b hab γ ht)

lemma kineticEnergy_restrictCurve (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed (restrictCurve a b γ) t ^ 2) =
      ENNReal.ofReal ((b : ℝ) - a) * ∫⁻ t in Set.Icc (a : ℝ) b, metricSpeed γ t ^ 2 := by
  have heq : (fun t => metricSpeed (restrictCurve a b γ) t ^ 2) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun t => (ENNReal.ofReal ((b : ℝ) - a) * metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t)) ^ 2) :=
    (ae_metricSpeed_restrictCurve a b hab γ).pow_const 2
  rw [lintegral_congr_ae heq, lintegral_scaled_sq_affine_Icc _ _ (sub_pos.mpr hab)]
  rw [show (a : ℝ) + ((b : ℝ) - a) * 0 = a by ring,
    show (a : ℝ) + ((b : ℝ) - a) * 1 = b by ring]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_RestrictCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.restrictCurve {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (a b : Time) (hab : (a : ℝ) < b) :
    IsTestPlan m (Measure.map (WeakHessian.restrictCurve a b) π) := by
  let : IsProbabilityMeasure π := hπ.1
  have hr := continuous_restrictCurve (X := X) a b
  obtain ⟨C, hC⟩ := hπ.2.1
  refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),
    ⟨C, fun t => ?_⟩, ?_, ?_⟩
  · rw [Measure.map_map (continuous_eval_const t).measurable hr.measurable]
    exact hC (affineTime a b t)
  · apply continuous_ae_map_of_ae hr
    filter_upwards [hπ.2.2.1] with γ hγ
    exact hγ.restrictCurve a b hab
  · rw [lintegral_map (measurable_metricSpeed.pow_const 2).lintegral_prod_right hr.measurable]
    calc
      (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed (WeakHessian.restrictCurve a b γ) t ^ 2 ∂volume ∂π) =
          ENNReal.ofReal ((b : ℝ) - a) *
            ∫⁻ γ, ∫⁻ t in Set.Icc (a : ℝ) b, metricSpeed γ t ^ 2 ∂volume ∂π := by
        simp_rw [kineticEnergy_restrictCurve a b hab]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((b : ℝ) - a) *
            ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂π := by
        gcongr 1
        exact lintegral_mono fun γ =>
          lintegral_mono_set (Set.Icc_subset_Icc a.property.1 b.property.2)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hπ.2.2.2

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma action_restrictCurve (D : X → ℝ) (a b : Time) (hab : (a : ℝ) < b) (γ : Curve X) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal (restrictCurve a b γ) t)) * metricSpeed (restrictCurve a b γ) t) =
    ∫⁻ t in Set.Icc (a : ℝ) b, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  have heq : (fun t => ENNReal.ofReal (D (evalReal (restrictCurve a b γ) t)) *
      metricSpeed (restrictCurve a b γ) t) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun t => ENNReal.ofReal ((b : ℝ) - a) *
        (ENNReal.ofReal (D (evalReal γ ((a : ℝ) + ((b : ℝ) - a) * t))) *
          metricSpeed γ ((a : ℝ) + ((b : ℝ) - a) * t))) := by
    filter_upwards [ae_metricSpeed_restrictCurve a b hab γ, ae_restrict_mem measurableSet_Icc]
      with t ht hm
    rw [ht, evalReal_restrictCurve hm]
    ac_rfl
  rw [lintegral_congr_ae heq,
    lintegral_scaled_affine_Icc (a : ℝ) ((b : ℝ) - a) (sub_pos.mpr hab) 0 1
      (fun t => ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t)]
  rw [show (a : ℝ) + ((b : ℝ) - a) * 0 = a by ring,
    show (a : ℝ) + ((b : ℝ) - a) * 1 = b by ring]

lemma IsLocalWeakUpperGradient.ae_subinterval_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (a b : Time) (hab : (a : ℝ) < b) :
    ∀ᵐ γ ∂π, ENNReal.ofReal |f (γ b) - f (γ a)| ≤
      ∫⁻ t in Set.Icc (a : ℝ) b, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  have ht := hD.ae_endpoint_le hf (hπ.restrictCurve a b hab) (hb.restrictCurve a b)
  have hh := ae_of_ae_map (continuous_restrictCurve a b).measurable.aemeasurable ht
  filter_upwards [hh] with γ hγ
  simpa only [restrictCurve_zero, restrictCurve_one, action_restrictCurve D a b hab γ] using hγ

end WeakHessian

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma IsTestPlan.lintegral_eval_le {π : Measure (Curve X)} (_hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {q : X → ℝ≥0∞} (hq : AEMeasurable q m) (t : Time) :
    (∫⁻ γ, q (γ t) ∂π) ≤ (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := by
  have hqm := hq.mono_ac (Measure.absolutelyContinuous_of_le_smul (hC t))
  rw [← lintegral_map' hqm (continuous_eval_const t).measurable.aemeasurable]
  calc
    (∫⁻ x, q x ∂Measure.map (fun γ : Curve X => γ t) π) ≤
        ∫⁻ x, q x ∂(C : ℝ≥0∞) • m := lintegral_mono' (hC t) le_rfl
    _ = _ := lintegral_smul_measure _ _

lemma IsTestPlan.lintegral_square_eval_lt_top {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) {D : X → ℝ} (hD : LocallyL2 m D) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂volume ∂π) < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨o, R, hR, hbound⟩ := hb
  obtain ⟨C, hC⟩ := hπ.2.1
  let q : X → ℝ≥0∞ := (Metric.ball o (R+1)).indicator (fun x => ENNReal.ofReal (D x ^ 2))
  have hqm : AEMeasurable q m :=
    (hD.aemeasurable.pow_const 2).ennreal_ofReal.indicator measurableSet_ball
  have hqfinite : (∫⁻ x, q x ∂m) < ∞ := by
    dsimp only [q]
    rw [lintegral_indicator measurableSet_ball]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg (D x))).mp
      (hD o (R+1) (by linarith)).integrable_sq.hasFiniteIntegral
  have hstep : ∀ t : ℝ,
      (∫⁻ γ, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂π) ≤
        (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := by
    intro t
    have heq : (fun γ : Curve X => ENNReal.ofReal ((D (evalReal γ t)) ^ 2)) =ᵐ[π]
        (fun γ => q (evalReal γ t)) := by
      filter_upwards [hbound] with γ hγ
      have hmem : evalReal γ t ∈ Metric.ball o (R+1) := (hγ (clampTime t)).trans_lt (by linarith)
      change _ = (Metric.ball o (R+1)).indicator (fun x => ENNReal.ofReal (D x ^ 2)) (evalReal γ t)
      exact (Set.indicator_of_mem hmem (fun x : X => ENNReal.ofReal (D x ^ 2))).symm
    rw [lintegral_congr_ae heq]
    exact hπ.lintegral_eval_le hC hqm (clampTime t)
  have hm : AEMeasurable (fun z : Curve X × ℝ => ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2))
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    ((hπ.aemeasurable_evalReal hD.aemeasurable).pow_const 2).ennreal_ofReal
  rw [lintegral_lintegral_swap hm]
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) 1, ∫⁻ γ, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂π) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := lintegral_mono hstep
    _ = (C : ℝ≥0∞) * ∫⁻ x, q x ∂m := by simp
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top hqfinite

lemma IsTestPlan.lintegral_action_lt_top {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) (hb : BoundedTracks π) {D : X → ℝ} (hD : LocallyL2 m D) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π) < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hmul : ∀ u v : ℝ≥0∞, u*v ≤ u^2+v^2 := by
    intro u v
    rcases le_total u v with h|h
    · calc
        u*v ≤ v*v := mul_le_mul_left h v
        _ ≤ u^2+v^2 := by simp only [pow_two]; exact le_add_left le_rfl
    · calc
        u*v ≤ u*u := mul_le_mul_right h u
        _ ≤ u^2+v^2 := by simp only [pow_two]; exact le_add_right le_rfl
  have hsq : ∀ z : Curve X × ℝ,
      ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2 ≤
        ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2) + metricSpeed z.1 z.2 ^ 2 := by
    intro z
    exact (hmul _ _).trans (add_le_add_left (ofReal_sq_le_ofReal_sq _) _)
  have hmD := ((hπ.aemeasurable_evalReal hD.aemeasurable).pow_const 2).ennreal_ofReal
  rw [← lintegral_prod _ (hπ.aemeasurable_action hD)]
  calc
    (∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2 ∂π.prod ν) ≤
        ∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2) + metricSpeed z.1 z.2 ^ 2 ∂π.prod ν :=
      lintegral_mono hsq
    _ = (∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2) ^ 2) ∂π.prod ν) +
        ∫⁻ z, metricSpeed z.1 z.2 ^ 2 ∂π.prod ν := lintegral_add_left' hmD _
    _ = (∫⁻ γ, ∫⁻ t, ENNReal.ofReal ((D (evalReal γ t)) ^ 2) ∂ν ∂π) +
        ∫⁻ γ, ∫⁻ t, metricSpeed γ t ^ 2 ∂ν ∂π := by
      rw [lintegral_prod _ hmD, lintegral_prod _ (measurable_metricSpeed.pow_const 2).aemeasurable]
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hπ.lintegral_square_eval_lt_top hb hD, hπ.2.2.2⟩

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_AeActionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsLocalWeakUpperGradient.ae_action_data {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π,
      AEMeasurable (fun t => ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t)
        (volume.restrict (Icc (0 : ℝ) 1)) ∧
      (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t) < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := volume.restrict (Icc (0 : ℝ) 1)
  let a : Curve X × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2
  have ham : AEMeasurable a (π.prod ν) := hπ.aemeasurable_action hD.1
  have hameq := Measure.ae_ae_eq_curry_of_prod ham.ae_eq_mk
  have hafin := ae_lt_top' ham.lintegral_prod_right' (hπ.lintegral_action_lt_top hb hD.1).ne
  filter_upwards [hameq, hafin] with γ hameq hafin
  exact ⟨(ham.measurable_mk.comp measurable_prodMk_left).aemeasurable.congr hameq.symm, hafin⟩

lemma IsLocalWeakUpperGradient.ae_dense_subinterval_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) (d : ℕ → Time) :
    ∀ᵐ γ ∂π, ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |f (γ (d j)) - f (γ (d i))| ≤
        ∫⁻ t in Icc (d i : ℝ) (d j : ℝ),
          ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : (d i : ℝ) < d j
  · exact (hD.ae_subinterval_le hf hπ hb (d i) (d j) hij).mono (fun _ h => fun _ => h)
  · exact ae_of_all _ fun _ h => (hij h).elim

lemma IsLocalWeakUpperGradient.min_measurable {f D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m f E)
    (hf : AEMeasurable f m) : IsLocalWeakUpperGradient m f (fun x => Min.min (D x) (E x)) := by
  refine ⟨hD.1.min hE.1, ?_, ?_⟩
  · filter_upwards [hD.2.1, hE.2.1] with x hx hy
    exact le_min hx hy
  · intro π hπ hb
    let : Nonempty Time := ⟨timeZero⟩
    let d : ℕ → Time := fun n => match n with
      | 0 => timeZero
      | 1 => timeOne
      | n + 2 => TopologicalSpace.denseSeq Time n
    have hd : DenseRange d := by
      apply DenseRange.of_comp (g := fun n => n + 2)
      exact TopologicalSpace.denseRange_denseSeq Time
    apply lintegral_mono_ae
    filter_upwards [hD.ae_action_data hπ hb, hE.ae_action_data hπ hb,
      hD.ae_dense_subinterval_le hf hπ hb d, hE.ae_dense_subinterval_le hf hπ hb d]
      with γ hDa hEa hDb hEb
    have hDb' : ∀ i j, (d i : ℝ) < d j →
        ENNReal.ofReal |f (evalReal γ (d j)) - f (evalReal γ (d i))| ≤
          ∫⁻ t in Icc (d i : ℝ) (d j : ℝ),
            ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
      simpa only [evalReal_coe] using hDb
    obtain ⟨q,hq,heq⟩ := WeakHessianCalculus.exists_ac_representative (q := fun t => f (evalReal γ t)) hDa.1 hDa.2 d hDb'
    have hqd : ∀ i, q (d i) = f (γ (d i)) := by
      simpa only [evalReal_coe] using heq
    have hqd0 : q 0 = f (γ timeZero) := hqd 0
    have hqd1 : q 1 = f (γ timeOne) := hqd 1
    have hdD := WeakHessianCalculus.ae_deriv_le_of_dense_action hq hDa.1 hDa.2 d hd
      (by simpa only [hqd] using hDb)
    have hdE := WeakHessianCalculus.ae_deriv_le_of_dense_action hq hEa.1 hEa.2 d hd
      (by simpa only [hqd] using hEb)
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv q t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hq.integral_deriv_eq_sub, hqd0, hqd1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv q t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (Min.min (D (evalReal γ t)) (E (evalReal γ t))) * metricSpeed γ t := by
        apply lintegral_mono_ae
        filter_upwards [hdD, hdE] with t hdt het
        rcases le_total (D (evalReal γ t)) (E (evalReal γ t)) with h|h
        · simpa only [min_eq_left h, Real.enorm_eq_ofReal_abs] using hdt
        · simpa only [min_eq_right h, Real.enorm_eq_ofReal_abs] using het

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NormSqLintegralEnorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma norm_minimal_is_minimal {f D : Lp ℝ 2 m}
    (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖) :
    IsMinimalLocalWeakUpperGradient m f D := by
  refine ⟨hD, fun E hE => ?_⟩
  let M : X → ℝ := fun x => min (D x) (E x)
  have hM : IsLocalWeakUpperGradient m f M :=
    hD.min_measurable hE (Lp.memLp f).aestronglyMeasurable.aemeasurable
  have hMb : ∀ᵐ x ∂m, ‖M x‖ ≤ D x := by
    filter_upwards [hD.2.1, hE.2.1] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
    exact min_le_left _ _
  have hMp : MemLp M 2 m := (Lp.memLp D).mono' hM.1.aestronglyMeasurable hMb
  let M' : Lp ℝ 2 m := hMp.toLp M
  have hM' : IsLocalWeakUpperGradient m f M' :=
    hM.congr_ae Filter.EventuallyEq.rfl hMp.coeFn_toLp.symm
  have hInt : (∫⁻ x, ‖D x‖ₑ ^ 2 ∂m) ≤ ∫⁻ x, ‖M x‖ₑ ^ 2 ∂m := by
    rw [← norm_sq_eq_lintegral_enorm D]
    calc
      ENNReal.ofReal (‖D‖ ^ 2) ≤ ENNReal.ofReal (‖M'‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hmin M' hM') 2)
      _ = ∫⁻ x, ‖M' x‖ₑ ^ 2 ∂m := norm_sq_eq_lintegral_enorm M'
      _ = _ := lintegral_congr_ae (hMp.coeFn_toLp.fun_comp (fun r : ℝ => ‖r‖ₑ ^ 2))
  have hsmall : (∫⁻ x, ‖M x‖ₑ ^ 2 ∂m) ≠ ∞ := by
    rw [← eLpNorm_sq_eq_lintegral M hMp.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top hMp.eLpNorm_lt_top).ne
  have hle : (fun x => ‖M x‖ₑ ^ 2) ≤ᵐ[m] (fun x => ‖D x‖ₑ ^ 2) := by
    filter_upwards [hMb] with x hx
    apply pow_le_pow_left₀ (by positivity)
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
  have heq := ae_eq_of_ae_le_of_lintegral_le hle hsmall
    ((Lp.memLp D).aestronglyMeasurable.enorm.pow_const 2) hInt
  filter_upwards [heq, hD.2.1, hE.2.1] with x hx hdx hex
  have hreal := congrArg ENNReal.toReal hx
  simp only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
  have hMx : 0 ≤ M x := le_min hdx hex
  rw [abs_of_nonneg hMx, abs_of_nonneg hdx] at hreal
  have hequal : M x = D x := by nlinarith
  exact hequal ▸ min_le_right (D x) (E x)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_AeEndpointGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open MeasureTheory Set Filter

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [Nonempty X] {m : Measure X}

lemma IsLocalWeakUpperGradient.ae_endpoint_le_global {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) :
    ∀ᵐ γ ∂π, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : IsProbabilityMeasure π := hπ.1
  let o : X := Classical.arbitrary X
  let S (n : ℕ) : Set (Curve X) := Metric.closedBall (ContinuousMap.const Time o) n
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_closedBall
  have H (n : ℕ) : ∀ᵐ γ ∂π, γ ∈ S n →
      ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)| ≤
      ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal (D (evalReal γ t))*metricSpeed γ t := by
    apply (ae_restrict_iff' (hS n)).mp
    by_cases hz : π (S n) = 0
    · rw [Measure.restrict_eq_zero.mpr hz]
      simp
    let ρ := (π (S n))⁻¹ • π.restrict (S n)
    have hdom : ρ ≤ (π (S n))⁻¹ • π := by
      change (π (S n))⁻¹ • π.restrict (S n) ≤ (π (S n))⁻¹ • π
      gcongr
      exact Measure.restrict_le_self
    have hp : IsProbabilityMeasure ρ := by
      constructor
      simp only [ρ,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,
        ENNReal.inv_mul_cancel hz (measure_ne_top _ _)]
    have ht := hπ.of_plan_le_smul hp (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hz)) hdom
    have hb : BoundedTracks ρ := by
      refine ⟨o,(n:ℝ)+1,by positivity,?_⟩
      have ha : ∀ᵐ γ ∂ρ, γ ∈ S n := by
        exact Measure.ae_smul_measure (ae_restrict_mem (hS n)) _
      filter_upwards [ha] with γ hγ
      intro t
      have hdist := ContinuousMap.dist_apply_le_dist (f := γ) (g := ContinuousMap.const Time o) t
      exact (hdist.trans hγ).trans (by linarith)
    have HH := hD.ae_endpoint_le hf ht hb
    exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))).mp HH
  filter_upwards [ae_all_iff.mpr H] with γ hγ
  obtain ⟨n,hn⟩ := exists_nat_gt (dist γ (ContinuousMap.const Time o))
  exact hγ n hn.le

lemma IsLocalWeakUpperGradient.integrated_global {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) :
    (∫⁻ γ, ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)| ∂π) ≤
      ∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1,
        ENNReal.ofReal (D (evalReal γ t))*metricSpeed γ t ∂volume ∂π :=
  lintegral_mono_ae (hD.ae_endpoint_le_global hf hπ)
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_EndpointPairingBoundGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {m : Measure X}

lemma IsLocalWeakUpperGradient.endpoint_pairing_bound_global
    {f D : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (D : X → ℝ))
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, π.map (fun γ => γ t) ≤ (C:ℝ≥0∞) • m)
    {A : ℝ} (hA : 0 ≤ A)
    (ha : (∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1, (metricSpeed γ r)^2 ∂volume ∂π) ≤ ENNReal.ofReal A) :
    |(∫ x, f x ∂(π.map (fun γ => γ timeOne))) -
      (∫ x, f x ∂(π.map (fun γ => γ timeZero)))| ≤ Real.sqrt C * ‖D‖ * Real.sqrt A := by
  let : IsProbabilityMeasure π := hπ.1
  have hm (r : Time) : MemLp (f : X → ℝ) 2 (π.map (fun γ => γ r)) :=
    ((Lp.memLp f).smul_measure ENNReal.coe_ne_top).mono_measure (hC r)
  have hi (r : Time) : Integrable (fun γ : Curve X => f (γ r)) π :=
    ((hm r).comp_of_map (continuous_eval_const r).measurable.aemeasurable).integrable (by norm_num)
  have hweak := hf.integrated_global (Lp.aestronglyMeasurable f).aemeasurable hπ
  have haction := hπ.lintegral_abs_action_le hC (Lp.aestronglyMeasurable D)
  have hdpos : (∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1,
      ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r ∂volume ∂π) ≤
      ∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1,
      ENNReal.ofReal |D (evalReal γ r)| * metricSpeed γ r ∂volume ∂π := by
    apply lintegral_mono
    intro γ
    apply lintegral_mono
    intro r
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_abs_self _)) _
  have hb : ENNReal.ofReal |∫ γ, f (γ timeOne)-f (γ timeZero) ∂π| ≤
      ((C:ℝ≥0∞)^(1/(2:ℝ))*eLpNorm (D : X → ℝ) 2 m) * (ENNReal.ofReal A)^(1/(2:ℝ)) := by
    have H := enorm_integral_le_lintegral_enorm (μ := π) (fun γ : Curve X => f (γ timeOne)-f (γ timeZero))
    simp only [Real.enorm_eq_ofReal_abs] at H
    exact (H.trans (hweak.trans (hdpos.trans haction))).trans
      (by gcongr)
  rw [← Lp.enorm_def] at hb
  have hreal := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal hA, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hreal
  rw [integral_sub (hi timeOne) (hi timeZero)] at hreal
  rw [integral_map (continuous_eval_const timeOne).measurable.aemeasurable
      (hm timeOne).aestronglyMeasurable,
    integral_map (continuous_eval_const timeZero).measurable.aemeasurable
      (hm timeZero).aestronglyMeasurable]
  simpa only [toReal_enorm] using hreal

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergyCongrAe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheegerEnergy_le_liminf {f : X → ℝ} (hf : MemLp f 2 m)
    {fs : ℕ → X → ℝ}
    (hfs : ∀ n, GloballyLipschitz (fs n) ∧ MemLp (fs n) 2 m)
    (hc : Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 m) atTop (𝓝 0)) :
    cheegerEnergy m f ≤ liminf (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂m) atTop := by
  rw [cheegerEnergy, ite_eq_left hf]
  exact sInf_le ⟨fs, hfs, hc, rfl⟩

lemma cheegerEnergy_lt_approx {f : Lp ℝ 2 m} {a : ℝ≥0∞}
    (ha : cheegerEnergy m (f : X → ℝ) < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, GloballyLipschitz g ∧ ∃ hg : MemLp g 2 m,
      dist (hg.toLp g) f < ε ∧
      (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, (localSlope g x)^2 ∂m) < a := by
  rw [cheegerEnergy, ite_eq_left (Lp.memLp f), sInf_lt_iff] at ha
  obtain ⟨b, ⟨fs, hfs, hc, hb⟩, hba⟩ := ha
  have hconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
    (fun n => (hfs n).2) (f : X → ℝ) (Lp.memLp f)).mpr hc
  simp only [Lp.toLp_coeFn] at hconv
  have hdist : ∀ᶠ n in atTop, dist ((hfs n).2.toLp (fs n)) f < ε :=
    (tendsto_order.1 (hconv.dist tendsto_const_nhds)).2 ε (by simpa only [dist_self] using hε)
  rw [hb] at hba
  have H := frequently_lt_of_liminf_lt (h := hba)
  obtain ⟨n, hn, hd⟩ := (H.and_eventually hdist).exists
  exact ⟨fs n, (hfs n).1, (hfs n).2, hd, hn⟩

lemma cheegerEnergy_le_of_lip_approximations {f : Lp ℝ 2 m} {a : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : X → ℝ, GloballyLipschitz g ∧
      ∃ hg : MemLp g 2 m, dist (hg.toLp g) f < ε ∧
        (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, (localSlope g x)^2 ∂m) ≤ a) :
    cheegerEnergy m (f : X → ℝ) ≤ a := by
  choose g hg hm hd he using fun n : ℕ => h (1/((n:ℝ)+1)) (by positivity)
  have hconv : Tendsto (fun n => (hm n).toLp (g n)) atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hm
    (f : X → ℝ) (Lp.memLp f)).mp (by simpa only [Lp.toLp_coeFn] using hconv)
  exact (cheegerEnergy_le_liminf (Lp.memLp f) (fun n => ⟨hg n, hm n⟩) hc).trans
    (liminf_le_of_frequently_le (Eventually.of_forall he).frequently)

lemma lowerSemicontinuous_cheegerEnergy :
    LowerSemicontinuous (fun f : Lp ℝ 2 m => cheegerEnergy m (f : X → ℝ)) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro f
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  apply cheegerEnergy_le_of_lip_approximations
  intro ε hε
  have H := frequently_lt_of_liminf_lt (h := ha)
  obtain ⟨u, hu, hd⟩ := (H.and_eventually
    (Metric.ball_mem_nhds f (half_pos hε))).exists
  obtain ⟨g, hg, hm, hgu, hge⟩ := cheegerEnergy_lt_approx hu (half_pos hε)
  refine ⟨g, hg, hm, ?_, hge.le⟩
  calc
    dist (hm.toLp g) f ≤ dist (hm.toLp g) u + dist u f := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add hgu hd
    _ = ε := add_halves ε

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_JoinControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace WeakHessianTransport

lemma intervalIntegrable_joinControl_left {u v : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1) :
    IntervalIntegrable (joinControl u v) volume 0 (1/2) := by
  have H : IntervalIntegrable (fun r => 2*u (2*r)) volume 0 (1/2) := by
    simpa using (hu.comp_mul_left (c := 2)).const_mul 2
  apply H.congr
  intro r hr
  simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2), mem_Ioc] at hr
  simp only [joinControl, ite_eq_left hr.2]

lemma intervalIntegrable_joinControl_right {u v : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1) :
    IntervalIntegrable (joinControl u v) volume (1/2) 1 := by
  have H : IntervalIntegrable (fun r => 2*v (2*r-1)) volume (1/2) 1 := by
    convert ((hv.comp_sub_right 1).comp_mul_left (c := 2)).const_mul 2 using 1 <;> norm_num
  apply H.congr
  intro r hr
  simp only [uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1), mem_Ioc] at hr
  simp only [joinControl, ite_eq_right (not_le.mpr hr.1)]

lemma intervalIntegrable_joinControl {u v : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1) (hv : IntervalIntegrable v volume 0 1) :
    IntervalIntegrable (joinControl u v) volume 0 1 :=
  (intervalIntegrable_joinControl_left hu).trans (intervalIntegrable_joinControl_right hv)

lemma intervalIntegrable_joinControl_sq {u v : ℝ → ℝ}
    (hu : IntervalIntegrable (fun r => (u r)^2) volume 0 1)
    (hv : IntervalIntegrable (fun r => (v r)^2) volume 0 1) :
    IntervalIntegrable (fun r => (joinControl u v r)^2) volume 0 1 := by
  rw [joinControl_sq]
  exact (intervalIntegrable_joinControl hu hv).const_mul 2

lemma integral_joinControl_left (u v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ 1/2) :
    (∫ r in a..b, joinControl u v r) = ∫ r in (2*a)..(2*b), u r := by
  calc
    (∫ r in a..b, joinControl u v r) = ∫ r in a..b, 2*u (2*r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hab] at hr
      simp only [joinControl, ite_eq_left (hr.2.trans hb)]
    _ = ∫ r in (2*a)..(2*b), u r := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left u (by norm_num : (2:ℝ) ≠ 0)]
      simp

lemma integral_joinControl_right (u v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha : 1/2 ≤ a) :
    (∫ r in a..b, joinControl u v r) = ∫ r in (2*a-1)..(2*b-1), v r := by
  calc
    (∫ r in a..b, joinControl u v r) = ∫ r in a..b, 2*v (2*r-1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro r hr
      simp only [joinControl, ite_eq_right (not_le.mpr (ha.trans_lt hr.1))]
    _ = ∫ r in (2*a-1)..(2*b-1), v r := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_sub v (by norm_num : (2:ℝ) ≠ 0)]
      simp

lemma integral_joinControl {u v : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1) (hv : IntervalIntegrable v volume 0 1) :
    (∫ r in (0:ℝ)..1, joinControl u v r) = (∫ r in (0:ℝ)..1, u r)+(∫ r in (0:ℝ)..1, v r) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_joinControl_left hu)
    (intervalIntegrable_joinControl_right hv), integral_joinControl_left u v (by norm_num) le_rfl,
    integral_joinControl_right u v (by norm_num) le_rfl]
  norm_num

lemma integral_joinControl_sq {u v : ℝ → ℝ}
    (hu : IntervalIntegrable (fun r => (u r)^2) volume 0 1)
    (hv : IntervalIntegrable (fun r => (v r)^2) volume 0 1) :
    (∫ r in (0:ℝ)..1, (joinControl u v r)^2) =
      2*((∫ r in (0:ℝ)..1, (u r)^2)+(∫ r in (0:ℝ)..1, (v r)^2)) := by
  rw [joinControl_sq, intervalIntegral.integral_const_mul, integral_joinControl hu hv]

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ClampTimeVal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace WeakHessian
open WeakHessianTransport

variable {X : Type*} [MetricSpace X]

lemma hasControlBound_of_memLp {γ : Curve X} {a : ℝ → ℝ}
    (ha : MemLp a 2 timeMeasure)
    (hd : ∀ s t : Time, s ≤ t → dist (γ s) (γ t) ≤ ∫ r in (s:ℝ)..(t:ℝ), a r) :
    HasControlBound γ (Real.sqrt (∫ r in Icc (0:ℝ) 1, (a r)^2)) := by
  let u := ha.toLp a
  have hueq : u =ᵐ[timeMeasure] a := MemLp.coeFn_toLp ha
  have hn : ‖u‖^2 = ∫ r in Icc (0:ℝ) 1, (a r)^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hueq] with r hr
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hr]
  refine ⟨u, ?_, fun s t hst => ?_⟩
  · rw [← hn, Real.sqrt_sq (norm_nonneg u)]
  · rw [intervalFunctional_apply s t u hst]
    have heq : (∫ r in (s:ℝ)..(t:ℝ), u r) = ∫ r in (s:ℝ)..(t:ℝ), a r := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (show (s:ℝ) ≤ (t:ℝ) from hst)]
      exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.2.1 t.2.2)) hueq
    rw [heq]
    exact hd s t hst

lemma join_distance_integral {γ η : Curve X} (h : γ timeOne = η timeZero)
    {a b : ℝ → ℝ} (ha : IsSquareControl γ a) (hb : IsSquareControl η b) :
    ∀ s t : Time, s ≤ t → dist (joinCurve γ η h s) (joinCurve γ η h t) ≤
      ∫ r in (s:ℝ)..(t:ℝ), joinControl a b r := by
  have haI : IntervalIntegrable a volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (ha.2.1.integrable (by norm_num))
  have hbI : IntervalIntegrable b volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (hb.2.1.integrable (by norm_num))
  have hjI := intervalIntegrable_joinControl haI hbI
  have HL (s t : Time) (hst : s ≤ t) (ht : (t:ℝ) ≤ 1/2) :
      dist (joinCurve γ η h s) (joinCurve γ η h t) ≤ ∫ r in (s:ℝ)..(t:ℝ), joinControl a b r := by
    have hs : (s:ℝ) ≤ 1/2 := (show (s:ℝ) ≤ (t:ℝ) from hst).trans ht
    have hsc : 2*(s:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by have := s.2.1; linarith, by linarith⟩
    have htc : 2*(t:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by have := t.2.1; linarith, by linarith⟩
    rw [joinCurve_apply_left _ _ _ s hs, joinCurve_apply_left _ _ _ t ht,
      integral_joinControl_left _ _ hst ht]
    have H := ha.2.2.2 (clampTime (2*(s:ℝ))) (clampTime (2*(t:ℝ))) (by
      rw [clampTime_val_eq hsc, clampTime_val_eq htc]
      linarith [show (s:ℝ) ≤ (t:ℝ) from hst])
    simpa only [evalReal, clampTime_val_eq hsc, clampTime_val_eq htc] using H
  have HR (s t : Time) (hst : s ≤ t) (hs : 1/2 ≤ (s:ℝ)) :
      dist (joinCurve γ η h s) (joinCurve γ η h t) ≤ ∫ r in (s:ℝ)..(t:ℝ), joinControl a b r := by
    have ht : 1/2 ≤ (t:ℝ) := hs.trans (show (s:ℝ) ≤ (t:ℝ) from hst)
    have hsc : 2*(s:ℝ)-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith, by have := s.2.2; linarith⟩
    have htc : 2*(t:ℝ)-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith, by have := t.2.2; linarith⟩
    rw [joinCurve_apply_right _ _ _ s hs, joinCurve_apply_right _ _ _ t ht,
      integral_joinControl_right _ _ hst hs]
    have H := hb.2.2.2 (clampTime (2*(s:ℝ)-1)) (clampTime (2*(t:ℝ)-1)) (by
      rw [clampTime_val_eq hsc, clampTime_val_eq htc]
      linarith [show (s:ℝ) ≤ (t:ℝ) from hst])
    simpa only [evalReal, clampTime_val_eq hsc, clampTime_val_eq htc] using H
  intro s t hst
  by_cases ht : (t:ℝ) ≤ 1/2
  · exact HL s t hst ht
  by_cases hs : 1/2 ≤ (s:ℝ)
  · exact HR s t hst hs
  let m : Time := ⟨1/2, by norm_num, by norm_num⟩
  have hsm : s ≤ m := le_of_lt (lt_of_not_ge hs)
  have hmt : m ≤ t := le_of_lt (lt_of_not_ge ht)
  calc
    dist (joinCurve γ η h s) (joinCurve γ η h t) ≤
        dist (joinCurve γ η h s) (joinCurve γ η h m)+dist (joinCurve γ η h m) (joinCurve γ η h t) := dist_triangle _ _ _
    _ ≤ (∫ r in (s:ℝ)..(m:ℝ), joinControl a b r)+(∫ r in (m:ℝ)..(t:ℝ), joinControl a b r) :=
      add_le_add (HL s m hsm le_rfl) (HR m t hmt le_rfl)
    _ = _ := intervalIntegral.integral_add_adjacent_intervals
      (hjI.mono_set (uIcc_subset_uIcc (by simpa only [uIcc_of_le zero_le_one] using s.2)
        (by simpa only [uIcc_of_le zero_le_one] using m.2)))
      (hjI.mono_set (uIcc_subset_uIcc (by simpa only [uIcc_of_le zero_le_one] using m.2)
        (by simpa only [uIcc_of_le zero_le_one] using t.2)))

lemma hasControlBound_join {γ η : Curve X} (h : γ timeOne = η timeZero)
    {A B : ℝ} (hA : HasControlBound γ A) (hB : HasControlBound η B) :
    HasControlBound (joinCurve γ η h) (Real.sqrt (2*(A^2+B^2))) := by
  obtain ⟨a,ha,haA⟩ := hA.squareControl
  obtain ⟨b,hb,hbB⟩ := hB.squareControl
  have haI : IntervalIntegrable (fun r => (a r)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr ha.2.1.integrable_sq
  have hbI : IntervalIntegrable (fun r => (b r)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hb.2.1.integrable_sq
  have hj : MemLp (joinControl a b) 2 timeMeasure :=
    (memLp_two_iff_integrable_sq (measurable_joinControl ha.1 hb.1).aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
        (intervalIntegrable_joinControl_sq haI hbI))
  have H := hasControlBound_of_memLp hj (join_distance_integral h ha hb)
  obtain ⟨u,hu,hud⟩ := H
  refine ⟨u,hu.trans ?_,hud⟩
  apply Real.sqrt_le_sqrt
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_joinControl_sq haI hbI]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one] at haA hbB
  linarith

end WeakHessian

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_HalfTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

lemma kineticAction_join (γ η : Curve X) (h : γ timeOne = η timeZero) :
    kineticAction (joinCurve γ η h) ≤ 2*(kineticAction γ+kineticAction η) := by
  by_cases hγ : controlNorm γ = ∞
  · simp [kineticAction, hγ]
  by_cases hη : controlNorm η = ∞
  · simp [kineticAction, hη]
  let A := (controlNorm γ).toReal
  let B := (controlNorm η).toReal
  have hA : HasControlBound γ A := (controlNorm_le_iff ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hγ])
  have hB : HasControlBound η B := (controlNorm_le_iff ENNReal.toReal_nonneg).mp (by rw [ENNReal.ofReal_toReal hη])
  have H := controlNorm_le (hasControlBound_join h hA hB)
  have hnonneg : 0 ≤ 2*(A^2+B^2) := by positivity
  calc
    kineticAction (joinCurve γ η h) ≤ (ENNReal.ofReal (Real.sqrt (2*(A^2+B^2))))^2 :=
      pow_le_pow_left₀ bot_le H 2
    _ = ENNReal.ofReal (2*(A^2+B^2)) := by rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg]
    _ = 2*(kineticAction γ+kineticAction η) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg]
      simp only [ENNReal.ofReal_toReal hγ, ENNReal.ofReal_toReal hη, ENNReal.ofReal_ofNat, kineticAction]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DyadicTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
lemma halfTime_one_eq_rightTime_zero : halfTime timeOne = rightTime timeZero := by
  apply Subtype.ext; norm_num [halfTime,rightTime,timeOne,timeZero]

lemma exists_dyadicTime_dist_le (n : ℕ) (t : Time) :
    ∃ s ∈ dyadicTimes n, dist s t ≤ (1/2:ℝ)^n := by
  induction n generalizing t with
  | zero =>
    refine ⟨timeZero,zero_mem_dyadicTimes 0,?_⟩
    change |0-(t:ℝ)| ≤ (1/2:ℝ)^0
    simpa only [zero_sub, abs_neg, abs_of_nonneg t.2.1, pow_zero] using t.2.2
  | succ n hn =>
    by_cases ht : (t:ℝ) ≤ 1/2
    · let u : Time := ⟨2*(t:ℝ), by constructor <;> linarith [t.2.1]⟩
      have hu : halfTime u = t := by apply Subtype.ext; dsimp [halfTime,u]; ring
      obtain ⟨s,hs,hsd⟩ := hn u
      refine ⟨halfTime s,Or.inl ⟨s,hs,rfl⟩,?_⟩
      rw [← hu,dist_halfTime,pow_succ]
      linarith
    · let u : Time := ⟨2*(t:ℝ)-1, by constructor <;> linarith [t.2.2]⟩
      have hu : rightTime u = t := by apply Subtype.ext; dsimp [rightTime,u]; ring
      obtain ⟨s,hs,hsd⟩ := hn u
      refine ⟨rightTime s,Or.inr ⟨s,hs,rfl⟩,?_⟩
      rw [← hu,dist_rightTime,pow_succ]
      linarith

lemma dense_dyadicTimes : Dense (⋃ n, dyadicTimes n) := by
  intro t
  rw [Metric.mem_closure_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  obtain ⟨s,hs,hsd⟩ := exists_dyadicTime_dist_le n t
  exact ⟨s,mem_iUnion.mpr ⟨n,hs⟩,by simpa only [dist_comm] using hsd.trans_lt hn⟩

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_DynamicActionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]

omit [CompactSpace X] [BorelSpace X] [Nonempty X] in
lemma DynamicActionBound.half {μ : Time → Measure X} {C : ℝ}
    (h : DynamicActionBound μ C) : DynamicActionBound (μ ∘ halfTime) (C/4) := by
  intro s t
  obtain ⟨π,hπ,h0,h1,hb⟩ := h (halfTime s) (halfTime t)
  refine ⟨π,hπ,h0,h1,?_⟩
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  rw [dist_halfTime]
  congr 1
  ring

omit [CompactSpace X] [BorelSpace X] [Nonempty X] in
lemma DynamicActionBound.right {μ : Time → Measure X} {C : ℝ}
    (h : DynamicActionBound μ C) : DynamicActionBound (μ ∘ rightTime) (C/4) := by
  intro s t
  obtain ⟨π,hπ,h0,h1,hb⟩ := h (rightTime s) (rightTime t)
  refine ⟨π,hπ,h0,h1,?_⟩
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  rw [dist_rightTime]
  congr 1
  ring

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ContinuousTimeMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma continuous_time_marginals (π : ProbabilityMeasure (Curve X)) :
    Continuous (fun t : Time => π.map (continuous_eval_const t).aemeasurable) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have H : Continuous (fun t : Time => ∫ γ : Curve X, f (γ t) ∂(π:Measure (Curve X))) := by
    apply continuous_of_dominated
      (bound := fun _ : Curve X => ‖f‖)
    · intro t
      exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
    · intro t
      exact ae_of_all _ (fun γ => f.norm_coe_le_norm (γ t))
    · exact integrable_const _
    · exact ae_of_all _ (fun γ => f.continuous.comp γ.continuous)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact integral_map (continuous_eval_const t).measurable.aemeasurable f.continuous.aestronglyMeasurable

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_JoinPlanPolish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set MeasureTheory Filter
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
lemma exists_join_plan_polish [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] (μ ν : Measure (Curve X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hpush : μ.map (fun γ => γ timeOne) = ν.map (fun γ => γ timeZero)) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ t : Time, π.map (fun γ => γ (halfTime t)) = μ.map (fun γ => γ t)) ∧
      (∀ t : Time, π.map (fun γ => γ (rightTime t)) = ν.map (fun γ => γ t)) ∧
      (∫⁻ γ, kineticAction γ ∂π) ≤ 2*((∫⁻ γ, kineticAction γ ∂μ)+(∫⁻ γ, kineticAction γ ∂ν)) := by
  let : Nonempty (Curve X) := ⟨ContinuousMap.const Time (Classical.arbitrary X)⟩
  let E := {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero}
  have hE : MeasurableSet E := isClosed_joinable.measurableSet
  obtain ⟨q,hqp,hq0,hq1,hqE⟩ := WeakHessianTransport.exists_fiber_gluing_supported μ ν
    (fun γ => γ timeOne) (fun γ => γ timeZero) (continuous_eval_const _).measurable
    (continuous_eval_const _).measurable hpush
  let := hqp
  let qs : Measure (Joinable X) := q.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : Joinable X → Curve X × Curve X) :=
    MeasurableEmbedding.subtype_coe hE
  have hsupp : ∀ᵐ p ∂q, p ∈ range (Subtype.val : Joinable X → Curve X×Curve X) := by
    simpa only [Subtype.range_coe_subtype, mem_ofPred_eq] using hqE
  let : IsProbabilityMeasure qs := hemb.isProbabilityMeasure_comap hsupp
  have hqs : qs.map Subtype.val = q := by
    rw [hemb.map_comap, Measure.restrict_eq_self_of_ae_mem hsupp]
  have hqsfst : qs.map (fun p => p.1.1) = μ := by
    rw [← hq0, ← hqs, Measure.map_map measurable_fst hemb.measurable]
    rfl
  have hqssnd : qs.map (fun p => p.1.2) = ν := by
    rw [← hq1, ← hqs, Measure.map_map measurable_snd hemb.measurable]
    rfl
  have hfstm : Measurable (fun p : Joinable X => p.1.1) := measurable_fst.comp measurable_subtype_coe
  have hsndm : Measurable (fun p : Joinable X => p.1.2) := measurable_snd.comp measurable_subtype_coe
  let π := qs.map joinMap
  have hjm : Measurable (joinMap (X := X)) := lipschitz_joinMap.continuous.measurable
  let : IsProbabilityMeasure π := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  refine ⟨π,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_,?_⟩
  · intro t
    change (qs.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hqsfst,
      Measure.map_map (g := fun γ : Curve X => γ t) (continuous_eval_const t).measurable hfstm]
    congr 1
    funext p
    exact joinCurve_halfTime _ _ _ t
  · intro t
    change (qs.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hqssnd,
      Measure.map_map (g := fun γ : Curve X => γ t) (continuous_eval_const t).measurable hsndm]
    congr 1
    funext p
    exact joinCurve_rightTime _ _ _ t
  · have ha := (lowerSemicontinuous_kineticAction (X := X)).measurable
    change (∫⁻ γ, kineticAction γ ∂qs.map joinMap) ≤ _
    rw [lintegral_map ha hjm]
    calc
      (∫⁻ p, kineticAction (joinMap p) ∂qs) ≤
          ∫⁻ p, 2*(kineticAction p.1.1+kineticAction p.1.2) ∂qs :=
        lintegral_mono fun p => kineticAction_join _ _ p.2
      _ = 2*((∫⁻ p, kineticAction p.1.1 ∂qs)+(∫⁻ p, kineticAction p.1.2 ∂qs)) := by
        have hsum : Measurable (fun p : Joinable X => kineticAction p.1.1+kineticAction p.1.2) :=
          (ha.comp hfstm).add (ha.comp hsndm)
        rw [lintegral_const_mul (μ := qs) 2 hsum]
        exact congrArg (fun v : ℝ≥0∞ => 2*v) (lintegral_add_aux (ha.comp hfstm) (ha.comp hsndm))
      _ = _ := by
        rw [← lintegral_map (μ := qs) ha hfstm, hqsfst,
          ← lintegral_map (μ := qs) ha hsndm, hqssnd]

end WeakHessian

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]

lemma exists_grid_plan_polish (n : ℕ) (μ : Time → Measure X) {C : ℝ} (hC : 0 ≤ C)
    (h : DynamicActionBound μ C) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ t ∈ dyadicTimes n, π.map (fun γ => γ t) = μ t) ∧
      (∫⁻ γ, kineticAction γ ∂π) ≤ ENNReal.ofReal C := by
  induction n generalizing μ C with
  | zero =>
    obtain ⟨π,hπ,h0,h1,hb⟩ := h timeZero timeOne
    refine ⟨π,hπ,?_,?_⟩
    · intro t ht
      rcases ht with rfl | ht
      · exact h0
      · have he : t = timeOne := ht
        simpa only [he] using h1
    · simpa only [Subtype.dist_eq, timeZero, timeOne, Real.dist_eq, zero_sub,
        abs_neg, abs_one, one_pow, mul_one] using hb
  | succ n ih =>
    obtain ⟨πL,hL,hLm,hLA⟩ := ih (μ ∘ halfTime) (div_nonneg hC (by norm_num)) h.half
    obtain ⟨πR,hR,hRm,hRA⟩ := ih (μ ∘ rightTime) (div_nonneg hC (by norm_num)) h.right
    let := hL
    let := hR
    have hmatch : πL.map (fun γ => γ timeOne) = πR.map (fun γ => γ timeZero) := by
      rw [hLm _ (one_mem_dyadicTimes n),hRm _ (zero_mem_dyadicTimes n)]
      simp only [Function.comp_apply,halfTime_one_eq_rightTime_zero]
    obtain ⟨π,hπ,hπL,hπR,hπA⟩ := exists_join_plan_polish πL πR hmatch
    refine ⟨π,hπ,?_,?_⟩
    · intro t ht
      rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
      · rw [hπL,hLm _ hs]; rfl
      · rw [hπR,hRm _ hs]; rfl
    · calc
        (∫⁻ γ, kineticAction γ ∂π) ≤ 2*((∫⁻ γ, kineticAction γ ∂πL)+(∫⁻ γ, kineticAction γ ∂πR)) := hπA
        _ ≤ 2*(ENNReal.ofReal (C/4)+ENNReal.ofReal (C/4)) := mul_le_mul_right (add_le_add hLA hRA) 2
        _ = ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_add (div_nonneg hC (by norm_num)) (div_nonneg hC (by norm_num)),
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          ring

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SuperpositionProper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set MeasureTheory Filter
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_superposition_proper [ProperSpace X] [TopologicalSpace.SeparableSpace X] [Nonempty X]
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ) {C : ℝ} (hC : 0 ≤ C)
    (h : DynamicActionBound (fun t => (μ t : Measure X)) C) :
    ∃ π : ProbabilityMeasure (Curve X),
      (∀ t : Time, (π:Measure (Curve X)).map (fun γ => γ t) = (μ t : Measure X)) ∧
      (∫⁻ γ, kineticAction γ ∂(π:Measure (Curve X))) ≤ ENNReal.ofReal C ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsAC2 γ) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂(π:Measure (Curve X))) ≤ ENNReal.ofReal C := by
  have hex := fun n => exists_grid_plan_polish n (fun t => (μ t : Measure X)) hC h
  choose πs hπs hgrid haction using hex
  let qs : ℕ → ProbabilityMeasure (Curve X) := fun n => ⟨πs n,hπs n⟩
  have ht : IsTightMeasureSet {((qs n:Measure (Curve X)).map (fun γ => γ timeZero)) | n : ℕ} := by
    apply (isTightMeasureSet_singleton (μ := (μ timeZero : Measure X))).subset
    rintro ν ⟨n,rfl⟩
    exact hgrid n timeZero (zero_mem_dyadicTimes n)
  obtain ⟨π,φ,hφ,hlim,hA,hAC,hS⟩ := exists_action_limit_initial qs ENNReal.ofReal_lt_top haction ht
  have hdense : EqOn (fun t : Time => π.map (continuous_eval_const t).aemeasurable)
      μ (⋃ n, dyadicTimes n) := by
    intro t ht
    obtain ⟨n,hn⟩ := mem_iUnion.mp ht
    have hevent : ∀ᶠ j in atTop,
        (qs (φ j)).map (continuous_eval_const t).aemeasurable = μ t := by
      filter_upwards [eventually_ge_atTop n] with j hj
      apply ProbabilityMeasure.toMeasure_injective
      exact hgrid (φ j) t (monotone_dyadicTimes (hj.trans (hφ.id_le j)) hn)
    have hlimt := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (qs ∘ φ) π hlim (continuous_eval_const t)
    exact tendsto_nhds_unique hlimt (tendsto_const_nhds.congr' (hevent.mono fun j hj => hj.symm))
  have heq := Continuous.ext_on dense_dyadicTimes (continuous_time_marginals π) hμ hdense
  refine ⟨π,?_,hA,hAC,hS⟩
  intro t
  exact congrArg ProbabilityMeasure.toMeasure (congrFun heq t)

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerEnergySlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma cheegerEnergy_le_slope {f : X → ℝ} (hf : GloballyLipschitz f) (hf2 : MemLp f 2 m) :
    cheegerEnergy m f ≤ (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, localSlope f x^2 ∂m := by
  have H := cheegerEnergy_le_liminf hf2 (fs := fun (_ : ℕ) => f) (fun _ => ⟨hf,hf2⟩)
    (by simp)
  simpa only [liminf_const] using H

lemma slopeGraph_energy_le {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2SlopeGraph m) :
    cheegerEnergy m (p.fst : X → ℝ) ≤ ENNReal.ofReal (‖p.snd‖^2/2) := by
  obtain ⟨f,hf,hf2,hpf,hmajor⟩ := hp
  have hm : MemLp (fun x => (localSlope f x).toReal) 2 m :=
    (Lp.memLp p.snd).mono'
      (measurable_localSlope hf.choose_spec.continuous).ennreal_toReal.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hmajor)
  have hn : ‖hm.toLp (fun x => (localSlope f x).toReal)‖ ≤ ‖p.snd‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hmajor,hm.coeFn_toLp] with x hx hy
    rw [hy,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,Real.norm_eq_abs]
    exact hx.trans (le_abs_self _)
  calc
    cheegerEnergy m (p.fst : X → ℝ) = cheegerEnergy m f :=
      cheegerEnergy_congr_ae (hpf ▸ hf2.coeFn_toLp)
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, localSlope f x^2 ∂m := cheegerEnergy_le_slope hf hf2
    _ = ENNReal.ofReal (‖hm.toLp (fun x => (localSlope f x).toReal)‖^2/2) :=
      half_lintegral_localSlope_eq hf.choose_spec hm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg p.snd,norm_nonneg (hm.toLp (fun x => (localSlope f x).toReal))])

lemma relaxedGraph_energy_le {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2RelaxedGraph m) :
    cheegerEnergy m (p.fst : X → ℝ) ≤ ENNReal.ofReal (‖p.snd‖^2/2) := by
  have hcl : IsClosed {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) |
      cheegerEnergy m (p.fst : X → ℝ) ≤ ENNReal.ofReal (‖p.snd‖^2/2)} := by
    exact (lowerSemicontinuous_iff_isClosed_epigraph.mp lowerSemicontinuous_cheegerEnergy).preimage
      ((WithLp.continuous_fst 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).prodMk
        (ENNReal.continuous_ofReal.comp
          (((WithLp.continuous_snd 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).norm.pow 2).div_const 2)))
  exact (closure_minimal (fun _ => slopeGraph_energy_le) hcl) hp

lemma exists_relaxedGradient_of_cheeger_lt {f : Lp ℝ 2 m} {B : ℝ} (hB : 0 ≤ B)
    (he : cheegerEnergy m (f : X → ℝ) < ENNReal.ofReal (B^2/2)) :
    ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧ ‖D‖ ≤ B := by
  have happrox (ε : ℝ) (hε : 0 < ε) := cheegerEnergy_lt_approx he hε
  choose fs hLip hfs hdist hEn using fun n : ℕ => happrox (1/((n:ℝ)+1)) (by positivity)
  have hsfin (n : ℕ) : (∫⁻ x, localSlope (fs n) x^2 ∂m) < ∞ := by
    by_contra hh
    have ht := top_le_iff.mp (not_lt.mp hh)
    have H := hEn n
    norm_num [ht] at H
  let hDs (n : ℕ) := memLp_localSlope_of_lintegral_lt_top (hLip n).choose_spec (hsfin n)
  let fn (n : ℕ) := (hfs n).toLp (fs n)
  let Dn (n : ℕ) := (hDs n).toLp (fun x => (localSlope (fs n) x).toReal)
  apply WeakHessianFunctional.exists_snd_of_tendsto_fst_of_bounded
    isClosed_l2RelaxedGraph convex_l2RelaxedGraph (u := fun n => WithLp.toLp 2 (fn n,Dn n))
  · intro n
    apply subset_closure
    exact ⟨fs n,hLip n,hfs n,rfl,by
      filter_upwards [(hDs n).coeFn_toLp] with x hx
      exact hx.ge⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    have H := hEn n
    rw [half_lintegral_localSlope_eq (hLip n).choose_spec (hDs n)] at H
    have H' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp H
    change ‖Dn n‖^2/2 < B^2/2 at H'
    change ‖Dn n‖ ≤ B
    nlinarith [norm_nonneg (Dn n)]

lemma exists_relaxedGradient_energy_eq {f : Lp ℝ 2 m}
    (he : cheegerEnergy m (f : X → ℝ) < ∞) :
    ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧
      (∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖) ∧
      cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
  let a := (cheegerEnergy m (f : X → ℝ)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have haB : a < (a+2)^2/2 := by nlinarith [sq_nonneg a]
  have hE : cheegerEnergy m (f : X → ℝ) < ENNReal.ofReal ((a+2)^2/2) := by
    rw [← ENNReal.ofReal_toReal he.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr haB
  obtain ⟨D₀,hD₀,_⟩ := exists_relaxedGradient_of_cheeger_lt (by linarith : 0 ≤ a+2) hE
  obtain ⟨D,hD,hmin⟩ := exists_norm_minimal_relaxedGradient (f := f) ⟨D₀,hD₀⟩
  refine ⟨D,hD,hmin,le_antisymm (relaxedGraph_energy_le (p := WithLp.toLp 2 (f,D)) hD) ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrt : r = ∞
  · rw [hrt]; exact le_top
  let B : ℝ := Real.sqrt (2*r.toReal)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBs : B^2/2 = r.toReal := by
    dsimp only [B]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2*r.toReal)]
    ring
  have hEB : cheegerEnergy m (f : X → ℝ) < ENNReal.ofReal (B^2/2) := by
    rwa [hBs,ENNReal.ofReal_toReal hrt]
  obtain ⟨E,hE,hEn⟩ := exists_relaxedGradient_of_cheeger_lt hB hEB
  have hDE := (hmin E hE).trans hEn
  calc
    ENNReal.ofReal (‖D‖^2/2) ≤ ENNReal.ofReal (B^2/2) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg D])
    _ = r := by rw [hBs,ENNReal.ofReal_toReal hrt]
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Young
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma RelaxedProx.young {u v D q : Lp ℝ 2 m} {t α c : ℝ} (h : RelaxedProx u t v D)
    (hq : cheegerEnergy m (q : X → ℝ) < ∞) (hα : 0 < α) :
    -α*(cheegerEnergy m (q : X → ℝ)).toReal + ⟪q,c • (u-v)⟫_ℝ ≤
      c^2/α*(t^2*‖D‖)^2/2 := by
  obtain ⟨E,hE,_hmin,he⟩ := exists_relaxedGradient_energy_eq hq
  rw [he,ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖E‖^2/2),real_inner_smul_right,
    real_inner_comm (u-v) q]
  have HB : c*⟪u-v,q⟫_ℝ ≤ |c| * (t^2*‖D‖)*‖E‖ := by
    calc
      _ ≤ |c*⟪u-v,q⟫_ℝ| := le_abs_self _
      _ = |c| * |⟪u-v,q⟫_ℝ| := abs_mul _ _
      _ ≤ |c| * (t^2*‖D‖*‖E‖) := mul_le_mul_of_nonneg_left (h.dual hE) (abs_nonneg c)
      _ = _ := by ring
  have HP := sq_nonneg (|c| * (t^2*‖D‖)-α*‖E‖)
  have HE : (|c| * (t^2*‖D‖))^2 = c^2*(t^2*‖D‖)^2 := by rw [mul_pow,sq_abs]
  have HC := mul_le_mul_of_nonneg_left HB hα.le
  have hr : c^2/α*(t^2*‖D‖)^2/2 = (c^2*(t^2*‖D‖)^2)/(2*α) := by ring
  rw [hr]
  apply (le_div_iff₀ (by positivity : 0 < 2*α)).mpr
  nlinarith
end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_HopfObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X]

def hopfLax (f : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sInf (Set.range (hopfObjective f t x))

lemma hopfObjective_bddBelow {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) :
    BddBelow (Set.range (hopfObjective f t x)) := by
  refine ⟨B, ?_⟩
  rintro r ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

lemma hopfLax_le_objective {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x y : X) :
    hopfLax f t x ≤ hopfObjective f t x y :=
  csInf_le (hopfObjective_bddBelow hf ht x) (mem_range_self y)

lemma hopfLax_le_self {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) : hopfLax f t x ≤ f x := by
  simpa only [hopfObjective, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    using hopfLax_le_objective hf ht x x

lemma lower_le_hopfLax {f : X → ℝ} {B t : ℝ}
    (hf : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) : B ≤ hopfLax f t x := by
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  exact (hf y).trans (le_add_of_nonneg_right (by positivity))

lemma continuous_hopfObjective {f : X → ℝ} (hf : Continuous f) (t : ℝ) (x : X) :
    Continuous (hopfObjective f t x) := by
  unfold hopfObjective
  fun_prop

lemma hopfLax_antitone_time {f : X → ℝ} {B s t : ℝ}
    (hf : ∀ y, B ≤ f y) (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f t x ≤ hopfLax f s x := by
  apply le_csInf ⟨hopfObjective f s x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  apply (hopfLax_le_objective hf (hs.trans_le hst) x y).trans
  change f y + dist x y ^ 2 / (2*t) ≤ f y + dist x y ^ 2 / (2*s)
  gcongr

lemma exists_hopf_minimizer [ProperSpace X] {f : X → ℝ} {B t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (ht : 0 < t) (x : X) :
    ∃ y : X, hopfObjective f t x y = hopfLax f t x := by
  let R := Real.sqrt (2*t*(f x-B+1))
  have hnon : 0 ≤ 2*t*(f x-B+1) := by nlinarith [hlower x]
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 2*t*(f x-B+1) := Real.sq_sqrt hnon
  obtain ⟨y,hy,hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    ⟨x, by simpa using hR⟩ (continuous_hopfObjective hf t x).continuousOn
  have hyall : ∀ z : X, hopfObjective f t x y ≤ hopfObjective f t x z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall x R
    · exact hmin hz
    · have hdist : R < dist x z := by
        simpa only [Metric.mem_closedBall, not_le, dist_comm] using hz
      have hsq : R^2 < dist x z ^ 2 := sq_lt_sq₀ hR (dist_nonneg) |>.mpr hdist
      have hcost : f x < hopfObjective f t x z := by
        dsimp [hopfObjective]
        have hdiv : f x-B+1 < dist x z^2/(2*t) := by
          apply (lt_div_iff₀ (by positivity : 0 < 2*t)).mpr
          nlinarith
        linarith [hlower z]
      have hym : hopfObjective f t x y ≤ f x := by
        simpa only [hopfObjective, dist_self, zero_pow (by decide : 2 ≠ 0), zero_div,
          add_zero] using (show hopfObjective f t x y ≤ hopfObjective f t x x from
            hmin (show x ∈ Metric.closedBall x R by simpa using hR))
      exact hym.trans hcost.le
  refine ⟨y, le_antisymm ?_ (hopfLax_le_objective hlower ht x y)⟩
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨z,rfl⟩
  exact hyall z

lemma hopf_minimizer_distance_sq {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) :
    dist x y ^ 2 ≤ 2*t*(f x-B) := by
  have H := hopfLax_le_self hlower ht x
  rw [← hy] at H
  have hdiv : dist x y^2/(2*t) ≤ f x-B := by
    dsimp [hopfObjective] at H
    linarith [hlower y]
  have H' := (div_le_iff₀ (by positivity : 0 < 2*t)).mp hdiv
  nlinarith

lemma hopf_spatial_increment {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) (z : X) :
    hopfLax f t z - hopfLax f t x ≤
      dist x y / t * dist z x + dist z x ^ 2 / (2*t) := by
  have H := hopfLax_le_objective hlower ht z y
  rw [← hy]
  have hd := dist_triangle z x y
  have hs : dist z y ^ 2 ≤ (dist z x + dist x y) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr hd
  have hcost : dist z y^2/(2*t) - dist x y^2/(2*t) ≤
      dist x y / t * dist z x + dist z x^2/(2*t) := by
    rw [div_sub_div_same]
    have heq : dist x y / t * dist z x + dist z x ^ 2 / (2*t) =
        (2 * dist x y * dist z x + dist z x ^ 2) / (2*t) := by
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  dsimp [hopfObjective] at *
  linarith

lemma hopf_minimizer_distance_le {f : X → ℝ} {B U t R : ℝ}
    (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U) (ht : 0 < t)
    (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) : dist x y ≤ R := by
  apply (sq_le_sq₀ dist_nonneg hR).mp
  exact (hopf_minimizer_distance_sq hlower ht hy).trans
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right (hupper x) B) (by positivity)).trans hR2)

lemma hopf_spatial_abs_increment [ProperSpace X] {f : X → ℝ} {B U t R : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (ht : 0 < t) (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) (x z : X) :
    |hopfLax f t z - hopfLax f t x| ≤ R/t * dist z x + dist z x^2/(2*t) := by
  obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hlower ht x
  obtain ⟨w,hw⟩ := exists_hopf_minimizer hf hlower ht z
  have hyR := hopf_minimizer_distance_le hlower hupper ht hR hR2 hy
  have hwR := hopf_minimizer_distance_le hlower hupper ht hR hR2 hw
  have H := hopf_spatial_increment hlower ht hy z
  have H' := hopf_spatial_increment hlower ht hw x
  have I : dist x y / t * dist z x ≤ R/t * dist z x := by gcongr
  have I' : dist z w / t * dist z x ≤ R/t * dist z x := by gcongr
  rw [dist_comm x z] at H'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma hopfLax_lipschitz_radius [ProperSpace X] {f : X → ℝ} {B U t R : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (hR : 0 ≤ R) (hR2 : 2*t*(U-B) ≤ R^2) :
    LipschitzWith ⟨R/t + 1/(2*t) + (U-B), by positivity⟩ (hopfLax f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z x
  change |hopfLax f t z - hopfLax f t x| ≤ (R/t+1/(2*t)+(U-B))*dist z x
  by_cases hd : dist z x ≤ 1
  · have H := hopf_spatial_abs_increment hf hlower hupper ht hR hR2 x z
    have hs : dist z x^2 ≤ dist z x := by nlinarith [dist_nonneg (x := z) (y := x)]
    have I := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 2*t)
    have J : 0 ≤ (U-B)*dist z x := by positivity
    simp only [div_eq_mul_inv, one_mul] at H I ⊢
    nlinarith
  · have hzlo := lower_le_hopfLax hlower ht z
    have hxlo := lower_le_hopfLax hlower ht x
    have hzup := (hopfLax_le_self hlower ht z).trans (hupper z)
    have hxup := (hopfLax_le_self hlower ht x).trans (hupper x)
    have H : |hopfLax f t z-hopfLax f t x| ≤ U-B := abs_le.mpr ⟨by linarith, by linarith⟩
    have I : U-B ≤ (U-B)*dist z x := by nlinarith
    have J : 0 ≤ (R/t+1/(2*t))*dist z x := by positivity
    nlinarith

lemma hopfLax_continuous [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) : Continuous (hopfLax f t) := by
  apply (hopfLax_lipschitz_radius hf hlower hupper hBU ht (Real.sqrt_nonneg (2*t*(U-B))) ?_).continuous
  exact (Real.sq_sqrt (by positivity)).ge

lemma hopf_time_increment {f : X → ℝ} {B s t : ℝ}
    (hlower : ∀ y, B ≤ f y) (hs : 0 < s) (ht : 0 < t) {x y : X}
    (hy : hopfObjective f t x y = hopfLax f t x) :
    hopfLax f s x - hopfLax f t x ≤ dist x y^2*(t-s)/(2*s*t) := by
  have H := hopfLax_le_objective hlower hs x y
  rw [← hy]
  have heq : dist x y^2/(2*s) - dist x y^2/(2*t) = dist x y^2*(t-s)/(2*s*t) := by
    field_simp
  dsimp [hopfObjective] at *
  linarith

lemma hopf_time_increment_bound [ProperSpace X] {f : X → ℝ} {B U s t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hs : 0 < s) (hst : s ≤ t) (x : X) :
    hopfLax f s x - hopfLax f t x ≤ (U-B)*(t-s)/s := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hlower ht x
  apply (hopf_time_increment hlower hs ht hy).trans
  have H : dist x y^2 ≤ 2*t*(U-B) :=
    (hopf_minimizer_distance_sq hlower ht hy).trans (by gcongr; exact hupper x)
  calc
    dist x y^2*(t-s)/(2*s*t) ≤ (2*t*(U-B))*(t-s)/(2*s*t) := by gcongr
    _ = (U-B)*(t-s)/s := by field_simp

lemma hopf_time_abs_bound [ProperSpace X] {f : X → ℝ} {B U a s t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ha : 0 < a) (hs : a ≤ s) (ht : a ≤ t) (x : X) :
    |hopfLax f s x - hopfLax f t x| ≤ (U-B)/a * |s-t| := by
  wlog hst : s ≤ t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have hs0 := ha.trans_le hs
  have ht0 := ha.trans_le ht
  rw [abs_of_nonneg (sub_nonneg.mpr (hopfLax_antitone_time hlower hs0 hst x)),
    abs_of_nonpos (sub_nonpos.mpr hst)]
  have H := hopf_time_increment_bound hf hlower hupper hs0 hst x
  calc
    hopfLax f s x - hopfLax f t x ≤ (U-B)*(t-s)/s := H
    _ ≤ (U-B)*(t-s)/a := by gcongr
    _ = (U-B)/a * -(s-t) := by ring

lemma hopfLax_ge_lipschitz {f : X → ℝ} {L : ℝ≥0} {t : ℝ}
    (hf : LipschitzWith L f) (ht : 0 < t) (x : X) :
    f x - t*(L:ℝ)^2/2 ≤ hopfLax f t x := by
  apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
  rintro r ⟨y,rfl⟩
  have H := hf.dist_le_mul x y
  rw [Real.dist_eq] at H
  have H' := (abs_le.mp H).2
  change f x - t*(L:ℝ)^2/2 ≤ f y + dist x y^2/(2*t)
  have Hsq := sq_nonneg (dist x y - t*(L:ℝ))
  have Hdiv : (L:ℝ)*dist x y - t*(L:ℝ)^2/2 ≤ dist x y^2/(2*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith
  linarith

def IsFarthestHopfMinimizer (f : X → ℝ) (t : ℝ) (x y : X) : Prop :=
  hopfObjective f t x y = hopfLax f t x ∧
  ∀ z, hopfObjective f t x z = hopfLax f t x → dist x z ≤ dist x y

lemma hopf_minimizers_compact [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) :
    IsCompact {y | hopfObjective f t x y = hopfLax f t x} := by
  let R := Real.sqrt (2*t*(U-B))
  apply (isCompact_closedBall x R).of_isClosed_subset
    (isClosed_eq (continuous_hopfObjective hf t x) continuous_const)
  intro y hy
  rw [Metric.mem_closedBall, dist_comm]
  exact hopf_minimizer_distance_le hlower hupper ht (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)).ge hy

lemma exists_farthest_hopf_minimizer [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (x : X) : ∃ y, IsFarthestHopfMinimizer f t x y := by
  obtain ⟨y,hy,hmax⟩ := (hopf_minimizers_compact hf hlower hupper hBU ht x).exists_isMaxOn
    (exists_hopf_minimizer hf hlower ht x) (continuous_const.dist continuous_id).continuousOn
  exact ⟨y,hy, fun z hz => hmax hz⟩

lemma eventually_hopf_minimizer_distance_lt [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) {x y : X} (hy : IsFarthestHopfMinimizer f t x y)
    {r : ℝ} (hr : dist x y < r) :
    ∀ᶠ z in 𝓝 x, ∀ w, hopfObjective f t z w = hopfLax f t z → dist z w < r := by
  let R := Real.sqrt (2*t*(U-B))
  let C := Metric.closedBall x (R+1)
  let : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall x (R+1))
  let S : Set (X × C) := {p | hopfObjective f t p.1 p.2 = hopfLax f t p.1 ∧ r ≤ dist p.1 p.2}
  have hobj : Continuous (fun p : X × C => hopfObjective f t p.1 p.2) := by
    dsimp [hopfObjective]
    fun_prop
  have hdist : Continuous (fun p : X × C => dist p.1 p.2) := by fun_prop
  have hS : IsClosed S := (isClosed_eq hobj
    ((hopfLax_continuous hf hlower hupper hBU ht).comp continuous_fst)).inter
      (isClosed_le continuous_const hdist)
  have hclosed : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  have hx : x ∉ Prod.fst '' S := by
    rintro ⟨⟨z,w⟩,⟨hmin,hd⟩,hpair⟩
    dsimp at hpair
    subst z
    exact (not_le_of_gt (lt_of_le_of_lt (hy.2 w hmin) hr)) hd
  have hne : ∀ᶠ z in 𝓝 x, z ∉ Prod.fst '' S := hclosed.isOpen_compl.mem_nhds hx
  have hball : ∀ᶠ z in 𝓝 x, dist z x < 1 := Metric.ball_mem_nhds x (by norm_num)
  filter_upwards [hne, hball] with z hz hzx
  intro w hw
  have hwR : dist z w ≤ R := hopf_minimizer_distance_le hlower hupper ht
    (Real.sqrt_nonneg _) (Real.sq_sqrt (by positivity)).ge hw
  have hwC : w ∈ C := by
    change dist w x ≤ R+1
    calc
      dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
      _ ≤ R+1 := by rw [dist_comm w z]; linarith
  by_contra hrw
  apply hz
  exact ⟨(z, ⟨w, hwC⟩), ⟨hw, le_of_not_gt hrw⟩, rfl⟩

lemma hopf_spatial_quotient_bound {f : X → ℝ} {B t r : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x z y w : X}
    (hy : hopfObjective f t x y = hopfLax f t x)
    (hw : hopfObjective f t z w = hopfLax f t z)
    (hyr : dist x y ≤ r) (hwr : dist z w ≤ r) (hzx : z ≠ x) :
    |hopfLax f t z - hopfLax f t x| / dist z x ≤ r/t + dist z x/(2*t) := by
  have H := hopf_spatial_increment hlower ht hy z
  have H' := hopf_spatial_increment hlower ht hw x
  have I : dist x y / t * dist z x ≤ r/t * dist z x := by gcongr
  have I' : dist z w / t * dist z x ≤ r/t * dist z x := by gcongr
  rw [dist_comm x z] at H'
  have Ha : |hopfLax f t z-hopfLax f t x| ≤ r/t*dist z x + dist z x^2/(2*t) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  apply (div_le_iff₀ (dist_pos.mpr hzx)).mpr
  apply Ha.trans_eq
  ring

lemma hopf_localSlope_le [ProperSpace X] {f : X → ℝ} {B U t : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) {x y : X} (hy : IsFarthestHopfMinimizer f t x y) :
    Filter.limsup (fun z => ENNReal.ofReal
      (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x) ≤
      ENNReal.ofReal (dist x y/t) := by
  by_cases hbot : (𝓝[≠] x) = ⊥
  · simp [hbot]
  have : NeBot (𝓝[≠] x) := ⟨hbot⟩
  have H : ∀ r : ℝ, dist x y < r →
      Filter.limsup (fun z => ENNReal.ofReal
        (|hopfLax f t z - hopfLax f t x| / dist z x)) (𝓝[≠] x) ≤ ENNReal.ofReal (r/t) := by
    intro r hr
    have he := eventually_hopf_minimizer_distance_lt hf hlower hupper hBU ht hy hr
    have hb : ∀ᶠ z in 𝓝[≠] x, ENNReal.ofReal (|hopfLax f t z-hopfLax f t x|/dist z x) ≤
        ENNReal.ofReal (r/t+dist z x/(2*t)) := by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzx
      obtain ⟨w,hw⟩ := exists_hopf_minimizer hf hlower ht z
      apply ENNReal.ofReal_le_ofReal
      exact hopf_spatial_quotient_bound hlower ht hy.1 hw hr.le (hz w hw).le hzx
    have hc : Tendsto (fun z => ENNReal.ofReal (r/t+dist z x/(2*t))) (𝓝[≠] x)
        (𝓝 (ENNReal.ofReal (r/t))) := by
      have hc' : ContinuousAt (fun z => ENNReal.ofReal (r/t+dist z x/(2*t))) x :=
        ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
      simpa using hc'.tendsto.mono_left nhdsWithin_le_nhds
    exact (limsup_le_limsup hb).trans_eq hc.limsup_eq
  have hc : Tendsto (fun r : ℝ => ENNReal.ofReal (r/t)) (𝓝[>] dist x y)
      (𝓝 (ENNReal.ofReal (dist x y/t))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_id.div_const t)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hc
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact H r hr

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_HopfMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
open WeakHessian

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma hopf_forward_increment {f : X → ℝ} {B U t s : ℝ}
    (hf : Continuous f) (hlower : ∀ y, B ≤ f y) (hupper : ∀ y, f y ≤ U)
    (hBU : B ≤ U) (ht : 0 < t) (hts : t ≤ s) (x : X) :
    hopfLax f s x - hopfLax f t x ≤
      -(s-t)*t/(2*s) * (localSlope (hopfLax f t) x).toReal^2 := by
  have hs : 0 < s := ht.trans_le hts
  obtain ⟨y,hy⟩ := exists_farthest_hopf_minimizer hf hlower hupper hBU ht x
  have hi := hopf_time_increment hlower hs ht hy.1
  have hsl := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hopf_localSlope_le hf hlower hupper hBU ht hy)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist x y/t)] at hsl
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity : 0 ≤ dist x y/t)).mpr hsl
  have hcoef : 0 ≤ (s-t)*t/(2*s) := by positivity
  have heq : dist x y^2*(t-s)/(2*s*t) = -((s-t)*t/(2*s))*(dist x y/t)^2 := by
    field_simp
    ring
  rw [heq] at hi
  simpa only [neg_div, neg_mul, localSlope] using
    hi.trans (mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hcoef))

end WeakHessianTransport

namespace WeakHessianTransport
open WeakHessian MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

omit [CompactSpace X] in
lemma cheegerEnergy_le_integral_localSlope {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hm : MemLp f 2 m) :
    cheegerEnergy m f ≤ ENNReal.ofReal ((∫ x, (localSlope f x).toReal^2 ∂m)/2) := by
  have H := cheegerEnergy_le_liminf hm (fs := fun _ => f)
    (fun _ => ⟨⟨L,hf⟩,hm⟩) (by simp)
  rw [liminf_const] at H
  have he : (∫⁻ x, localSlope f x^2 ∂m) = ENNReal.ofReal (∫ x, (localSlope f x).toReal^2 ∂m) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_localSlope_sq m hf)
      (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ((localSlope_le_lipschitz hf x).trans_lt (by simp)).ne]
  rw [he] at H
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]
  simpa only [div_eq_mul_inv, mul_comm] using H

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


namespace WeakHessianTransport
open WeakHessian MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

omit [MeasurableSpace X] [BorelSpace X] in

def boundedHopfMap (f : X →ᵇ ℝ) (t : ℝ) : X →ᵇ ℝ :=
  if ht : 0 < t then
    BoundedContinuousFunction.ofNormedAddCommGroup (hopfLax f t)
      (hopfLax_continuous f.continuous (fun x => (boundedContinuous_bounds f x).1)
        (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht)
      ‖f‖ (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨lower_le_hopfLax (fun x => (boundedContinuous_bounds f x).1) ht x,
          (hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) ht x).trans
            (boundedContinuous_bounds f x).2⟩)
  else f

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma boundedHopfMap_zero (f : X →ᵇ ℝ) : boundedHopfMap f 0 = f := by simp [boundedHopfMap]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_apply_pos (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) (x : X) :
    boundedHopfMap f t x = hopfLax f t x := by simp [boundedHopfMap, ht]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_time_lipschitz (f : X →ᵇ ℝ) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨2*‖f‖/a, by positivity⟩ (boundedHopfMap f) (Ici a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  apply (BoundedContinuousFunction.dist_le (by positivity : 0 ≤ 2*‖f‖/a*dist t s)).mpr
  intro x
  rw [boundedHopfMap_apply_pos f (ha.trans_le ht), boundedHopfMap_apply_pos f (ha.trans_le hs)]
  have H := hopf_time_abs_bound f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ha ht hs x
  simpa only [Real.dist_eq, sub_neg_eq_add, ← two_mul] using H

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_dist_initial {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 ≤ t) : dist (boundedHopfMap f t) f ≤ t*(L:ℝ)^2/2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  apply (BoundedContinuousFunction.dist_le (by positivity : 0 ≤ t*(L:ℝ)^2/2)).mpr
  intro x
  rw [boundedHopfMap_apply_pos f ht, Real.dist_eq]
  have H := hopfLax_ge_lipschitz hf ht x
  have H' := hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) ht x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuousOn_boundedHopfMap {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (boundedHopfMap f) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases ht.eq_or_lt with rfl | ht
  · rw [ContinuousWithinAt, boundedHopfMap_zero]
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      (show ∀ᶠ s in 𝓝[≥] (0:ℝ), dist (boundedHopfMap f s) f ≤ s*(L:ℝ)^2/2 from
        Filter.Eventually.mono self_mem_nhdsWithin (fun s hs => boundedHopfMap_dist_initial hf hs))
    have H : Tendsto (fun s : ℝ => s*(L:ℝ)^2/2) (𝓝[≥] (0:ℝ)) (𝓝 (0*(L:ℝ)^2/2)) :=
      (((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0:ℝ)) (𝓝 0)).mul_const
        ((L:ℝ)^2)).div_const 2).mono_left nhdsWithin_le_nhds
    simpa using H
  · exact ((boundedHopfMap_time_lipschitz f (by positivity : 0 < t/2)).continuousOn.continuousAt
      (Ici_mem_nhds (by linarith : t/2 < t))).continuousWithinAt

def boundedHopfLp (f : X →ᵇ ℝ) (t : ℝ) : Lp ℝ 2 m := BoundedContinuousFunction.toLp 2 m ℝ (boundedHopfMap f t)

lemma continuousOn_boundedHopfLp {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (boundedHopfLp m f) (Ici 0) :=
  (BoundedContinuousFunction.toLp 2 m ℝ).continuous.comp_continuousOn (continuousOn_boundedHopfMap hf)

lemma boundedHopfLp_coe_ae (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    (boundedHopfLp m f t : X → ℝ) =ᵐ[m] hopfLax f t := by
  apply (BoundedContinuousFunction.coeFn_toLp 2 m ℝ (boundedHopfMap f t)).trans
  exact Eventually.of_forall (boundedHopfMap_apply_pos f ht)
lemma boundedHopfLp_energy_bound (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    cheegerEnergy m (boundedHopfLp m f t : X → ℝ) < ∞ ∧
      (cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal ≤
        (∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m)/2 := by
  have hf := hopfLax_lipschitz_radius f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖)))) (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have hm : MemLp (hopfLax f t) 2 m := (memLp_congr_ae (boundedHopfLp_coe_ae m f ht)).mp (Lp.memLp (boundedHopfLp m f t))
  have H := cheegerEnergy_le_integral_localSlope m hf hm
  rw [← cheegerEnergy_congr_ae (boundedHopfLp_coe_ae m f ht)] at H
  have hfin := H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  have Hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
  rwa [ENNReal.toReal_ofReal (by positivity)] at Hr

end WeakHessianTransport

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfLpPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianTransport
open WeakHessian MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma boundedHopfLp_pairing_increment (f : X →ᵇ ℝ) {t s α : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (hα : 0 ≤ α) (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, α ≤ ρ x) :
    ⟪boundedHopfLp m f s-boundedHopfLp m f t,ρ⟫_ℝ ≤
      -(s-t)*t/s*α*(cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal := by
  have hs : 0 < s := ht.trans_le hts
  let k : ℝ := (s-t)*t/(2*s)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hf := hopfLax_lipschitz_radius f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖))))
    (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have he := (boundedHopfLp_energy_bound m f ht).2
  have HI := integral_mono_ae (L2.integrable_inner (boundedHopfLp m f s-boundedHopfLp m f t) ρ (𝕜 := ℝ))
    ((integrable_localSlope_sq m hf).const_mul (-k*α)) (show
      ∀ᵐ x ∂m, ⟪(boundedHopfLp m f s-boundedHopfLp m f t) x,ρ x⟫_ℝ ≤
      (-k*α)*(localSlope (hopfLax f t) x).toReal^2 from by
        filter_upwards [Lp.coeFn_sub (boundedHopfLp m f s) (boundedHopfLp m f t),
          boundedHopfLp_coe_ae m f hs, boundedHopfLp_coe_ae m f ht, hρ] with x hx hxs hxt hxρ
        rw [hx, Pi.sub_apply, hxs, hxt, RCLike.inner_apply, conj_trivial]
        have H := hopf_forward_increment f.continuous (fun x => (boundedContinuous_bounds f x).1)
          (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht hts x
        have Hnorm : hopfLax f s x-hopfLax f t x ≤ -k*(localSlope (hopfLax f t) x).toReal^2 := by
          simpa only [k, neg_mul, neg_div] using H
        have H' := mul_le_mul_of_nonneg_left Hnorm (hα.trans hxρ)
        have H'' := mul_le_mul_of_nonpos_left hxρ
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) (sq_nonneg ((localSlope (hopfLax f t) x).toReal)))
        change ρ x * (hopfLax f s x-hopfLax f t x) ≤ _
        calc
          _ ≤ ρ x * (-k*(localSlope (hopfLax f t) x).toReal^2) := H'
          _ = (-k*(localSlope (hopfLax f t) x).toReal^2)*ρ x := by ring
          _ ≤ (-k*(localSlope (hopfLax f t) x).toReal^2)*α := H''
          _ = _ := by ring)
  rw [integral_const_mul] at HI
  rw [L2.inner_def]
  apply HI.trans
  have H := mul_le_mul_of_nonpos_left he (by nlinarith [mul_nonneg hk hα] : -2*k*α ≤ 0)
  calc
    -k*α*(∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m) =
      (-2*k*α)*((∫ x, (localSlope (hopfLax f t) x).toReal^2 ∂m)/2) := by ring
    _ ≤ (-2*k*α)*(cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal := H
    _ = _ := by dsimp [k]; ring

end WeakHessianTransport

open Set

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_TruncatedQuadraticCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in

lemma bounded_lipschitz_dual_improvement {t : ℝ} (ht : 0 < t)
    (a b : X →ᵇ ℝ) (hab : ∀ x y, a x+b y ≤ dist x y^2/(2*t)) :
    ∃ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) ∧
      (∀ x, |f x| ≤ ‖a‖) ∧
      (∀ x, a x ≤ hopfLax f t x) ∧ (∀ y, f y ≤ -b y) := by
  let B := ‖a‖
  have ha : ∀ x, |a x| ≤ B := fun x => a.norm_coe_le_norm x
  have hlo : ∀ x, -B ≤ -a x := fun x => by linarith [(abs_le.mp (ha x)).2]
  have hup : ∀ x, -a x ≤ B := fun x => by linarith [(abs_le.mp (ha x)).1]
  have hBU : -B ≤ B := by dsimp [B]; linarith [norm_nonneg a]
  have hlip := hopfLax_lipschitz_radius a.continuous.neg hlo hup hBU ht
    (Real.sqrt_nonneg (2*t*(B-(-B))))
    (Real.sq_sqrt (show 0 ≤ 2*t*(B-(-B)) by positivity)).ge
  let f : X → ℝ := fun y => -hopfLax (fun x => -a x) t y
  have hfbound : ∀ y, |f y| ≤ B := by
    intro y
    have H := lower_le_hopfLax hlo ht y
    have I := (hopfLax_le_self hlo ht y).trans (hup y)
    exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
  refine ⟨f, ⟨_, hlip.neg⟩, hfbound, ?_, ?_⟩
  · intro x
    apply le_csInf ⟨hopfObjective f t x x, mem_range_self x⟩
    rintro r ⟨y,rfl⟩
    have H := hopfLax_le_objective hlo ht y x
    dsimp [hopfObjective, f] at *
    rw [dist_comm y x] at H
    linarith
  · intro y
    suffices b y ≤ hopfLax (fun x => -a x) t y by
      dsimp [f]
      linarith
    apply le_csInf ⟨hopfObjective (fun x => -a x) t y y, mem_range_self y⟩
    rintro r ⟨x,rfl⟩
    have H := hab x y
    change a x + b y ≤ dist x y^2/(2*t) at H
    dsimp [hopfObjective]
    rw [dist_comm y x]
    linarith

variable [TopologicalSpace.SeparableSpace X]

lemma exists_coupling_truncatedCost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) (n : ℕ) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫ p,truncatedQuadraticCost n p ∂q) ≤ B/2 := by
  obtain ⟨q,hq,h0,h1,hql⟩ := bounded_kantorovich_duality μ ν (truncatedQuadraticCost n)
  let := hq
  refine ⟨q,hq,h0,h1,?_⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨⟨a,b⟩,hab,habI⟩ := hql ε hε
  have hab' (x y : X) : a x+b y ≤ dist x y^2/(2*(1:ℝ)) := by
    have H := hab (x,y)
    change a x+b y ≤ min (dist x y^2/2) (n:ℝ) at H
    simpa only [mul_one] using H.trans (min_le_left _ _)
  obtain ⟨f,⟨L,hf⟩,hB,haf,hfb⟩ := bounded_lipschitz_dual_improvement (by norm_num : (0:ℝ)<1) a b hab'
  let f' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous ‖a‖
    (fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hd := hdual f' ⟨L,hf⟩
  have hlo (x : X) : -‖a‖ ≤ f x := (abs_le.mp (hB x)).1
  have hup (x : X) : f x ≤ ‖a‖ := (abs_le.mp (hB x)).2
  have hc : Continuous (hopfLax f 1) := hopfLax_continuous hf.continuous hlo hup
    (by linarith [norm_nonneg a]) (by norm_num)
  have hi : Integrable (hopfLax f 1) μ := Integrable.of_bound hc.aestronglyMeasurable ‖a‖
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨lower_le_hopfLax hlo (by norm_num) x,
        (hopfLax_le_self hlo (by norm_num) x).trans (hup x)⟩)
  have HA := integral_mono (a.integrable μ) hi haf
  have HB := integral_mono (f'.integrable ν) (b.integrable ν).neg hfb
  change (∫ x,f x ∂ν) ≤ ∫ x,-b x ∂ν at HB
  rw [integral_neg] at HB
  change (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2 at hd
  change (∫ p,truncatedQuadraticCost n p ∂q) < (∫ x,a x ∂μ)+(∫ x,b x ∂ν)+ε at habI
  linarith
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_ProbabilityTightMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_proper_coupling_cost_of_hopf_bound (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (B : ℝ)
    (hdual : ∀ f : X →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L f) →
      (∫ x,hopfLax f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B/2) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂(q:Measure (X×X))) ≤ ENNReal.ofReal B := by
  choose qs hp h0 h1 hc using exists_coupling_truncatedCost_of_hopf_bound μ ν B hdual
  let ps : ℕ → ProbabilityMeasure (X×X) := fun n => ⟨qs n,hp n⟩
  obtain ⟨q,φ,hφ,hlim,hq0,hq1⟩ := exists_coupling_limit μ ν ps h0 h1
  have hcost (k : ℕ) : (∫ p,truncatedQuadraticCost k p ∂(q:Measure (X×X))) ≤ B/2 := by
    have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (truncatedQuadraticCost k)
    apply le_of_tendsto H
    filter_upwards [eventually_ge_atTop k] with n hn
    have hk : k ≤ φ n := hn.trans (hφ.id_le n)
    have hi (p : X×X) : truncatedQuadraticCost k p ≤ truncatedQuadraticCost (φ n) p := by
      exact min_le_min_left _ (Nat.cast_le.mpr hk)
    let := hp (φ n)
    exact (integral_mono ((truncatedQuadraticCost k).integrable (qs (φ n)))
      ((truncatedQuadraticCost (φ n)).integrable (qs (φ n))) hi).trans (hc (φ n))
  have hnn (k : ℕ) (p : X×X) : 0 ≤ truncatedQuadraticCost k p :=
    le_min (by positivity) (Nat.cast_nonneg k)
  have heavg : (∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X))) ≤ ENNReal.ofReal (B/2) := by
    have hs (p : X×X) : ENNReal.ofReal (dist p.1 p.2^2/2) =
        ⨆ n : ℕ, ENNReal.ofReal (truncatedQuadraticCost n p) := by
      apply le_antisymm
      · obtain ⟨n,hn⟩ := exists_nat_gt (dist p.1 p.2^2/2)
        exact (le_iSup_of_le n (by simp only [truncatedQuadraticCost_apply, min_eq_left hn.le]; exact le_rfl))
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    simp_rw [hs]
    rw [lintegral_iSup (fun n => (truncatedQuadraticCost n).continuous.measurable.ennreal_ofReal)]
    · apply iSup_le
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal ((truncatedQuadraticCost n).integrable (q:Measure (X×X)))
        (ae_of_all _ (hnn n))]
      exact ENNReal.ofReal_le_ofReal (hcost n)
    · intro a b hab p
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hab))
  refine ⟨q,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),hq0,hq1,?_⟩
  calc
    (∫⁻ p, (edist p.1 p.2)^2 ∂(q:Measure (X×X))) =
        ∫⁻ p : X×X, (2:ℝ≥0∞)*ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X)) := by
      apply lintegral_congr
      intro p
      rw [edist_dist,←ENNReal.ofReal_pow dist_nonneg]
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    _ = 2*(∫⁻ p : X×X, ENNReal.ofReal (dist p.1 p.2^2/2) ∂(q:Measure (X×X))) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ 2*ENNReal.ofReal (B/2) := by gcongr
    _ = ENNReal.ofReal B := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfLpDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianTransport

section DualPairing
open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma boundedHopfLp_dual_pairing_le
    {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {ρ A : ℝ → Lp ℝ 2 m} {b α M : ℝ}
    (hb : 0 ≤ b) (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 b))
    (hlower : ∀ t ∈ Ico 0 b, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hyoung : ∀ t ∈ Ico 0 b, ∀ q : Lp ℝ 2 m, cheegerEnergy m (q : X → ℝ) < ∞ →
      -α*(cheegerEnergy m (q : X → ℝ)).toReal + ⟪q,A t⟫_ℝ ≤ M)
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt ρ (A t) (Ici t) t) :
    ⟪boundedHopfLp m f b,ρ b⟫_ℝ - ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ 0⟫_ℝ ≤ b*M := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [boundedHopfLp]
  have H (a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      ⟪boundedHopfLp m f b,ρ b⟫_ℝ - ⟪boundedHopfLp m f a,ρ a⟫_ℝ ≤ (b-a)*M := by
    have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc ha.le le_rfl
    have hq : ContinuousOn (boundedHopfLp m f) (Icc a b) := (continuousOn_boundedHopfLp m hf).mono
      (fun t ht => ha.le.trans ht.1)
    apply dualTransport_pairing_le ha hab hα hq (hρ.mono hsub)
    · intro t ht
      exact hyoung t ⟨ha.le.trans ht.1,ht.2⟩ _ (boundedHopfLp_energy_bound m f (ha.trans_le ht.1)).1
    · intro t ht
      exact hderiv t ⟨ha.le.trans ht.1,ht.2⟩
    · intro t ht s hs
      exact boundedHopfLp_pairing_increment m f (ha.trans_le ht.1) hs.1.le hα.le (ρ t)
        (hlower t ⟨ha.le.trans ht.1,ht.2⟩)
  have hq0 : Tendsto (boundedHopfLp m f) (𝓝[>] (0:ℝ)) (𝓝 (BoundedContinuousFunction.toLp 2 m ℝ f)) := by
    simpa only [boundedHopfLp, boundedHopfMap_zero] using
      ((continuousOn_boundedHopfLp m hf) 0 (by simp)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hρ0 : Tendsto ρ (𝓝[>] (0:ℝ)) (𝓝 (ρ 0)) :=
    (hρ 0 ⟨le_rfl,hb.le⟩).mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl,hb⟩))
  have hleft : Tendsto (fun a : ℝ => ⟪boundedHopfLp m f b,ρ b⟫_ℝ-⟪boundedHopfLp m f a,ρ a⟫_ℝ)
      (𝓝[>] (0:ℝ)) (𝓝 (⟪boundedHopfLp m f b,ρ b⟫_ℝ-⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ 0⟫_ℝ)) :=
    tendsto_const_nhds.sub (hq0.inner hρ0)
  have hright : Tendsto (fun a : ℝ => (b-a)*M) (𝓝[>] (0:ℝ)) (𝓝 (b*M)) := by
    have hc : Continuous (fun a : ℝ => (b-a)*M) := by fun_prop
    simpa only [sub_zero] using (hc.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioc_mem_nhdsGT hb] with a ha
  exact H a ha.1 ha.2

end DualPairing

open WeakHessian WeakHessianFunctional MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

lemma proper_dual_density_coupling_bound
    {ρ A : ℝ → Lp ℝ 2 m} {α M : ℝ}
    (hα : 0 < α) (hρ : ContinuousOn ρ (Icc 0 1))
    (hpos : ∀ t ∈ Icc 0 1, ∀ᵐ x ∂m, 0 ≤ ρ t x)
    (hmass : ∀ t ∈ Icc 0 1, ∫ x, ρ t x ∂m = 1)
    (hlower : ∀ t ∈ Ico 0 1, ∀ᵐ x ∂m, α ≤ ρ t x)
    (hyoung : ∀ t ∈ Ico 0 1, ∀ q : Lp ℝ 2 m, cheegerEnergy m (q : X → ℝ) < ∞ →
      -α*(cheegerEnergy m (q : X → ℝ)).toReal + ⟪q,A t⟫_ℝ ≤ M)
    (hderiv : ∀ t ∈ Ico 0 1, HasDerivWithinAt ρ (A t) (Ici t) t) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (ρ 1) ∧
      q.map Prod.snd = densityMeasure m (ρ 0) ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal (2*M) := by
  let hp0 := densityMeasure_probability m (ρ 0) (hpos 0 (by norm_num)) (hmass 0 (by norm_num))
  let hp1 := densityMeasure_probability m (ρ 1) (hpos 1 (by norm_num)) (hmass 1 (by norm_num))
  apply exists_proper_coupling_cost_of_hopf_bound _ _ (2*M)
  intro f hf
  obtain ⟨L,hf⟩ := hf
  let f' : X →ᵇ ℝ := f
  have H := boundedHopfLp_dual_pairing_le m (f := f') hf (by norm_num : (0:ℝ) ≤ 1)
    hα hρ hlower hyoung hderiv
  have hq : (fun x => hopfLax f 1 x) = (boundedHopfMap f' 1 : X → ℝ) := by
    funext x
    exact (boundedHopfMap_apply_pos f' (by norm_num) x).symm
  rw [hq, integral_densityMeasure_boundedContinuous m _ (hpos 1 (by norm_num))]
  change _ - (∫ x, f' x ∂densityMeasure m (ρ 0)) ≤ _
  rw [integral_densityMeasure_boundedContinuous m _ (hpos 0 (by norm_num))]
  change ⟪boundedHopfLp m f' 1,ρ 1⟫_ℝ - ⟪BoundedContinuousFunction.toLp 2 m ℝ f',ρ 0⟫_ℝ ≤ _
  calc
    _ ≤ 1*M := H
    _ = _ := by ring

end WeakHessianTransport

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LiftBoundedCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma CurvatureDimension.lift_coupling {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) (q : Measure (X×X)) [IsFiniteMeasure q]
    (hac0 : q.map Prod.fst ≪ m) (hac1 : q.map Prod.snd ≪ m) [Nonempty X] :
    ∃ π : Measure (Curve X), interpolation π timeZero = q.map Prod.fst ∧
      interpolation π timeOne = q.map Prod.snd ∧
      (∫⁻ γ,kineticAction γ ∂π) ≤ QuadraticTransportCost q := by
  let o : X := Classical.arbitrary X
  let S : ℕ → Set (X×X) := fun n => Metric.closedBall o n ×ˢ Metric.closedBall o n
  let T : ℕ → Set (X×X) := disjointed S
  have hS (n : ℕ) : MeasurableSet (S n) := Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet
  have hT (n : ℕ) : MeasurableSet (T n) := MeasurableSet.disjointed hS n
  have hcover : ⋃ n,T n = univ := by
    rw [iUnion_disjointed]
    apply eq_univ_of_forall
    intro p
    obtain ⟨n,hn⟩ := exists_nat_gt (max (dist p.1 o) (dist p.2 o))
    exact mem_iUnion.mpr ⟨n,⟨(le_max_left _ _).trans hn.le,(le_max_right _ _).trans hn.le⟩⟩
  have hsum : Measure.sum (fun n => q.restrict (T n)) = q := by
    rw [←Measure.restrict_iUnion (disjoint_disjointed S) hT,hcover,Measure.restrict_univ]
  have hex (n : ℕ) : ∃ π : Measure (Curve X),
      interpolation π timeZero = (q.restrict (T n)).map Prod.fst ∧
      interpolation π timeOne = (q.restrict (T n)).map Prod.snd ∧
      (∫⁻ γ,kineticAction γ ∂π) ≤ QuadraticTransportCost (q.restrict (T n)) := by
    apply hcd.lift_bounded_coupling (q.restrict (T n))
      ((Measure.absolutelyContinuous_of_le (Measure.map_mono Measure.restrict_le_self measurable_fst)).trans hac0)
      ((Measure.absolutelyContinuous_of_le (Measure.map_mono Measure.restrict_le_self measurable_snd)).trans hac1) o n
    filter_upwards [ae_restrict_mem (hT n)] with p hp
    exact disjointed_subset S n hp
  choose πs h0 h1 hA using hex
  refine ⟨Measure.sum πs,?_,?_,?_⟩
  · change (Measure.sum πs).map _ = _
    rw [Measure.map_sum (continuous_eval_const timeZero).measurable.aemeasurable]
    simp_rw [show ∀ n,(πs n).map (fun γ => γ timeZero) = (q.restrict (T n)).map Prod.fst from h0]
    rw [←Measure.map_sum measurable_fst.aemeasurable,hsum]
  · change (Measure.sum πs).map _ = _
    rw [Measure.map_sum (continuous_eval_const timeOne).measurable.aemeasurable]
    simp_rw [show ∀ n,(πs n).map (fun γ => γ timeOne) = (q.restrict (T n)).map Prod.snd from h1]
    rw [←Measure.map_sum measurable_snd.aemeasurable,hsum]
  · rw [lintegral_sum_measure]
    calc
      _ ≤ ∑' n,QuadraticTransportCost (q.restrict (T n)) := ENNReal.tsum_le_tsum hA
      _ = QuadraticTransportCost q := by simp only [QuadraticTransportCost]; rw [←lintegral_sum_measure,hsum]
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_DynamicActionBoundProper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] [Nonempty X]

lemma CurvatureDimension.dynamicActionBound_proper {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) (μ : Time → ProbabilityMeasure X)
    (hac : ∀ t,(μ t:Measure X) ≪ m)
    {C : ℝ} (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C) :
    DynamicActionBound (fun t => (μ t:Measure X)) C := by
  intro s t
  obtain ⟨q,hq,hqb⟩ := hcost s t
  have hp : IsProbabilityMeasure (q.map Prod.fst) := by rw [hq.1]; infer_instance
  let := Measure.isProbabilityMeasure_of_map (μ := q) Prod.fst
  obtain ⟨π,h0,h1,hA⟩ := hcd.lift_coupling q (by rw [hq.1]; exact hac s)
    (by rw [hq.2]; exact hac t)
  have hpπ : IsProbabilityMeasure (π.map (fun γ => γ timeZero)) := by
    change IsProbabilityMeasure (interpolation π timeZero)
    rw [h0,hq.1]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  haveI : IsProbabilityMeasure (π.map (fun γ : Curve X => γ timeZero)) := by change IsProbabilityMeasure (interpolation π timeZero); rw [h0]; exact hp
  let := Measure.isProbabilityMeasure_of_map (μ := π) (fun γ : Curve X => γ timeZero)
  exact ⟨π,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),h0.trans hq.1,h1.trans hq.2,hA.trans hqb⟩

lemma exists_proper_testPlan_superposition (m : Measure X)
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (h : DynamicActionBound (fun t => (μ t:Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time,(μ t:Measure X) ≤ (L:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X), IsTestPlan m π ∧
      (∀ t : Time,π.map (fun γ => γ t) = (μ t:Measure X)) ∧
      (∫⁻ γ,∫⁻ t in Icc (0:ℝ) 1,(metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  obtain ⟨π,hmarg,_hA,hAC,hS⟩ := exists_superposition_proper μ hμ hC h
  refine ⟨π,⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),?_,hAC,hS.trans_lt ENNReal.ofReal_lt_top⟩,hmarg,hS⟩
  obtain ⟨L,hL⟩ := hcomp
  exact ⟨L,fun t => by rw [hmarg t]; exact hL t⟩

end WeakHessian

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsProbabilityMeasure m]

lemma prox_linearDensity_coupling_forward {u v D : Lp ℝ 2 m} {t : ℝ}
    (h : RelaxedProx u t v D) (hmass : ∫ x,u x ∂m = 0) {ε B a b : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) (hv : ∀ᵐ x ∂m, |v x| ≤ B)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (hab : a ≤ b) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (linearDensity ε u v b) ∧
      q.map Prod.snd = densityMeasure m (linearDensity ε u v a) ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤
        ENNReal.ofReal (ε^2/(1-ε*B)*(t^2*‖D‖)^2*(b-a)^2) := by
  have hi (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : a+(b-a)*r ∈ Icc (0:ℝ) 1 := by
    constructor
    · have := mul_nonneg (sub_nonneg.mpr hab) hr.1; linarith [ha.1]
    · have := mul_le_mul_of_nonneg_left hr.2 (sub_nonneg.mpr hab); nlinarith [hb.2]
  have hα : 0 < 1-ε*B := sub_pos.mpr hεB
  have hpos (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      ∀ᵐ x ∂m,0 ≤ linearDensity ε u v (a+(b-a)*r) x :=
    (linearDensity_bounds hε hB (hi r hr) hu hv).mono fun _ hx => hα.le.trans hx.1
  have hv0 := h.mass.trans hmass
  obtain ⟨q,hq,hq0,hq1,hqb⟩ := proper_dual_density_coupling_bound m
    (ρ := fun r => linearDensity ε u v (a+(b-a)*r))
    (A := fun _ => (-(ε*(b-a))) • (u-v))
    (M := (-(ε*(b-a)))^2/(1-ε*B)*(t^2*‖D‖)^2/2)
    hα ((continuous_linearDensity ε u v).comp (by fun_prop)).continuousOn hpos
    (fun r _ => linearDensity_mass ε u v hmass hv0 _)
    (fun r hr => (linearDensity_bounds hε hB (hi r (Ico_subset_Icc_self hr)) hu hv).mono fun _ hx => hx.1)
    (fun _ _ f hf => h.young hf hα)
    (fun r _ => by
      have H := (linearDensity_affine_deriv ε u v a (b-a) r).hasDerivWithinAt (s := Ici r)
      have he : (-(ε*(b-a))) • (u-v) = (ε*(b-a)) • (v-u) := by
        rw [neg_smul,smul_sub,smul_sub]
        abel
      rw [he]
      exact H)
  refine ⟨q,hq,?_,?_,?_⟩
  · convert hq0 using 2
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · simpa only [mul_zero,add_zero] using hq1
  · apply hqb.trans_eq
    congr 1
    ring

lemma prox_linearDensity_coupling_cost {u v D : Lp ℝ 2 m} {t : ℝ}
    (h : RelaxedProx u t v D) (hmass : ∫ x,u x ∂m = 0) {ε B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) (hv : ∀ᵐ x ∂m, |v x| ≤ B) :
    CouplingCostBound (fun r : Time => densityMeasure m (linearDensity ε u v r))
      (ε^2/(1-ε*B)*(t^2*‖D‖)^2) := by
  intro s r
  rcases le_total (s:ℝ) (r:ℝ) with hsr | hrs
  · obtain ⟨q,hq,hq0,hq1,hqb⟩ := prox_linearDensity_coupling_forward h hmass hε hB hεB hu hv s.2 r.2 hsr
    refine ⟨q.map Prod.swap,⟨?_,?_⟩,?_⟩
    · rw [Measure.map_map measurable_fst measurable_swap]
      simpa only [Function.comp_def,Prod.fst_swap] using hq1
    · rw [Measure.map_map measurable_snd measurable_swap]
      simpa only [Function.comp_def,Prod.snd_swap] using hq0
    · rw [QuadraticTransportCost,lintegral_map
        ((continuous_fst.edist continuous_snd).measurable.pow_const 2) measurable_swap]
      simp only [Prod.fst_swap,Prod.snd_swap]
      simp_rw [edist_comm]
      convert hqb using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      change _ * |(s:ℝ)-(r:ℝ)|^2 = _
      rw [sq_abs]
      ring
  · obtain ⟨q,hq,hq0,hq1,hqb⟩ := prox_linearDensity_coupling_forward h hmass hε hB hεB hu hv r.2 s.2 hrs
    refine ⟨q,⟨hq0,hq1⟩,?_⟩
    change (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤ _
    convert hqb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    change _ * |(s:ℝ)-(r:ℝ)|^2 = _
    rw [sq_abs]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_TestPlanCostReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X}

lemma CurvatureDimension.testPlan_of_cost_reference [Nonempty X] {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time,(μ t:Measure X) ≤ (L:ℝ≥0∞) • ν) :
    ∃ π : Measure (Curve X), IsTestPlan ν π ∧
      (∀ t : Time,π.map (fun γ => γ t) = (μ t:Measure X)) ∧
      (∫⁻ γ,∫⁻ t in Icc (0:ℝ) 1,(metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  apply exists_proper_testPlan_superposition ν μ hμ hC _ hcomp
  apply hcd.dynamicActionBound_proper μ _ hcost
  obtain ⟨L,hL⟩ := hcomp
  intro t
  exact (Measure.absolutelyContinuous_of_le_smul (hL t)).trans hν

variable [IsProbabilityMeasure ν]
lemma CurvatureDimension.prox_testPlan {K N : ℝ} (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (hmass : ∫ x,u x ∂ν = 0) {ε B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂ν, |u x| ≤ B) (hv : ∀ᵐ x ∂ν, |v x| ≤ B) :
    ∃ π : Measure (Curve X), IsTestPlan ν π ∧
      (∀ r : Time, π.map (fun γ => γ r) = densityMeasure ν (linearDensity ε u v r)) ∧
      (∀ r : Time, π.map (fun γ => γ r) ≤ ENNReal.ofReal (1+ε*B) • ν) ∧
      (∫⁻ γ,∫⁻ r in Icc (0:ℝ) 1,(metricSpeed γ r)^2 ∂volume ∂π) ≤
        ENNReal.ofReal (ε^2/(1-ε*B)*(t^2*‖D‖)^2) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure ν
  let ρ : Time → Lp ℝ 2 ν := fun r => linearDensity ε u v r
  have hpos (r : Time) : ∀ᵐ x ∂ν,0 ≤ ρ r x :=
    (linearDensity_bounds hε hB r.2 hu hv).mono fun _ hx => (sub_pos.mpr hεB).le.trans hx.1
  have hm (r : Time) : ∫ x,ρ r x ∂ν = 1 := linearDensity_mass ε u v hmass (h.mass.trans hmass) _
  let μ : Time → ProbabilityMeasure X := fun r => densityProbability ν (ρ r) (hpos r) (hm r)
  have hρ : Continuous ρ := (continuous_linearDensity ε u v).comp continuous_subtype_val
  have hμ : Continuous μ := continuous_boundedDensityProbability ν hρ hpos hm
  have hcomp (r : Time) : (μ r:Measure X) ≤ ENNReal.ofReal (1+ε*B) • ν :=
    densityMeasure_le ν ((linearDensity_bounds hε hB r.2 hu hv).mono fun _ hx => hx.2)
  have hcomp' : ∃ L : ℝ≥0, ∀ r : Time,(μ r:Measure X) ≤ (L:ℝ≥0∞) • ν := by
    exact ⟨Real.toNNReal (1+ε*B), hcomp⟩
  obtain ⟨π,hπ,hmarg,hact⟩ := hcd.testPlan_of_cost_reference hν μ hμ
    (by positivity : 0 ≤ ε^2/(1-ε*B)*(t^2*‖D‖)^2)
    (prox_linearDensity_coupling_cost h hmass hε hB hεB hu hv) hcomp'
  exact ⟨π,hπ,hmarg,fun r => by rw [hmarg]; exact hcomp r,hact⟩
end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_IntegralDensityMeasureLp'
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.prox_weak_pairing_perturbed {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (hmass : ∫ x,u x ∂ν = 0) {ε B : ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂ν, |u x| ≤ B) (hv : ∀ᵐ x ∂ν, |v x| ≤ B)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    |⟪f,u-v⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure ν
  obtain ⟨π,hπ,hmarg,hcomp,hact⟩ := hcd.prox_testPlan hν h hmass hε.le hB hεB hu hv
  let C : ℝ≥0 := ⟨1+ε*B,by positivity⟩
  have hC (r : Time) : π.map (fun γ => γ r) ≤ (C:ℝ≥0∞) • ν := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hcomp r
  have H := hf.endpoint_pairing_bound_global hπ hC
    (by positivity : 0 ≤ ε^2/(1-ε*B)*(t^2*‖D‖)^2) hact
  rw [hmarg timeOne,hmarg timeZero] at H
  have hpos (r : Time) : ∀ᵐ x ∂ν,0 ≤ linearDensity ε u v r x :=
    (linearDensity_bounds hε.le hB r.2 hu hv).mono fun _ hx => (sub_pos.mpr hεB).le.trans hx.1
  rw [integral_densityMeasure_lp' _ (hpos timeOne),integral_densityMeasure_lp' _ (hpos timeZero)] at H
  have hl : |⟪f,linearDensity ε u v timeOne⟫_ℝ-⟪f,linearDensity ε u v timeZero⟫_ℝ| =
      ε*|⟪f,u-v⟫_ℝ| := by
    simp only [linearDensity,timeOne,timeZero,one_smul,zero_smul,add_zero,
      inner_add_right,real_inner_smul_right,inner_sub_right]
    rw [show ⟪f,constLp 1⟫_ℝ+ε*(⟪f,u⟫_ℝ+(⟪f,v⟫_ℝ-⟪f,u⟫_ℝ))-
      (⟪f,constLp 1⟫_ℝ+ε*⟪f,u⟫_ℝ) = ε*(⟪f,v⟫_ℝ-⟪f,u⟫_ℝ) by ring]
    rw [abs_mul,abs_of_pos hε,abs_sub_comm]
  rw [hl] at H
  have hr : Real.sqrt (ε^2/(1-ε*B)*(t^2*‖D‖)^2) = ε*(t^2*‖D‖)/Real.sqrt (1-ε*B) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ ε^2/(1-ε*B)),Real.sqrt_div (sq_nonneg ε),
      Real.sqrt_sq hε.le,Real.sqrt_sq (by positivity : 0 ≤ t^2*‖D‖)]
    ring
  rw [hr] at H
  change ε*|⟪f,u-v⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖W‖*(ε*(t^2*‖D‖)/Real.sqrt (1-ε*B)) at H
  apply (mul_le_mul_iff_right₀ hε).mp
  calc
    ε*|⟪f,u-v⟫_ℝ| ≤ Real.sqrt (1+ε*B)*‖W‖*(ε*(t^2*‖D‖)/Real.sqrt (1-ε*B)) := H
    _ = ε*(Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B)) := by ring

lemma CurvatureDimension.prox_weak_pairing_centered {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (hmass : ∫ x,u x ∂ν = 0) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂ν,|u x| ≤ B) (hv : ∀ᵐ x ∂ν,|v x| ≤ B)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    |⟪f,u-v⟫_ℝ| ≤ t^2*‖D‖*‖W‖ := by
  have hc : ContinuousAt (fun ε : ℝ => Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B)) 0 := by
    fun_prop (disch := norm_num)
  have hl : Tendsto (fun ε : ℝ => Real.sqrt (1+ε*B)*‖W‖*(t^2*‖D‖)/Real.sqrt (1-ε*B))
      (𝓝[>] 0) (𝓝 (t^2*‖D‖*‖W‖)) := by
    simpa [mul_comm] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hl
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0,ε*B < 1 := by
    have H : Tendsto (fun ε : ℝ => ε*B) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0:ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds).mul_const B
    exact H.eventually_lt_const zero_lt_one
  filter_upwards [hb,self_mem_nhdsWithin] with ε hεB hε
  exact hcd.prox_weak_pairing_perturbed hν h hmass hε hB hεB hu hv hf
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ReLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology


namespace WeakHessianFunctional

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

lemma imLp_ae (f : Lp ℂ 2 m) : imLp m f =ᵐ[m] fun x => (f x).im :=
  Complex.imCLM.coeFn_compLpL f

end WeakHessianFunctional

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_LocalSlopeNotMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma cheegerEnergy_lipschitz_compact_lt_top [IsLocallyFiniteMeasure m]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    cheegerEnergy m f < ∞ := by
  have hm : MemLp f 2 m := hf.continuous.memLp_of_hasCompactSupport hc
  have he : (∫⁻ x, localSlope f x ^ 2 ∂m) < ∞ := by
    calc
      (∫⁻ x, localSlope f x ^ 2 ∂m) ≤ ∫⁻ x, (tsupport f).indicator (fun _ => (L:ℝ≥0∞)^2) x ∂m := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ tsupport f
        · rw [Set.indicator_of_mem hx]
          exact pow_le_pow_left' (localSlope_le_lipschitz hf x) 2
        · simp only [Set.indicator_of_notMem hx, localSlope_eq_zero_of_notMem_tsupport hx,
            zero_pow (by omega : (2:ℕ) ≠ 0), le_refl]
      _ = (L:ℝ≥0∞)^2 * m (tsupport f) := by
        rw [lintegral_indicator (isClosed_tsupport f).measurableSet, lintegral_const,
          Measure.restrict_apply_univ]
      _ < ∞ := ENNReal.mul_lt_top (by finiteness) hc.measure_lt_top
  have H := cheegerEnergy_le_liminf hm (fs := fun _ => f)
    (fun _ => ⟨⟨L,hf⟩, hm⟩) (by simp)
  rw [liminf_const] at H
  exact H.trans_lt (ENNReal.mul_lt_top (by norm_num) he)

end WeakHessian

open Set Filter
open scoped Topology ENNReal NNReal

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RelaxedDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set
open scoped NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

variable [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma relaxedDomain_dense [IsLocallyFiniteMeasure m] :
    (relaxedDomain m).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro H hH
  change H=0
  have hAE : (H : X → ℝ) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro φ hc hφ
    obtain ⟨L,hL⟩ := hφ
    have hm : MemLp φ 2 m := hL.continuous.memLp_of_hasCompactSupport hc
    have hd : hm.toLp φ ∈ relaxedDomain m := by
      have he : cheegerEnergy m (hm.toLp φ : X → ℝ) < ∞ := by
        rw [cheegerEnergy_congr_ae hm.coeFn_toLp]
        exact cheegerEnergy_lipschitz_compact_lt_top hL hc
      obtain ⟨D,hD,_⟩ := exists_relaxedGradient_energy_eq he
      exact ⟨D,hD⟩
    have hz := Submodule.inner_left_of_mem_orthogonal hd hH
    rw [L2.inner_def] at hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [Real.inner_apply, hx]
  apply Lp.ext
  exact hAE.trans (Lp.coeFn_zero ℝ 2 m).symm

lemma relaxedProx_tendsto [IsLocallyFiniteMeasure m] (u : Lp ℝ 2 m)
    (v D : ℕ → Lp ℝ 2 m) (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0))
    (h : ∀ n,RelaxedProx u (τ n) (v n) (D n)) : Tendsto v atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun n => ‖u-v n‖)
  · intro n
    rw [norm_sub_rev]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hd : Dense (relaxedDomain m : Set (Lp ℝ 2 m)) := by
    rw [dense_iff_closure_eq]
    exact congrArg (fun S : Submodule ℝ (Lp ℝ 2 m) => (S : Set (Lp ℝ 2 m)))
      (relaxedDomain_dense (m := m))
  obtain ⟨q,hq,hqdist⟩ := hd.exists_dist_lt u (by linarith : 0 < ε/2)
  obtain ⟨E,hE⟩ := hq
  have ht : Tendsto (fun n => ‖u-q‖^2+(τ n)^2*‖E‖^2) atTop (𝓝 (‖u-q‖^2)) := by
    simpa using tendsto_const_nhds.add ((hτ.pow 2).mul_const (‖E‖^2))
  have hsmall : ‖u-q‖^2 < ε^2 := by
    rw [dist_eq_norm] at hqdist
    nlinarith [norm_nonneg (u-q)]
  have hev := ht.eventually_lt_const hsmall
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,fun n hn => ?_⟩
  have HC := (h n).comparison hE
  have HH := hN n hn
  simp only [Real.dist_eq,sub_zero,abs_norm]
  nlinarith [mul_nonneg (sq_nonneg (τ n)) (sq_nonneg ‖D n‖),norm_nonneg (u-v n)]
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SubConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] {m : Measure X}
lemma CurvatureDimension.prox_weak_pairing {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (n : ℕ) (hu : ∀ᵐ x ∂ν,|u x| ≤ (n:ℝ))
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    |⟪f,u-v⟫_ℝ| ≤ t^2*‖D‖*‖W‖ := by
  let c := ∫ x,u x ∂ν
  have H := hcd.prox_weak_pairing_centered hν (h.sub_const c) (centeredLp_mass u)
    (by positivity : 0 ≤ (n:ℝ)+|c|) (centeredLp_bound hu c) (centeredLp_bound (h.bounded n hu) c) hf
  simpa only [sub_sub_sub_cancel_right] using H

lemma CurvatureDimension.prox_gradient_norm_le {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D W : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D) (ht : t ≠ 0)
    (n : ℕ) (hu : ∀ᵐ x ∂ν,|u x| ≤ (n:ℝ))
    (hf : IsLocalWeakUpperGradient ν (u : X → ℝ) (W : X → ℝ)) : ‖D‖ ≤ ‖W‖ := by
  have H := hcd.prox_weak_pairing hν h n hu hf
  rw [real_inner_comm] at H
  have HS := h.displacement
  have HP : 0 < t^2 := sq_pos_of_ne_zero ht
  have HD : t^2*‖D‖^2 ≤ t^2*(‖D‖*‖W‖) := by
    have HA := le_abs_self ⟪u-v,u⟫_ℝ
    nlinarith [sq_nonneg ‖u-v‖]
  have HN := (mul_le_mul_iff_right₀ HP).mp HD
  nlinarith [norm_nonneg D,norm_nonneg W]
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CongrAeLeft
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian

section UpperGradientCongruence
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
lemma IsLocalWeakUpperGradient.congr_ae_left {f g D : X → ℝ}
    (hf : IsLocalWeakUpperGradient m f D) (hfg : f =ᵐ[m] g) :
    IsLocalWeakUpperGradient m g D := by
  refine ⟨hf.1,hf.2.1,fun π hπ hb => ?_⟩
  have he : (fun γ : Curve X => ENNReal.ofReal |f (γ timeOne)-f (γ timeZero)|)
      =ᵐ[π] (fun γ : Curve X => ENNReal.ofReal |g (γ timeOne)-g (γ timeZero)|) := by
    filter_upwards [hπ.ae_eval_of_ae hfg timeOne,hπ.ae_eval_of_ae hfg timeZero] with γ h1 h0
    rw [h1,h0]
  rw [← lintegral_congr_ae he]
  exact hf.2.2 π hπ hb

omit [BorelSpace X] in
lemma IsLocalWeakUpperGradient.normalContraction {f D : X → ℝ}
    (hf : IsLocalWeakUpperGradient m f D) {η : ℝ → ℝ} (hη : LipschitzWith 1 η) :
    IsLocalWeakUpperGradient m (η ∘ f) D := by
  refine ⟨hf.1,hf.2.1,fun π hπ hb => ?_⟩
  apply le_trans (lintegral_mono (fun γ => ?_)) (hf.2.2 π hπ hb)
  apply ENNReal.ofReal_le_ofReal
  simpa only [Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul] using
    hη.dist_le_mul (f (γ timeOne)) (f (γ timeZero))

end UpperGradientCongruence

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.reference_cheegerEnergy_le_weak_bounded {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ))
    (k : ℕ) (hfb : ∀ᵐ x ∂ν,|f x| ≤ (k:ℝ)) :
    cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖W‖^2/2) := by
  choose v D h using fun n : ℕ => exists_relaxedProx f (t := 1/((n:ℝ)+1)) (by positivity)
  have hconv : Tendsto v atTop (𝓝 f) :=
    relaxedProx_tendsto f v D _ tendsto_one_div_add_atTop_nhds_zero_nat h
  apply (lowerSemicontinuous_cheegerEnergy.isClosed_preimage (ENNReal.ofReal (‖W‖^2/2))).mem_of_tendsto hconv
  apply Eventually.of_forall
  intro n
  have H := hcd.prox_gradient_norm_le hν (h n) (by positivity) k hfb hf
  exact (relaxedGraph_energy_le (h n).graph).trans (ENNReal.ofReal_le_ofReal (by
    change ‖D n‖^2/2 ≤ ‖W‖^2/2
    nlinarith [norm_nonneg (D n),norm_nonneg W]))

lemma CurvatureDimension.reference_cheegerEnergy_le_weak {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖W‖^2/2) := by
  let fn : ℕ → Lp ℝ 2 ν := fun n => (realClip_lipschitz n).compLp (realClip_zero n) f
  have hw (n : ℕ) : IsLocalWeakUpperGradient ν (fn n : X → ℝ) (W : X → ℝ) :=
    (hf.normalContraction (realClip_lipschitz n)).congr_ae_left
      ((realClip_lipschitz n).coeFn_compLp (realClip_zero n) f).symm
  have hb (n : ℕ) : ∀ᵐ x ∂ν,|fn n x| ≤ (n:ℝ) := by
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) f] with x hx
    rw [show fn n x = realClip n (f x) from hx]
    exact realClip_abs_le n (f x)
  exact (lowerSemicontinuous_cheegerEnergy.isClosed_preimage
    (ENNReal.ofReal (‖W‖^2/2))).mem_of_tendsto (realClip_tendsto_Lp f)
      (Eventually.of_forall fun n => hcd.reference_cheegerEnergy_le_weak_bounded hν (hw n) n (hb n))
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_UpperGradientTendstoNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian

open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.reference_relaxedGradient_isMinimal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f D : Lp ℝ 2 ν} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph ν)
    (he : cheegerEnergy ν (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (D : X → ℝ) := by
  apply norm_minimal_is_minimal (relaxedGraph_isUpperGradient (fun B _ => measure_lt_top ν B) hD)
  intro E hE
  change IsLocalWeakUpperGradient ν (f : X → ℝ) (E : X → ℝ) at hE
  change ‖D‖ ≤ ‖E‖
  have H := hcd.reference_cheegerEnergy_le_weak hν hE
  rw [he] at H
  have HR : ‖D‖^2/2 ≤ ‖E‖^2/2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
  nlinarith [norm_nonneg D,norm_nonneg E]

lemma CurvatureDimension.reference_exists_relaxedGradient_le {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    ∃ D : Lp ℝ 2 ν,WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph ν ∧
      (∀ᵐ x ∂ν,0 ≤ D x ∧ D x ≤ W x) := by
  have he := hcd.reference_cheegerEnergy_le_weak hν hf
  obtain ⟨D,hD,_hmin,he⟩ := exists_relaxedGradient_energy_eq (he.trans_lt ENNReal.ofReal_lt_top)
  have hm := hcd.reference_relaxedGradient_isMinimal hν hD he
  exact ⟨D,hD,hm.1.2.1.and (hm.2 W hf)⟩
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CutoffCheegerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X} [IsProbabilityMeasure ν]

lemma CurvatureDimension.cutoff_cheegerEnergy_le {K N : ℝ}
    (hcd : CurvatureDimension m K N) {C : ℝ≥0} (hν : ν ≤ (C:ℝ≥0∞) • m) (hm : m ≪ ν)
    {f W : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (W : X → ℝ))
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hφ0 : ∀ x,0 ≤ φ x) (hφ1 : ∀ x,φ x ≤ 1) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict (tsupport φ) ≤ c • ν) :
    cheegerEnergy m (boundedMulLp hφ.continuous.aestronglyMeasurable
      (ae_of_all m (fun x => by rw [abs_of_nonneg (hφ0 x)]; exact hφ1 x)) f : X → ℝ) ≤
      ENNReal.ofReal ((‖W‖+(L:ℝ)*‖f‖)^2/2) := by
  let J := Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) ENNReal.coe_ne_top hν
  have hJ (u : Lp ℝ 2 m) : J u =ᵐ[ν] (u : X → ℝ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν u
  have hweak : IsLocalWeakUpperGradient ν (J f : X → ℝ) (J W : X → ℝ) :=
    (hf.of_measure_le_smul hν).congr_ae (hJ f).symm (hJ W).symm
  obtain ⟨D,hD,hDW⟩ := hcd.reference_exists_relaxedGradient_le
    (Measure.absolutelyContinuous_of_le_smul hν) hweak
  have hφB : ∀ x,|φ x| ≤ 1 := fun x => by rw [abs_of_nonneg (hφ0 x)]; exact hφ1 x
  let T := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB)
  let S := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ (localSlope_toReal_bound hφ))
  have hT (u : Lp ℝ 2 ν) : T u =ᵐ[m] (fun x => u x*φ x) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => image_eq_zero_of_notMem_tsupport hx) u
  have hS (u : Lp ℝ 2 ν) : S u =ᵐ[m] (fun x => u x*(localSlope φ x).toReal) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => by
      rw [localSlope_zero_of_notMem_tsupport hx,ENNReal.toReal_zero]) u
  have hTD : ‖T D‖ ≤ ‖W‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hT D,hm.ae_le hDW,hm.ae_le (hJ W)] with x hx hD hW
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hD.1 (hφ0 x))]
    calc D x*φ x ≤ D x*1 := mul_le_mul_of_nonneg_left (hφ1 x) hD.1
         _ = D x := mul_one _
         _ ≤ W x := hW ▸ hD.2
         _ ≤ ‖W x‖ := le_abs_self _
  have hSf : ‖S (realAbs_lipschitz.compLp abs_zero (J f))‖ ≤ (L:ℝ)*‖f‖ := by
    calc
      _ ≤ ‖(L:ℝ) • f‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [hS (realAbs_lipschitz.compLp abs_zero (J f)),
          hm.ae_le (realAbs_lipschitz.coeFn_compLp abs_zero (J f)),
          hm.ae_le (hJ f),Lp.coeFn_smul (L:ℝ) f] with x hx hab hfx hsm
        rw [hx,hab,Function.comp_apply,hfx,hsm]
        simp only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_abs,
          abs_of_nonneg (ENNReal.toReal_nonneg),abs_of_nonneg L.coe_nonneg]
        calc |f x| *(localSlope φ x).toReal ≤ |f x| *(L:ℝ) :=
               mul_le_mul_of_nonneg_left ((le_abs_self _).trans (localSlope_toReal_bound hφ x)) (abs_nonneg _)
             _ = (L:ℝ)*|f x| := mul_comm _ _
      _ = (L:ℝ)*‖f‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg L.coe_nonneg]
  have hnorm : ‖T D+S (realAbs_lipschitz.compLp abs_zero (J f))‖ ≤ ‖W‖+(L:ℝ)*‖f‖ :=
    (norm_add_le _ _).trans (add_le_add hTD hSf)
  have hgraph := relaxedGraph_localized hφ hcφ hφ0 hφB hc hlocal hD
  have he : T (J f) = boundedMulLp hφ.continuous.aestronglyMeasurable (ae_of_all m hφB) f := by
    apply Lp.ext
    filter_upwards [hT (J f),hm.ae_le (hJ f),
      boundedMulLp_ae hφ.continuous.aestronglyMeasurable (ae_of_all m hφB) f] with x hx hy hz
    rw [hx,hy,hz]
  have HE := relaxedGraph_energy_le hgraph
  change cheegerEnergy m (T (J f) : X → ℝ) ≤
    ENNReal.ofReal (‖T D+S (realAbs_lipschitz.compLp abs_zero (J f))‖^2/2) at HE
  rw [he] at HE
  exact HE.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm) (by norm_num)))
end WeakHessian

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end


