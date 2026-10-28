-- Prove2me | Definitions.Def_OAIQ52Wh001
-- name    : OAIQ52Wh001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:39:41.807265+00:00
-- url     : https://prove2.me/theorems/735828bf-cc83-4155-823e-4cffd212acd6
-- title:
--   Definitions bundle OAIQ52Wh001 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 237 declarations of OpenAI's Lean: 30 definitions, 2 inductive types or structures and 205 theorems. The definitions and types are `OAI.WeakHessian.RelaxedProx`, `OAI.WeakHessian.affineHomeomorph`, `OAI.WeakHessian.boundedMulLp`, `OAI.WeakHessian.constLp`, `OAI.WeakHessian.cutoffChangeLp`, `OAI.WeakHessian.l2GradientGraph`, `OAI.WeakHessian.l2RelaxedGraph`, `OAI.WeakHessian.l2SlopeGraph`, `OAI.WeakHessian.linearDensity`, `OAI.WeakHessian.localizedSlopeGraphMap`, `OAI.WeakHessian.radialCutoff`, `OAI.WeakHessian.relaxedDomain`, `OAI.WeakHessian.slopeApprox`, `OAI.WeakHessian.speedApprox`, `OAI.WeakHessian.zeroExtendLp`, `OAI.WeakHessianCalculus.runningMin`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy`, `OAI.WeakHessianFunctional.energyPolar`, `OAI.WeakHessianFunctional.imLp`, `OAI.WeakHessianFunctional.realClip`, `OAI.WeakHessianTransport.ballCutoff`, `OAI.WeakHessianTransport.boundedIntegral`, `OAI.WeakHessianTransport.boundedMarginalIntegral`, `OAI.WeakHessianTransport.boundedMarginalSum`, `OAI.WeakHessianTransport.boundedMulCompact`, `OAI.WeakHessianTransport.compactTensor`, `OAI.WeakHessianTransport.compactToBounded`, `OAI.WeakHessianTransport.densityMeasure`, `OAI.WeakHessianTransport.densityProbability`, `OAI.WeakHessianTransport.joinControl`, `OAI.WeakHessianTransport.truncatedQuadraticCost`, `OAI.WeakHessianTransport.upperEnvelope`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_CompactThickenedIndicator`, `WeakHessian_Calculus_ELpNormSq`, `WeakHessian_Calculus_LipschitzMulCompact`, `WeakHessian_Calculus_NormSqLintegralEnorm`, `WeakHessian_Entropy_IntegralDensityMeasureLp'`, `WeakHessian_Entropy_LinearDensity`, `WeakHessian_Entropy_NonnegativeParallelogram`, `WeakHessian_LocalBounds_AbsolutelyContinuousDistDom`, `WeakHessian_LocalBounds_AffineTime`, `WeakHessian_LocalBounds_BoundedMulLp`, `WeakHessian_LocalBounds_BoundedMulLpTendsto`, `WeakHessian_LocalBounds_ClampTimeVal`, `WeakHessian_LocalBounds_ClosedQuadraticEnergy`, `WeakHessian_LocalBounds_ConstLp`, `WeakHessian_LocalBounds_EvalRealCoe`, `WeakHessian_LocalBounds_ExtendLp`, `WeakHessian_LocalBounds_InclusionDoubleDualSurjective`, `WeakHessian_LocalBounds_L2SlopeGraph`, `WeakHessian_LocalBounds_LocalizedSlopeGraphMap`, `WeakHessian_LocalBounds_ReLp`, `WeakHessian_LocalBounds_RealClip`, `WeakHessian_LocalBounds_RelaxedDomain`, `WeakHessian_LocalBounds_RelaxedProx`, `WeakHessian_LocalBounds_RunningMin`, `WeakHessian_LocalBounds_SlopeApprox`, `WeakHessian_LocalBounds_SlopeApproxAntitone`, `WeakHessian_LocalBounds_SlopeApproxProduct`, `WeakHessian_LocalBounds_SpeedApprox`, `WeakHessian_LocalBounds_SquareControl`, `WeakHessian_LocalBounds_SubConst`, `WeakHessian_Measure_AeMinimumDominated`, `WeakHessian_Measure_InlinedFile0`, `WeakHessian_Measure_LocalSlopeNotMem`, `WeakHessian_Measure_RadialCutoff`, `WeakHessian_Sobolev_CheegerEnergyCongrAe`, `WeakHessian_Sobolev_L2GradientGraph`, `WeakHessian_Transport_ActionIntervalIntegrable`, `WeakHessian_Transport_AeEvalAe`, `WeakHessian_Transport_BoundedHopfMap`, `WeakHessian_Transport_BoundedMarginalSum`, `WeakHessian_Transport_CompactBounded`, `WeakHessian_Transport_DensityMeasure`, `WeakHessian_Transport_DualTransportPairing`, `WeakHessian_Transport_HopfMap`, `WeakHessian_Transport_JoinControl`, `WeakHessian_Transport_KineticAction`, `WeakHessian_Transport_LocalSlopeCompContraction`, `WeakHessian_Transport_MapEvalReal`, `WeakHessian_Transport_ProbabilityTightMarginals`, `WeakHessian_Transport_RestrictCurve`, `WeakHessian_Transport_TruncatedQuadraticCost`, `WeakHessian_Transport_UpperEnvelope`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ52Wh003` and `OAIQ52Wh004`; the statements `OAI.WeakHessian.RCD.compact_core_localized_pairing` and `OAI.WeakHessian.RCD.generator_entropy_subdifferential`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactThickenedIndicator
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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianCalculus
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma compact_thickenedIndicator {s : Set X} (hs : IsCompact s) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  have hc : IsCompact (Metric.cthickening δ s) := hs.cthickening
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  apply Metric.thickening_subset_cthickening δ s
  by_contra h
  exact hx (by simp only [thickenedIndicator_zero hδ s h, NNReal.coe_zero])

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_thickenedIndicator {s : Set X} {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith δ.toNNReal⁻¹ (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  exact NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator hδ s) |>.weaken
    (by simp)

lemma ae_eq_zero_of_integral_lipschitz_compact {H : X → ℝ}
    (hH : LocallyIntegrable H m)
    (hzero : ∀ φ : X → ℝ, HasCompactSupport φ →
      (∃ L : ℝ≥0, LipschitzWith L φ) → (∫ x, H x * φ x ∂m) = 0) :
    H =ᵐ[m] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hH
  intro s hs
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by dsimp only [δ]; positivity
  let φ : ℕ → X → ℝ := fun n x => thickenedIndicator (hδ n) s x
  have hφc : ∀ n, Continuous (φ n) := fun n => (lipschitz_thickenedIndicator (hδ n)).continuous
  have hφzero : ∀ n, (∫ x, H x * φ n x ∂m) = 0 := fun n =>
    hzero _ (compact_thickenedIndicator hs (hδ n)) ⟨_,lipschitz_thickenedIndicator (hδ n)⟩
  have hφbound : ∀ n x, |φ n x| ≤ 1 := by
    intro n x
    simpa only [φ, abs_of_nonneg (NNReal.coe_nonneg _), NNReal.coe_one] using
      (NNReal.coe_le_coe.mpr (thickenedIndicator_le_one (hδ n) s x))
  have hδle : ∀ n, δ n ≤ 1 := fun n => by
    dsimp only [δ]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let c : Set X := Metric.cthickening 1 s
  have hc : IsCompact c := hs.cthickening
  have hφout : ∀ n x, x ∉ c → φ n x = 0 := by
    intro n x hx
    have hx' : x ∉ Metric.thickening (δ n) s := fun h =>
      hx (Metric.cthickening_mono (hδle n) s (Metric.thickening_subset_cthickening (δ n) s h))
    simp only [φ, thickenedIndicator_zero (hδ n) s hx', NNReal.coe_zero]
  have hlimφ : ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℝ)) x)) := by
    intro x
    have h := (tendsto_pi_nhds.mp
      (thickenedIndicator_tendsto_indicator_closure hδ tendsto_one_div_add_atTop_nhds_zero_nat s)) x
    have h' := NNReal.continuous_coe.continuousAt.tendsto.comp h
    by_cases hx : x ∈ s <;> simpa [hs.isClosed.closure_eq, φ, hx, Function.comp_def] using h'
  have hm : ∀ n, AEStronglyMeasurable (fun x => H x * φ n x) m :=
    fun n => hH.aestronglyMeasurable.mul (hφc n).aestronglyMeasurable
  have hdom : Integrable (c.indicator (fun x => |H x|)) m :=
    (integrable_indicator_iff hc.measurableSet).mpr (by
      change Integrable (fun x => |H x|) (m.restrict c)
      simpa only [Real.norm_eq_abs] using (hH.integrableOn_isCompact hc).norm)
  have hlim := tendsto_integral_of_dominated_convergence (c.indicator (fun x => |H x|)) hm hdom
    (fun n => ae_of_all _ fun x => by
      by_cases hx : x ∈ c
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hφbound n x)
      · simp only [hφout n x hx, mul_zero, norm_zero, Set.indicator_of_notMem hx, le_rfl])
    (ae_of_all _ fun x => tendsto_const_nhds.mul (hlimφ x))
  have heq : (fun x => H x * s.indicator (fun _ => (1 : ℝ)) x) = s.indicator H := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq, integral_indicator hs.measurableSet] at hlim
  exact (tendsto_nhds_unique (by simpa only [hφzero] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))) hlim).symm

end WeakHessianCalculus

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

lemma IsTestPlan.of_measure_le_smul {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) {C : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) :
    IsTestPlan ν π := by
  obtain ⟨hp, ⟨D, hD⟩, hac, he⟩ := hπ
  refine ⟨hp, ⟨D*C, fun t => ?_⟩, hac, he⟩
  calc
    Measure.map (fun γ : Curve X => γ t) π ≤ (D : ℝ≥0∞) • m := hD t
    _ ≤ (D : ℝ≥0∞) • ((C : ℝ≥0∞) • ν) :=
      by gcongr
    _ = ((D*C : ℝ≥0) : ℝ≥0∞) • ν := by rw [smul_smul, ENNReal.coe_mul]

lemma LocallyL2.of_measure_le_smul {f : X → ℝ} (hf : LocallyL2 m f)
    {C : ℝ≥0} (hν : ν ≤ (C : ℝ≥0∞) • m) : LocallyL2 ν f := by
  intro o R hR
  exact MemLp.of_measure_le_smul (c := (C : ℝ≥0∞)) ENNReal.coe_ne_top
    (by simpa only [Measure.restrict_smul] using
      Measure.restrict_mono_measure hν (Metric.ball o R)) (hf o R hR)

lemma IsLocalWeakUpperGradient.of_measure_le_smul {D : ℝ≥0}
    (hν : ν ≤ (D : ℝ≥0∞) • m)
    {f W : X → ℝ} (hw : IsLocalWeakUpperGradient m f W) :
    IsLocalWeakUpperGradient ν f W := by
  refine ⟨hw.1.of_measure_le_smul hν,
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le hw.2.1, ?_⟩
  intro π hπ hb
  exact hw.2.2 π (hπ.of_measure_le_smul hν) hb

omit [MeasurableSpace X] [BorelSpace X] in

lemma absolutelyContinuous_of_dist_le {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ s ∈ Set.uIcc a b, ∀ t ∈ Set.uIcc a b,
      dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hsmall => lt_of_le_of_lt ?_ (hbound E hE hsmall)⟩
  refine Finset.sum_le_sum fun i hi => ?_
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

omit [MeasurableSpace X] [BorelSpace X] in

lemma lipschitz_comp_absolutelyContinuous {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  change Tendsto _ _ (𝓝 0) at hf ⊢
  have hlim := hf.const_mul (L : ℝ)
  simp only [mul_zero] at hlim
  refine squeeze_zero (fun E => Finset.sum_nonneg fun i _ => dist_nonneg)
    (fun E => ?_) hlim
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hg.dist_le_mul _ _

lemma lintegral_lt_top_of_square {a : ℝ → ℝ≥0∞} (_ha : Measurable a)
    (hfinite : (∫⁻ t in Set.Icc (0 : ℝ) 1, (a t) ^ 2) < ∞) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1, a t) < ∞ := by
  have hpoint : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
    intro x
    by_cases hx : x ≤ 1
    · exact hx.trans (le_add_right le_rfl)
    · have hx' : 1 ≤ x := le_of_not_ge hx
      calc
        x = x * 1 := (mul_one x).symm
        _ ≤ x * x := by gcongr
        _ ≤ 1 + x ^ 2 := by rw [pow_two]; exact le_add_left le_rfl
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) 1, a t) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, 1 + (a t) ^ 2 :=
      lintegral_mono fun t => hpoint (a t)
    _ = (∫⁻ _t in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞)) +
        ∫⁻ t in Set.Icc (0 : ℝ) 1, (a t) ^ 2 :=
      lintegral_add_left measurable_const _
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨by simp, hfinite⟩

omit [MeasurableSpace X] [BorelSpace X] in

lemma IsAC2.absolutelyContinuous {γ : Curve X} (hγ : IsAC2 γ) :
    AbsolutelyContinuousOnInterval (evalReal γ) 0 1 := by
  obtain ⟨a, ha, hfinite, hinc⟩ := hγ
  have hfin : (∫⁻ t in Set.Icc (0 : ℝ) 1, a t) < ∞ :=
    lintegral_lt_top_of_square ha hfinite
  have hane : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), a t ≠ ∞ :=
    (ae_lt_top ha hfin.ne).mono fun _ h => h.ne
  have hai : IntegrableOn (fun t => (a t).toReal) (Set.Icc (0 : ℝ) 1) :=
    (integrable_toReal_iff ha.aemeasurable hane).mpr hfin.ne
  have haint : IntervalIntegrable (fun t => (a t).toReal) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hai
  let A : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, (a r).toReal
  have hA : AbsolutelyContinuousOnInterval A 0 1 :=
    haint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have heval (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      evalReal γ t = γ ⟨t, ht⟩ := by
    change γ (clampTime t) = γ ⟨t, ht⟩
    apply congrArg γ
    apply Subtype.ext
    simp only [clampTime, max_eq_right ht.1, min_eq_right ht.2]
  have hdom (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
      (ht : t ∈ Set.Icc (0 : ℝ) 1) (hst : s ≤ t) :
      dist (evalReal γ s) (evalReal γ t) ≤ dist (A s) (A t) := by
    have hstsub : Set.Icc s t ⊆ Set.Icc (0 : ℝ) 1 :=
      fun r hr => ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    have hstfin : (∫⁻ r in Set.Icc s t, a r) ≠ ∞ :=
      ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hstsub)
    have hstreal : (∫⁻ r in Set.Icc s t, a r).toReal = ∫ r in s..t, (a r).toReal := by
      rw [← integral_toReal ha.aemeasurable (ae_lt_top ha hstfin),
        integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
    have hDs : IntervalIntegrable (fun r => (a r).toReal) volume 0 s :=
      haint.mono_set (by simpa only [Set.uIcc_of_le hs.1, Set.uIcc_of_le zero_le_one]
        using (show Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) 1 from
          fun r hr => ⟨hr.1, hr.2.trans hs.2⟩))
    have hDt : IntervalIntegrable (fun r => (a r).toReal) volume 0 t :=
      haint.mono_set (by simpa only [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
        using (show Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 1 from
          fun r hr => ⟨hr.1, hr.2.trans ht.2⟩))
    have hprim : A t - A s = ∫ r in s..t, (a r).toReal :=
      intervalIntegral.integral_interval_sub_left hDt hDs
    rw [heval s hs, heval t ht]
    calc
      dist (γ ⟨s, hs⟩) (γ ⟨t, ht⟩) ≤ (∫⁻ r in Set.Icc s t, a r).toReal := by
        simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
          ENNReal.toReal_mono hstfin (hinc ⟨s, hs⟩ ⟨t, ht⟩ hst)
      _ = A t - A s := hstreal.trans hprim.symm
      _ ≤ dist (A s) (A t) := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _
  apply absolutelyContinuous_of_dist_le hA
  intro s hs t ht
  rw [Set.uIcc_of_le zero_le_one] at hs ht
  rcases le_total s t with hst | hts
  · exact hdom s t hs ht hst
  · simpa only [dist_comm] using hdom t s ht hs hts

lemma LocallyL2.const_mul {f : X → ℝ} (hf : LocallyL2 m f) (c : ℝ) :
    LocallyL2 m (fun x => c * f x) :=
  fun o R hR => (hf o R hR).const_mul c

lemma isLocalWeakUpperGradient_const (c : ℝ) :
    IsLocalWeakUpperGradient m (fun _ => c) (fun _ => 0) := by
  refine ⟨fun _ _ _ => ?_, ae_of_all m fun _ => le_rfl, ?_⟩
  · exact MemLp.zero
  · intro π _hπ _hb
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le

lemma isMinimalLocalWeakUpperGradient_const (c : ℝ) :
    IsMinimalLocalWeakUpperGradient m (fun _ => c) (fun _ => 0) :=
  ⟨isLocalWeakUpperGradient_const c, fun _ hD => hD.2.1⟩

lemma IsMinimalLocalWeakUpperGradient.ae_eq {f D D' : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D)
    (hD' : IsMinimalLocalWeakUpperGradient m f D') : D =ᵐ[m] D' := by
  filter_upwards [hD.2 _ hD'.1, hD'.2 _ hD.1] with x hx hx'
  exact le_antisymm hx hx'

lemma IsLocalWeakUpperGradient.const_mul {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (c : ℝ) :
    IsLocalWeakUpperGradient m (fun x => c * f x) (fun x => |c| * D x) := by
  refine ⟨hD.1.const_mul |c|, ?_, ?_⟩
  · filter_upwards [hD.2.1] with x hx
    exact mul_nonneg (abs_nonneg c) hx
  · intro π hπ hb
    calc
      (∫⁻ γ : Curve X, ENNReal.ofReal |c * f (γ timeOne) - c * f (γ timeZero)| ∂π) =
          ENNReal.ofReal |c| * ∫⁻ γ : Curve X,
            ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π := by
        simp_rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal |c| * ∫⁻ γ : Curve X, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π := by
        gcongr 1
        exact hD.2.2 π hπ hb
      _ = ∫⁻ γ : Curve X, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (|c| * D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π := by
        simp_rw [ENNReal.ofReal_mul (abs_nonneg c), mul_assoc,
          lintegral_const_mul' (ENNReal.ofReal |c|) _ ENNReal.ofReal_ne_top]

lemma IsMinimalLocalWeakUpperGradient.const_mul {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) {c : ℝ} (hc : c ≠ 0) :
    IsMinimalLocalWeakUpperGradient m (fun x => c * f x) (fun x => |c| * D x) := by
  refine ⟨hD.1.const_mul c, ?_⟩
  intro D' hD'
  have hinv := hD'.const_mul c⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hinv
  filter_upwards [hD.2 _ hinv] with x hx
  calc
    |c| * D x ≤ |c| * (|c⁻¹| * D' x) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    _ = D' x := by rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_AeEvalAe
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

lemma IsTestPlan.ae_eval_of_ae {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {p : X → Prop} (hp : ∀ᵐ x ∂m, p x) (t : Time) :
    ∀ᵐ γ ∂π, p (γ t) := by
  obtain ⟨C, hC⟩ := hπ.2.1
  exact ae_of_ae_map (continuous_eval_const t).measurable.aemeasurable
    ((Measure.absolutelyContinuous_of_le_smul (hC t)).ae_le hp)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_clampTime : Continuous clampTime := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_evalReal : Continuous (fun p : Curve X × ℝ => evalReal p.1 p.2) := by
  exact continuous_eval.comp (continuous_fst.prodMk (continuous_clampTime.comp continuous_snd))

lemma IsTestPlan.ae_ae_eval_of_ae {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {p : X → Prop} (hp : ∀ᵐ x ∂m, p x) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), p (evalReal γ t) := by
  let S := toMeasurable m {x | ¬ p x}
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hSzero : m S = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hp
  have hSae : ∀ᵐ x ∂m, x ∉ S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hSzero
  let : IsProbabilityMeasure π := hπ.1
  have hpath : ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      evalReal γ t ∉ S := by
    apply (Measure.ae_ae_comm (p := fun γ t => evalReal γ t ∉ S)
      (hSm.compl.preimage continuous_evalReal.measurable)).mpr
    exact ae_of_all _ fun t => hπ.ae_eval_of_ae hSae (clampTime t)
  filter_upwards [hpath] with γ hγ
  filter_upwards [hγ] with t ht
  by_contra hn
  exact ht (subset_toMeasurable m {x | ¬ p x} hn)

omit [BorelSpace X] in
lemma LocallyL2.ae_eq {f g : X → ℝ} (hf : LocallyL2 m f) (hfg : f =ᵐ[m] g) :
    LocallyL2 m g := by
  intro o R hR
  exact (hf o R hR).ae_eq (ae_restrict_of_ae hfg)

lemma IsLocalWeakUpperGradient.congr_ae {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hfg : f =ᵐ[m] g) (hDE : D =ᵐ[m] E) :
    IsLocalWeakUpperGradient m g E := by
  refine ⟨hD.1.ae_eq hDE, ?_, ?_⟩
  · filter_upwards [hD.2.1, hDE] with x hx hxe
    rwa [← hxe]
  · intro π hπ hb
    have hend : (fun γ : Curve X => ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)|)
        =ᵐ[π] (fun γ : Curve X => ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)|) := by
      filter_upwards [hπ.ae_eval_of_ae hfg timeOne, hπ.ae_eval_of_ae hfg timeZero]
        with γ h1 h0
      rw [h1, h0]
    have hpath : (fun γ : Curve X => ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t)
        =ᵐ[π] (fun γ : Curve X => ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t) := by
      filter_upwards [hπ.ae_ae_eval_of_ae hDE] with γ hγ
      apply lintegral_congr_ae
      filter_upwards [hγ] with t ht
      rw [ht]
    rw [← lintegral_congr_ae hend, ← lintegral_congr_ae hpath]
    exact hD.2.2 π hπ hb

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

def speedApprox (n : ℕ) (p : Curve X × ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : h ≠ 0 ∧ |h| < 1 / (n + 1 : ℝ)),
    ENNReal.ofReal (dist (evalReal p.1 (p.2 + h)) (evalReal p.1 p.2) / |h|)

omit [MeasurableSpace X] [BorelSpace X] in
lemma metricSpeed_eq_iInf_speedApprox (γ : Curve X) (t : ℝ) :
    metricSpeed γ t = ⨅ n : ℕ, speedApprox n (γ, t) := by
  rw [metricSpeed, nhdsWithin,
    ((Metric.nhds_basis_ball_inv_nat_succ (x := t)).inf_principal ({t}ᶜ)).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  apply iInf_congr
  intro n
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    rintro ⟨hs, hst⟩
    have hne : s - t ≠ 0 := sub_ne_zero.mpr hst
    have hlt : |s - t| < 1 / (n + 1 : ℝ) := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
    calc
      ENNReal.ofReal (dist (evalReal γ s) (evalReal γ t) / |s - t|) =
          ENNReal.ofReal (dist (evalReal γ (t + (s - t))) (evalReal γ t) / |s - t|) := by
        rw [show t + (s - t) = s by ring]
      _ ≤ speedApprox n (γ, t) := le_iSup_of_le (s - t) (le_iSup_of_le ⟨hne, hlt⟩ le_rfl)
  · apply iSup_le
    intro h
    apply iSup_le
    rintro ⟨hne, hlt⟩
    have hball : t + h ∈ Metric.ball t (1 / (n + 1 : ℝ)) := by
      simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left] using hlt
    have hne' : t + h ∈ ({t}ᶜ : Set ℝ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun heq => hne (by linarith)
    apply le_iSup_of_le (t + h)
    apply le_iSup_of_le (show t + h ∈ Metric.ball t (1 / (n + 1 : ℝ)) ∩ {t}ᶜ from
      ⟨hball, hne'⟩)
    simp only [add_sub_cancel_left, le_refl]

omit [MeasurableSpace X] [BorelSpace X] in
lemma lowerSemicontinuous_speedApprox (n : ℕ) :
    LowerSemicontinuous (speedApprox (X := X) n) := by
  apply lowerSemicontinuous_biSup
  intro h _hh
  apply Continuous.lowerSemicontinuous
  apply ENNReal.continuous_ofReal.comp
  exact ((continuous_evalReal.comp (continuous_fst.prodMk (continuous_snd.add_const h))).dist
    continuous_evalReal).div_const |h|

omit [MeasurableSpace X] [BorelSpace X] in
lemma measurable_metricSpeed : Measurable (fun p : Curve X × ℝ => metricSpeed p.1 p.2) := by
  simp_rw [metricSpeed_eq_iInf_speedApprox]
  exact Measurable.iInf fun n => (lowerSemicontinuous_speedApprox n).measurable

omit [BorelSpace X] in

lemma LocallyL2.aestronglyMeasurable {f : X → ℝ} (hf : LocallyL2 m f) :
    AEStronglyMeasurable f m := by
  cases isEmpty_or_nonempty X with
  | inl h => exact (measurable_of_empty f).aestronglyMeasurable
  | inr h =>
    obtain ⟨o⟩ := h
    have hm : AEStronglyMeasurable f (m.restrict (⋃ n : ℕ, Metric.ball o (n + 1))) :=
      AEStronglyMeasurable.iUnion fun n =>
        (hf o (n + 1) (by positivity)).aestronglyMeasurable
    simpa only [Metric.iUnion_ball_nat_succ, Measure.restrict_univ] using hm

omit [BorelSpace X] in
lemma LocallyL2.aemeasurable {f : X → ℝ} (hf : LocallyL2 m f) :
    AEMeasurable f m := hf.aestronglyMeasurable.aemeasurable

lemma IsTestPlan.ae_prod_eval_of_ae {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {p : X → Prop} (hp : ∀ᵐ x ∂m, p x) :
    ∀ᵐ z ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)), p (evalReal z.1 z.2) := by
  let S := toMeasurable m {x | ¬ p x}
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  have hSzero : m S = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hp
  have hSae : ∀ᵐ x ∂m, x ∉ S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hSzero
  let : IsProbabilityMeasure π := hπ.1
  have hh : ∀ᵐ z ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)),
      evalReal z.1 z.2 ∉ S :=
    (Measure.ae_prod_iff_ae_ae
      (hSm.compl.preimage continuous_evalReal.measurable)).mpr (hπ.ae_ae_eval_of_ae hSae)
  filter_upwards [hh] with z hz
  by_contra hn
  exact hz (subset_toMeasurable m {x | ¬ p x} hn)

lemma IsTestPlan.aemeasurable_evalReal {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) :
    AEMeasurable (fun z : Curve X × ℝ => f (evalReal z.1 z.2))
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
  exact ((hf.measurable_mk.comp continuous_evalReal.measurable).aemeasurable).congr
    (Filter.EventuallyEq.symm (hπ.ae_prod_eval_of_ae hf.ae_eq_mk))

lemma IsTestPlan.aemeasurable_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : AEMeasurable f m) (t : Time) :
    AEMeasurable (fun γ : Curve X => f (γ t)) π := by
  exact ((hf.measurable_mk.comp (continuous_eval_const t).measurable).aemeasurable).congr
    (Filter.EventuallyEq.symm (hπ.ae_eval_of_ae hf.ae_eq_mk t))

lemma IsTestPlan.aemeasurable_action {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {D : X → ℝ} (hD : LocallyL2 m D) :
    AEMeasurable (fun z : Curve X × ℝ =>
      ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2)
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
  ((hπ.aemeasurable_evalReal hD.aemeasurable).ennreal_ofReal).mul
    measurable_metricSpeed.aemeasurable

omit [BorelSpace X] in
lemma LocallyL2.add {f g : X → ℝ} (hf : LocallyL2 m f) (hg : LocallyL2 m g) :
    LocallyL2 m (fun x => f x + g x) := by
  intro o R hR
  exact (hf o R hR).add (hg o R hR)

lemma IsLocalWeakUpperGradient.add {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m g E)
    (hf : LocallyL2 m f) :
    IsLocalWeakUpperGradient m (fun x => f x + g x) (fun x => D x + E x) := by
  refine ⟨hD.1.add hE.1, ?_, ?_⟩
  · filter_upwards [hD.2.1, hE.2.1] with x hx hy
    exact add_nonneg hx hy
  · intro π hπ hb
    let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
    have hDm := hπ.aemeasurable_action hD.1
    have hEm := hπ.aemeasurable_action hE.1
    have hfm := ((hπ.aemeasurable_eval hf.aemeasurable timeOne).sub
      (hπ.aemeasurable_eval hf.aemeasurable timeZero)).abs.ennreal_ofReal
    have hsum : (fun z : Curve X × ℝ =>
        ENNReal.ofReal ((D (evalReal z.1 z.2)) + E (evalReal z.1 z.2)) * metricSpeed z.1 z.2)
        =ᵐ[π.prod ν] (fun z => ENNReal.ofReal (D (evalReal z.1 z.2)) * metricSpeed z.1 z.2 +
          ENNReal.ofReal (E (evalReal z.1 z.2)) * metricSpeed z.1 z.2) := by
      filter_upwards [hπ.ae_prod_eval_of_ae hD.2.1,
        hπ.ae_prod_eval_of_ae hE.2.1] with z hz hz'
      rw [ENNReal.ofReal_add hz hz', add_mul]
    have hsm := (hDm.add hEm).congr hsum.symm
    calc
      (∫⁻ γ : Curve X, ENNReal.ofReal |f (γ timeOne) + g (γ timeOne) -
          (f (γ timeZero) + g (γ timeZero))| ∂π) ≤
        (∫⁻ γ : Curve X, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| +
          ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π) := by
            apply lintegral_mono
            intro γ
            dsimp only
            rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            rw [show f (γ timeOne) + g (γ timeOne) - (f (γ timeZero) + g (γ timeZero)) =
              (f (γ timeOne) - f (γ timeZero)) + (g (γ timeOne) - g (γ timeZero)) by ring]
            exact abs_add_le _ _
      _ ≤ (∫⁻ γ : Curve X, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) +
          ∫⁻ γ : Curve X, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π :=
        (lintegral_add_left' hfm _).le
      _ ≤ (∫⁻ γ, ∫⁻ t, ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂ν ∂π) +
          ∫⁻ γ, ∫⁻ t, ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t ∂ν ∂π :=
        add_le_add (hD.2.2 π hπ hb) (hE.2.2 π hπ hb)
      _ = ∫⁻ z, ENNReal.ofReal (D (evalReal z.1 z.2) + E (evalReal z.1 z.2)) *
          metricSpeed z.1 z.2 ∂π.prod ν := by
        rw [← lintegral_prod _ hDm, ← lintegral_prod _ hEm,
          lintegral_congr_ae hsum, lintegral_add_left' hDm]
      _ = _ := lintegral_prod _ hsm

lemma IsTestPlan.of_plan_le_smul {π ρ : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hρp : IsProbabilityMeasure ρ) {C : ℝ≥0∞} (hC : C < ∞) (hρ : ρ ≤ C • π) :
    IsTestPlan m ρ := by
  obtain ⟨D, hD⟩ := hπ.2.1
  refine ⟨hρp, ⟨C.toNNReal * D, fun t => ?_⟩, ?_, ?_⟩
  · calc
      Measure.map (fun γ : Curve X => γ t) ρ ≤
          Measure.map (fun γ : Curve X => γ t) (C • π) :=
        Measure.map_mono hρ (continuous_eval_const t).measurable
      _ = C • Measure.map (fun γ : Curve X => γ t) π :=
        Measure.map_smul C _ _
      _ ≤ C • ((D : ℝ≥0∞) • m) := by gcongr; exact hD t
      _ = ((C.toNNReal * D : ℝ≥0) : ℝ≥0∞) • m := by
        rw [smul_smul, ENNReal.coe_mul, ENNReal.coe_toNNReal hC.ne]
  · exact (Measure.absolutelyContinuous_of_le_smul hρ).ae_le hπ.2.2.1
  · calc
      (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂ρ) ≤
          ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂C • π :=
        lintegral_mono' hρ le_rfl
      _ = C * ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂π :=
        lintegral_smul_measure _ _
      _ < ∞ := ENNReal.mul_lt_top hC hπ.2.2.2

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SlopeApprox
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
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def slopeApprox (f : X → ℝ) (n : ℕ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < 1 / (n + 1 : ℝ)),
    ENNReal.ofReal (|f y - f x| / dist y x)

lemma localSlope_eq_iInf_slopeApprox (f : X → ℝ) (x : X) :
    localSlope f x = ⨅ n : ℕ, slopeApprox f n x := by
  rw [localSlope, nhdsWithin,
    ((Metric.nhds_basis_ball_inv_nat_succ (x := x)).inf_principal ({x}ᶜ)).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  apply iInf_congr
  intro n
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le y (le_iSup_of_le hy.1 le_rfl)
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    by_cases hyx : y = x
    · simp [hyx]
    · exact le_iSup_of_le y (le_iSup_of_le
        (show y ∈ Metric.ball x (1 / (n + 1 : ℝ)) ∩ {x}ᶜ from ⟨hy, hyx⟩) le_rfl)

lemma lowerSemicontinuous_slopeApprox {f : X → ℝ} (hf : Continuous f) (n : ℕ) :
    LowerSemicontinuous (slopeApprox f n) := by
  intro x a ha
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp ha
  obtain ⟨hy, hay⟩ := lt_iSup_iff.mp hy
  have hyx : y ≠ x := by
    intro heq
    simp [heq] at hay
  have hdist : ContinuousAt (fun z => dist y z) x := continuous_const.dist continuous_id |>.continuousAt
  have hq : ContinuousAt (fun z => ENNReal.ofReal (|f y - f z| / dist y z)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (((continuous_const.sub hf).abs.continuousAt).div hdist (dist_ne_zero.mpr hyx))
  filter_upwards [hdist.eventually_lt continuousAt_const hy,
    (continuousAt_const.eventually_lt hq hay)] with z hz hqz
  exact hqz.trans_le (le_iSup_of_le y (le_iSup_of_le hz le_rfl))

lemma measurable_localSlope [MeasurableSpace X] [BorelSpace X]
    {f : X → ℝ} (hf : Continuous f) : Measurable (localSlope f) := by
  simp_rw [show localSlope f = fun x => ⨅ n, slopeApprox f n x from
    funext (localSlope_eq_iInf_slopeApprox f)]
  exact Measurable.iInf fun n => (lowerSemicontinuous_slopeApprox hf n).measurable

lemma slopeApprox_le_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : X) : slopeApprox f n x ≤ L := by
  apply iSup_le
  intro y
  apply iSup_le
  intro _hy
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  by_cases hyx : y = x
  · simp [hyx]
  · apply (div_le_iff₀ (dist_pos.mpr hyx)).mpr
    simpa only [Real.dist_eq] using hf.dist_le_mul y x

lemma localSlope_le_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) : localSlope f x ≤ L := by
  rw [localSlope_eq_iInf_slopeApprox]
  exact (iInf_le _ 0).trans (slopeApprox_le_lipschitz hf 0 x)

lemma deriv_comp_le_slopeApprox {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (n : ℕ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      slopeApprox f n (evalReal γ t) * metricSpeed γ t := by
  by_cases hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t
  · have hlim : Tendsto
        (fun s => ENNReal.ofReal (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|))
        (𝓝[≠] t) (𝓝 (ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t|)) := by
      simpa only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
        Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
        ENNReal.tendsto_ofReal (hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt).norm
    have hγc : Continuous (evalReal γ) :=
      continuous_evalReal.comp (continuous_const.prodMk continuous_id)
    have hnear : ∀ᶠ s in 𝓝 t,
        dist (evalReal γ s) (evalReal γ t) < 1 / (n + 1 : ℝ) := by
      apply (hγc.dist continuous_const).continuousAt.eventually_lt continuousAt_const
      simp only [dist_self]
      positivity
    calc
      _ = limsup (fun s => ENNReal.ofReal
          (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|)) (𝓝[≠] t) := hlim.limsup_eq.symm
      _ ≤ limsup (fun s => slopeApprox f n (evalReal γ t) * ENNReal.ofReal
          (dist (evalReal γ s) (evalReal γ t) / |s-t|)) (𝓝[≠] t) := by
        refine limsup_le_limsup ?_
        filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with s hs
        by_cases heq : evalReal γ s = evalReal γ t
        · simp [heq]
        have hdne : dist (evalReal γ s) (evalReal γ t) ≠ 0 := dist_ne_zero.mpr heq
        have hid : |f (evalReal γ s) - f (evalReal γ t)| / |s-t| =
            (|f (evalReal γ s) - f (evalReal γ t)| / dist (evalReal γ s) (evalReal γ t)) *
              (dist (evalReal γ s) (evalReal γ t) / |s-t|) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          calc
            _ = |f (evalReal γ s) - f (evalReal γ t)| *
                ((dist (evalReal γ s) (evalReal γ t))⁻¹ * dist (evalReal γ s) (evalReal γ t)) * |s-t|⁻¹ := by
              rw [inv_mul_cancel₀ hdne, mul_one]
            _ = _ := by ring
        rw [hid, ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) dist_nonneg)]
        apply mul_le_mul_left
        exact le_iSup_of_le (evalReal γ s) (le_iSup_of_le hs le_rfl)
      _ = _ := ENNReal.limsup_const_mul_of_ne_top
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (slopeApprox_le_lipschitz hf n _))
  · simp only [deriv_zero_of_not_differentiableAt hd, abs_zero, ENNReal.ofReal_zero]
    exact bot_le

lemma deriv_comp_le_localSlope {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (hspeed : metricSpeed γ t ≠ ∞) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      localSlope f (evalReal γ t) * metricSpeed γ t := by
  rw [localSlope_eq_iInf_slopeApprox, ENNReal.iInf_mul (fun h => (hspeed h).elim)]
  exact le_iInf fun n => deriv_comp_le_slopeApprox hf γ t n

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma localSlope_isLocalWeakUpperGradient (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    IsLocalWeakUpperGradient m f (fun x => (localSlope f x).toReal) := by
  have hm : Measurable (fun x => (localSlope f x).toReal) :=
    (measurable_localSlope hf.continuous).ennreal_toReal
  have hbound : ∀ x, ‖(localSlope f x).toReal‖ ≤ (L : ℝ) := by
    intro x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)).trans_eq
      (ENNReal.coe_toReal L)
  have hsl : ∀ x, localSlope f x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)
  refine ⟨?_, ae_of_all m fun _ => ENNReal.toReal_nonneg, ?_⟩
  · intro o R _hR
    let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        hfinite (Metric.ball o R) Metric.isBounded_ball⟩
    exact MemLp.of_bound hm.aestronglyMeasurable (L : ℝ) (ae_of_all _ hbound)
  · intro π hπ _hb
    let : IsProbabilityMeasure π := hπ.1
    have hsm : Measurable (fun p : Curve X × ℝ => metricSpeed p.1 p.2 ^ 2) :=
      measurable_metricSpeed.pow_const 2
    have hfin := ae_lt_top hsm.lintegral_prod_right hπ.2.2.2.ne
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1, hfin] with γ hγ hfinγ
    have hfiniteSpeed : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), metricSpeed γ t ≠ ∞ := by
      have hh := ae_lt_top (hsm.comp measurable_prodMk_left) hfinγ.ne
      filter_upwards [hh] with t ht
      exact fun heq => by simp [heq] at ht
    have hac := lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Set.Icc (0 : ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hac.integral_deriv_eq_sub]
        simp [evalReal, clampTime, timeOne, timeZero]
        rfl
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hfiniteSpeed] with t ht
        simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_toReal (hsl _)]
          using deriv_comp_le_localSlope hf γ t ht

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_InclusionDoubleDualSurjective
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
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessianFunctional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inclusionInDoubleDual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro F
  let T := InnerProductSpace.toDual ℝ E
  let g : StrongDual ℝ E := F.comp T.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨T.symm g, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨y, rfl⟩ := T.surjective f
  change ⟪y, T.symm g⟫_ℝ = F (T y)
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

lemma inclusionInDoubleDualWeak_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
  intro F
  obtain ⟨x, hx⟩ := inclusionInDoubleDual_surjective
    ((StrongDual.toWeakDual : StrongDual ℝ (StrongDual ℝ E) ≃ₗ[ℝ]
      WeakDual ℝ (StrongDual ℝ E)).symm F)
  refine ⟨toWeakSpace ℝ E x, ?_⟩
  apply (StrongDual.toWeakDual : StrongDual ℝ (StrongDual ℝ E) ≃ₗ[ℝ]
      WeakDual ℝ (StrongDual ℝ E)).symm.injective
  change (NormedSpace.inclusionInDoubleDual ℝ E) x = _
  exact hx

lemma isCompact_weakImage {s : Set E} (hconv : Convex ℝ s)
    (hclosed : IsClosed s) (hbounded : IsBounded s) :
    IsCompact (toWeakSpace ℝ E '' s) := by
  have hcl : closure (toWeakSpace ℝ E '' s) = toWeakSpace ℝ E '' s := by
    rw [← hconv.toWeakSpace_closure (𝕜 := ℝ), hclosed.closure_eq]
  rw [← hcl]
  apply NormedSpace.isCompact_closure_of_isBounded
  · simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using hbounded
  · rw [Set.range_eq_univ.mpr inclusionInDoubleDualWeak_surjective]
    exact subset_univ _

lemma nonempty_iInter_closed_convex {K : ℕ → Set E}
    (hne : ∀ n, (K n).Nonempty) (hcl : ∀ n, IsClosed (K n))
    (hc : ∀ n, Convex ℝ (K n)) (hanti : Antitone K) (hb : IsBounded (K 0)) :
    (⋂ n, K n).Nonempty := by
  let T := toWeakSpace ℝ E
  have himgcl : ∀ n, IsClosed (T '' K n) := by
    intro n
    rw [← (hcl n).closure_eq, (hc n).toWeakSpace_closure (𝕜 := ℝ)]
    exact isClosed_closure
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => T '' K n) (fun n => image_mono (hanti (Nat.le_succ n)))
    (fun n => (hne n).image T) (isCompact_weakImage (hc 0) (hcl 0) hb) himgcl
  refine ⟨T.symm y, mem_iInter.mpr fun n => ?_⟩
  obtain ⟨x, hx, heq⟩ := mem_iInter.mp hy n
  simpa only [← heq, LinearEquiv.symm_apply_apply] using hx

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma exists_snd_of_tendsto_fst_of_bounded
    {C : Set (WithLp 2 (E × F))} (hCcl : IsClosed C) (hCconv : Convex ℝ C)
    {u : ℕ → WithLp 2 (E × F)} (hu : ∀ n, u n ∈ C)
    {f : E} (hf : Tendsto (fun n => (u n).fst) atTop (𝓝 f))
    {B : ℝ} (hB : ∀ n, ‖(u n).snd‖ ≤ B) :
    ∃ g : F, WithLp.toLp 2 (f, g) ∈ C ∧ ‖g‖ ≤ B := by
  let K : ℕ → Set (WithLp 2 (E × F)) := fun n =>
    (C ∩ WithLp.fst ⁻¹' Metric.closedBall f (1 / (n + 1 : ℝ))) ∩
      WithLp.snd ⁻¹' Metric.closedBall (0 : F) B
  have hKcl : ∀ n, IsClosed (K n) := fun _ =>
    (hCcl.inter (Metric.isClosed_closedBall.preimage (WithLp.continuous_fst 2 E F))).inter
      (Metric.isClosed_closedBall.preimage (WithLp.continuous_snd 2 E F))
  have hKconv : ∀ n, Convex ℝ (K n) := fun n =>
    (hCconv.inter ((convex_closedBall f (1 / (n + 1 : ℝ))).linear_preimage (WithLp.fstₗ 2 ℝ E F))).inter
      ((convex_closedBall (0 : F) B).linear_preimage (WithLp.sndₗ 2 ℝ E F))
  have hKanti : Antitone K := by
    intro n k hnk p hp
    refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
    have hpdist : dist p.fst f ≤ 1 / (k + 1 : ℝ) := hp.1.2
    exact hpdist.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1))
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.mp hf) (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨u k, ⟨⟨hu k, (hk k le_rfl).le⟩, by simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hB k⟩⟩
  have hKb : IsBounded (K 0) := by
    have hbprod : IsBounded (Metric.closedBall f (1 : ℝ) ×ˢ Metric.closedBall (0 : F) B) :=
      Metric.isBounded_closedBall.prod Metric.isBounded_closedBall
    have himg := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.lipschitz.isBounded_image hbprod
    apply himg.subset
    intro p hp
    refine ⟨WithLp.ofLp p, ?_, rfl⟩
    refine ⟨?_, hp.2⟩
    have hpdist : dist p.fst f ≤ 1 / (0 + 1 : ℝ) := by
      simpa only [mem_preimage, Metric.mem_closedBall, Nat.cast_zero] using hp.1.2
    simpa only [zero_add, div_one, Metric.mem_closedBall, WithLp.ofLp_fst] using hpdist
  obtain ⟨p, hp⟩ := nonempty_iInter_closed_convex hKne hKcl hKconv hKanti hKb
  have hpf : p.fst = f := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    have hbound : ∀ n : ℕ, dist p.fst f ≤ 1 / (n + 1 : ℝ) := fun n => (mem_iInter.mp hp n).1.2
    exact ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hbound)
  refine ⟨p.snd, ?_, ?_⟩
  · have heq : WithLp.toLp 2 (f, p.snd) = p := by
      rw [← hpf]
      rfl
    rw [heq]
    exact (mem_iInter.mp hp 0).1.1
  · simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using (mem_iInter.mp hp 0).2

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_MapEvalReal
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
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.map_evalReal_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m) :
    Measure.map (fun z : Curve X × ℝ => evalReal z.1 z.2)
      (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) ≤ (C : ℝ≥0∞) • m := by
  let : IsProbabilityMeasure π := hπ.1
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.map_apply continuous_evalReal.measurable hS,
    Measure.prod_apply_symm (hS.preimage continuous_evalReal.measurable)]
  calc
    _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1, ((C : ℝ≥0∞) • m) S := by
      apply lintegral_mono
      intro t
      simpa only [Measure.map_apply (continuous_eval_const (clampTime t)).measurable hS,
        preimage_preimage, Function.comp_def, evalReal] using
        (hC (clampTime t)) S
    _ = _ := by simp

lemma IsTestPlan.lintegral_abs_eval_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {D : X → ℝ} (hD : AEStronglyMeasurable D m) (t : Time) :
    (∫⁻ γ, ENNReal.ofReal |D (γ t)| ∂π) ≤ (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm D 2 m := by
  let : IsProbabilityMeasure π := hπ.1
  have hm := hD.mono_ac (Measure.absolutelyContinuous_of_le_smul (hC t))
  have hcomp : AEStronglyMeasurable (fun γ : Curve X => D (γ t)) π :=
    hm.comp_measurable (continuous_eval_const t).measurable
  calc
    _ = eLpNorm (fun γ : Curve X => D (γ t)) 1 π := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp only [Real.enorm_eq_ofReal_abs]
    _ ≤ eLpNorm (fun γ : Curve X => D (γ t)) 2 π :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hcomp
    _ = eLpNorm D 2 (Measure.map (fun γ : Curve X => γ t) π) :=
      (eLpNorm_map_measure hm (continuous_eval_const t).measurable.aemeasurable).symm
    _ ≤ eLpNorm D 2 ((C : ℝ≥0∞) • m) := eLpNorm_mono_measure _ (hC t)
    _ = _ := by
      rw [eLpNorm_smul_measure_of_ne_top (by norm_num) D _]
      norm_num

lemma IsTestPlan.lintegral_abs_action_le {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {D : X → ℝ} (hD : AEStronglyMeasurable D m) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal |D (evalReal γ t)| * metricSpeed γ t ∂volume ∂π) ≤
    ((C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm D 2 m) *
      (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1, metricSpeed γ t ^ 2 ∂volume ∂π) ^ (1/(2 : ℝ)) := by
  let : IsProbabilityMeasure π := hπ.1
  let ν := π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
  have hmap := hπ.map_evalReal_le hC
  have hm := hD.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)
  have hcomp : AEStronglyMeasurable (fun point : Curve X × ℝ =>
      D (evalReal point.1 point.2)) ν := hm.comp_measurable continuous_evalReal.measurable
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (show Real.HolderConjugate 2 2 from Real.holderConjugate_iff.mpr (by norm_num))
    hcomp.aemeasurable.abs.ennreal_ofReal measurable_metricSpeed.aemeasurable
  have hnorm : eLpNorm (fun z : Curve X × ℝ => D (evalReal z.1 z.2)) 2 ν ≤
      (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm D 2 m := by
    calc
      _ = eLpNorm D 2 (Measure.map (fun z : Curve X × ℝ => evalReal z.1 z.2) ν) :=
        (eLpNorm_map_measure hm continuous_evalReal.measurable.aemeasurable).symm
      _ ≤ _ := by
        refine (eLpNorm_mono_measure _ hmap).trans_eq ?_
        rw [eLpNorm_smul_measure_of_ne_top (by norm_num) D _]
        norm_num
  have ham : AEMeasurable (fun z : Curve X × ℝ =>
      ENNReal.ofReal |D (evalReal z.1 z.2)| * metricSpeed z.1 z.2) ν :=
    hcomp.aemeasurable.abs.ennreal_ofReal.mul measurable_metricSpeed.aemeasurable
  rw [← lintegral_prod _ ham]
  calc
    _ ≤ eLpNorm (fun z : Curve X × ℝ => D (evalReal z.1 z.2)) 2 ν *
        (∫⁻ z : Curve X × ℝ, metricSpeed z.1 z.2 ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := by
      simpa only [Pi.mul_apply, Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs,
        ENNReal.rpow_two] using hh
    _ ≤ _ := by
      rw [lintegral_prod _ (measurable_metricSpeed.pow_const 2).aemeasurable]
      exact mul_le_mul_left hnorm _

lemma IsTestPlan.endpoint_mean_le_add {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {C : ℝ≥0} (hC : ∀ t : Time, Measure.map (fun γ : Curve X => γ t) π ≤ (C : ℝ≥0∞) • m)
    {f g : X → ℝ} (hf : AEStronglyMeasurable f m) (hg : AEStronglyMeasurable g m) :
    (∫⁻ γ, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) ≤
    (∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π) +
      (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm (fun x => g x - f x) 2 m +
      (C : ℝ≥0∞) ^ (1 / (2 : ℝ)) * eLpNorm (fun x => g x - f x) 2 m := by
  have hgmean : AEMeasurable (fun γ : Curve X =>
      ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)|) π :=
    ((hπ.aemeasurable_eval hg.aemeasurable timeOne).sub
    (hπ.aemeasurable_eval hg.aemeasurable timeZero)).abs.ennreal_ofReal
  have hdiff : AEMeasurable (fun γ : Curve X =>
      ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)|) π :=
    (hπ.aemeasurable_eval (hg.sub hf).aemeasurable timeOne).abs.ennreal_ofReal
  have hsum : AEMeasurable (fun γ : Curve X =>
      ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| +
        ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)|) π := hgmean.add hdiff
  have hpt : ∀ γ : Curve X,
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| +
        ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)| +
        ENNReal.ofReal |g (γ timeZero) - f (γ timeZero)| := by
    intro γ
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := abs_sub_le (f (γ timeOne)) (g (γ timeOne)) (f (γ timeZero))
    have h2 := abs_sub_le (g (γ timeOne)) (g (γ timeZero)) (f (γ timeZero))
    rw [abs_sub_comm (f (γ timeOne)) (g (γ timeOne))] at h1
    linarith
  calc
    _ ≤ ∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| +
      ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)| +
      ENNReal.ofReal |g (γ timeZero) - f (γ timeZero)| ∂π := lintegral_mono hpt
    _ = (∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - g (γ timeZero)| ∂π) +
      (∫⁻ γ, ENNReal.ofReal |g (γ timeOne) - f (γ timeOne)| ∂π) +
      (∫⁻ γ, ENNReal.ofReal |g (γ timeZero) - f (γ timeZero)| ∂π) := by
        rw [lintegral_add_left' hsum,
          lintegral_add_left' hgmean]
    _ ≤ _ := add_le_add (add_le_add_right (hπ.lintegral_abs_eval_le hC (hg.sub hf) timeOne) _)
      (hπ.lintegral_abs_eval_le hC (hg.sub hf) timeZero)

lemma IsTestPlan.action_le_add {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {D E : X → ℝ} (hD : LocallyL2 m D) (hE : LocallyL2 m E) :
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t ∂volume ∂π) ≤
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π) +
    (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal |E (evalReal γ t) - D (evalReal γ t)| * metricSpeed γ t ∂volume ∂π) := by
  let : IsProbabilityMeasure π := hπ.1
  have hdiff : LocallyL2 m (fun x => |E x - D x|) := fun o R hR =>
    ((hE o R hR).sub (hD o R hR)).norm
  rw [← lintegral_prod _ (hπ.aemeasurable_action hE),
    ← lintegral_prod _ (hπ.aemeasurable_action hD),
    ← lintegral_prod _ (hπ.aemeasurable_action hdiff),
    ← lintegral_add_left' (hπ.aemeasurable_action hD)]
  apply lintegral_mono
  intro z
  calc
    _ ≤ (ENNReal.ofReal (D (evalReal z.1 z.2)) +
        ENNReal.ofReal |E (evalReal z.1 z.2) - D (evalReal z.1 z.2)|) * metricSpeed z.1 z.2 := by
      apply mul_le_mul_left
      exact (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (E (evalReal z.1 z.2) -
        D (evalReal z.1 z.2))])).trans ENNReal.ofReal_add_le
    _ = _ := add_mul _ _ _

lemma IsLocalWeakUpperGradient.of_l2_tendsto {fn Dn : ℕ → X → ℝ} {f D : X → ℝ}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hfn : ∀ n, MemLp (fn n) 2 m) (hDn : ∀ n, MemLp (Dn n) 2 m)
    (hf : MemLp f 2 m) (hD : MemLp D 2 m)
    (hfconv : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 m) atTop (𝓝 0))
    (hDconv : Tendsto (fun n => eLpNorm (fun x => Dn n x - D x) 2 m) atTop (𝓝 0)) :
    IsLocalWeakUpperGradient m f D := by
  have hDl : LocallyL2 m D := fun _ _ _ => hD.restrict _
  refine ⟨hDl, ?_, ?_⟩
  · obtain ⟨ns, _hns, hlim⟩ :=
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (fun n => (hDn n).1) hD.1 hDconv).exists_seq_tendsto_ae
    filter_upwards [hlim, ae_all_iff.mpr fun n => (hn n).2.1] with x hx hpos
    exact ge_of_tendsto hx (Eventually.of_forall fun n => hpos (ns n))
  · intro π hπ hb
    obtain ⟨C, hC⟩ := hπ.2.1
    let c : ℝ≥0∞ := (C : ℝ≥0∞) ^ (1 / (2 : ℝ))
    let k : ℝ≥0∞ := (∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      metricSpeed γ t ^ 2 ∂volume ∂π) ^ (1/(2 : ℝ))
    let A : ℝ≥0∞ := ∫⁻ γ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π
    have hc : c ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top).ne
    have hk : k ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hπ.2.2.2.ne).ne
    have hcf : Tendsto (fun n => c * eLpNorm (fun x => fn n x - f x) 2 m) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero] using (ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp hfconv
    have hcd : Tendsto (fun n => (c * eLpNorm (fun x => Dn n x - D x) 2 m) * k)
        atTop (𝓝 0) := by
      have hh := (ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp hDconv
      simpa only [Function.comp_def, mul_zero, zero_mul] using (ENNReal.continuous_mul_const hk).continuousAt.tendsto.comp hh
    have hbound : ∀ n,
        (∫⁻ γ, ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π) ≤
          A + (c * eLpNorm (fun x => Dn n x - D x) 2 m) * k +
          c * eLpNorm (fun x => fn n x - f x) 2 m +
          c * eLpNorm (fun x => fn n x - f x) 2 m := by
      intro n
      refine (hπ.endpoint_mean_le_add hC hf.aestronglyMeasurable
        (hfn n).aestronglyMeasurable).trans ?_
      apply add_le_add_left
      apply add_le_add_left
      refine ((hn n).2.2 π hπ hb).trans ?_
      exact (hπ.action_le_add hDl (hn n).1).trans
        (add_le_add_right (hπ.lintegral_abs_action_le hC
          ((hDn n).aestronglyMeasurable.sub hD.aestronglyMeasurable)) _)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hlim := ((hconst.add hcd).add hcf).add hcf
    simpa only [add_zero] using ge_of_tendsto hlim (Eventually.of_forall hbound)

end WeakHessian

open Set Filter Topology Bornology
open scoped InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_L2GradientGraph
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
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma eLpNorm_sub_tendsto_of_tendsto_Lp {u : ℕ → Lp ℝ 2 m} {v : Lp ℝ 2 m}
    (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (fun x => u n x - v x) 2 m) atTop (𝓝 0) := by
  have heq : (fun n => eLpNorm (fun x => u n x - v x) 2 m) =
      (fun n => ‖u n - v‖ₑ) := by
    funext n
    rw [Lp.enorm_def]
    exact (eLpNorm_congr_ae (Lp.coeFn_sub (u n) v)).symm
  rw [heq]
  simpa only [sub_self, enorm_zero] using (h.sub (tendsto_const_nhds (x := v))).enorm

def l2GradientGraph (m : Measure X) : Set (WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :=
  {p | IsLocalWeakUpperGradient m p.fst p.snd}

lemma isClosed_l2GradientGraph : IsClosed (l2GradientGraph m) := by
  apply IsSeqClosed.isClosed
  intro u p hu hlim
  have hf := (WithLp.continuous_fst 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).tendsto p |>.comp hlim
  have hg := (WithLp.continuous_snd 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).tendsto p |>.comp hlim
  exact IsLocalWeakUpperGradient.of_l2_tendsto hu
    (fun n => Lp.memLp (u n).fst) (fun n => Lp.memLp (u n).snd)
    (Lp.memLp p.fst) (Lp.memLp p.snd)
    (eLpNorm_sub_tendsto_of_tendsto_Lp hf) (eLpNorm_sub_tendsto_of_tendsto_Lp hg)

lemma convex_l2GradientGraph : Convex ℝ (l2GradientGraph m) := by
  intro p hp q hq a b ha hb _hab
  have hpa := hp.const_mul a
  have hqb := hq.const_mul b
  have H := hpa.add hqb (fun o R _ => ((Lp.memLp p.fst).const_mul a).restrict (Metric.ball o R))
  apply H.congr_ae
  · change (fun x => a * p.fst x + b * q.fst x) =ᵐ[m] ⇑(a • p.fst + b • q.fst)
    filter_upwards [Lp.coeFn_add (a • p.fst) (b • q.fst),
      Lp.coeFn_smul a p.fst, Lp.coeFn_smul b q.fst] with x hsum hp hq
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hq] using hsum.symm
  · change (fun x => |a| * p.snd x + |b| * q.snd x) =ᵐ[m] ⇑(a • p.snd + b • q.snd)
    filter_upwards [Lp.coeFn_add (a • p.snd) (b • q.snd),
      Lp.coeFn_smul a p.snd, Lp.coeFn_smul b q.snd] with x hsum hp hq
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hq,
      abs_of_nonneg ha, abs_of_nonneg hb] using hsum.symm

lemma exists_upperGradient_of_bounded_l2 {fn Dn : ℕ → Lp ℝ 2 m} {f : Lp ℝ 2 m}
    (hn : ∀ n, IsLocalWeakUpperGradient m (fn n) (Dn n))
    (hf : Tendsto fn atTop (𝓝 f)) {B : ℝ} (hB : ∀ n, ‖Dn n‖ ≤ B) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B := by
  exact WeakHessianFunctional.exists_snd_of_tendsto_fst_of_bounded
    isClosed_l2GradientGraph convex_l2GradientGraph
    (u := fun n => WithLp.toLp 2 (fn n, Dn n)) hn hf hB

lemma isClosed_upperGradient_sublevel (B : ℝ) :
    IsClosed {f : Lp ℝ 2 m | ∃ D : Lp ℝ 2 m,
      IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B} := by
  apply IsSeqClosed.isClosed
  intro fn f hfn hf
  choose Dn hDn hB using hfn
  exact exists_upperGradient_of_bounded_l2 hDn hf hB

lemma exists_norm_minimal_upperGradient {f : Lp ℝ 2 m}
    (h : ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧
      ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖ := by
  let S : Set (Lp ℝ 2 m) := {D | IsLocalWeakUpperGradient m f D}
  have hScl : IsClosed S := by
    exact isClosed_l2GradientGraph.preimage
      ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
        (continuous_const.prodMk continuous_id))
  have hSc : Convex ℝ S := by
    intro D hD E hE a b ha hb hab
    have H := convex_l2GradientGraph (m := m)
      (x := WithLp.toLp 2 (f, D)) (y := WithLp.toLp 2 (f, E)) hD hE ha hb hab
    change IsLocalWeakUpperGradient m ⇑(a • f + b • f) ⇑(a • D + b • E) at H
    rwa [← add_smul, hab, one_smul] at H
  obtain ⟨D, hD, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex h hScl.isComplete hSc (0 : Lp ℝ 2 m)
  refine ⟨D, hD, fun E hE => ?_⟩
  rw [zero_sub, norm_neg] at hnorm
  rw [hnorm]
  have hlow : BddBelow (Set.range fun w : S => ‖(0 : Lp ℝ 2 m) - w‖) := ⟨0, by
    rintro _ ⟨w, rfl⟩
    exact norm_nonneg _⟩
  calc
    _ ≤ ‖(0 : Lp ℝ 2 m) - E‖ := ciInf_le hlow (⟨E, hE⟩ : S)
    _ = ‖E‖ := by rw [zero_sub, norm_neg]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_ELpNormSq
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
attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma eLpNorm_sq_eq_lintegral (f : X → ℝ) (hf : AEStronglyMeasurable f m) :
    eLpNorm f 2 m ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂m := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := m) (f := f) (p := 2) (by norm_num)
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_natCast] at h
  simpa only [ENNReal.rpow_two] using h

lemma eLpNorm_localSlope_sq {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    eLpNorm (fun x => (localSlope f x).toReal) 2 m ^ 2 =
      ∫⁻ x, localSlope f x ^ 2 ∂m := by
  rw [eLpNorm_sq_eq_lintegral _
    (measurable_localSlope hf.continuous).ennreal_toReal.aestronglyMeasurable]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (lt_of_le_of_lt (localSlope_le_lipschitz hf x) ENNReal.coe_lt_top).ne]

lemma memLp_localSlope_of_lintegral_lt_top {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (h : (∫⁻ x, localSlope f x ^ 2 ∂m) < ∞) :
    MemLp (fun x => (localSlope f x).toReal) 2 m := by
  rw [← eLpNorm_localSlope_sq hf, ENNReal.pow_lt_top_iff] at h
  exact ⟨(measurable_localSlope hf.continuous).ennreal_toReal.aestronglyMeasurable, h.resolve_right (by omega)⟩

omit [BorelSpace X] in
lemma norm_localSlope_toLp_sq {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (h : MemLp (fun x => (localSlope f x).toReal) 2 m) :
    ENNReal.ofReal (‖h.toLp (fun x => (localSlope f x).toReal)‖ ^ 2) =
      ∫⁻ x, localSlope f x ^ 2 ∂m := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def,
    eLpNorm_congr_ae h.coeFn_toLp, eLpNorm_sq_eq_lintegral _ h.aestronglyMeasurable]
  apply lintegral_congr
  intro point
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal
      (lt_of_le_of_lt (localSlope_le_lipschitz hf point) ENNReal.coe_lt_top).ne]


omit [BorelSpace X] in
lemma half_lintegral_localSlope_eq {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (h : MemLp (fun x => (localSlope f x).toReal) 2 m) :
    (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope f x ^ 2 ∂m) =
      ENNReal.ofReal (‖h.toLp (fun x => (localSlope f x).toReal)‖ ^ 2 / 2) := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    norm_localSlope_toLp_sq hf]
  norm_num only [ENNReal.ofReal_ofNat]
  exact mul_comm _ _

lemma lipschitz_mem_upperGradient_sublevel (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hf2 : MemLp f 2 m)
    {B : ℝ} (hB : 0 ≤ B)
    (he : (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope f x ^ 2 ∂m) ≤
      ENNReal.ofReal (B ^ 2 / 2)) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m (hf2.toLp f) D ∧ ‖D‖ ≤ B := by
  have hsfin : (∫⁻ x, localSlope f x ^ 2 ∂m) < ∞ := by
    by_contra hh
    have ht : (∫⁻ x, localSlope f x ^ 2 ∂m) = ∞ := top_le_iff.mp (not_lt.mp hh)
    norm_num [ht] at he
  have hs := memLp_localSlope_of_lintegral_lt_top hf hsfin
  refine ⟨hs.toLp (fun x => (localSlope f x).toReal), ?_, ?_⟩
  · exact (localSlope_isLocalWeakUpperGradient hfinite hf).congr_ae
      hf2.coeFn_toLp.symm hs.coeFn_toLp.symm
  · rw [half_lintegral_localSlope_eq hf hs] at he
    have hsq : ‖hs.toLp (fun x => (localSlope f x).toReal)‖ ^ 2 / 2 ≤ B ^ 2 / 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
    nlinarith [norm_nonneg (hs.toLp (fun x => (localSlope f x).toReal))]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SlopeApproxAntitone
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
lemma slopeApprox_antitone (f : X → ℝ) (x : X) : Antitone (fun n => slopeApprox f n x) := by
  intro i j hij
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hrad : (1 : ℝ) / (j+1) ≤ 1/(i+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  exact le_iSup_of_le y (le_iSup_of_le (hy.trans_le hrad) le_rfl)

lemma slopeApprox_const_mul (c : ℝ) (f : X → ℝ) (n : ℕ) (x : X) :
    slopeApprox (fun y => c * f y) n x = ENNReal.ofReal |c| * slopeApprox f n x := by
  unfold slopeApprox
  simp only [← mul_sub, abs_mul, mul_div_assoc, ENNReal.ofReal_mul (abs_nonneg c)]
  rw [ENNReal.mul_iSup]
  congr 1
  funext y
  rw [ENNReal.mul_iSup]

lemma localSlope_const_mul (c : ℝ) (f : X → ℝ) (x : X) :
    localSlope (fun y => c * f y) x = ENNReal.ofReal |c| * localSlope f x := by
  simp only [localSlope_eq_iInf_slopeApprox, slopeApprox_const_mul]
  exact (ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)).symm

lemma localSlope_zero (x : X) : localSlope (fun _ : X => (0:ℝ)) x = 0 := by
  simpa only [zero_mul, abs_zero, ENNReal.ofReal_zero, Pi.zero_apply] using
    localSlope_const_mul 0 (fun _ : X => (0:ℝ)) x

lemma slopeApprox_add_le (f g : X → ℝ) (n : ℕ) (x : X) :
    slopeApprox (fun y => f y + g y) n x ≤ slopeApprox f n x + slopeApprox g n x := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hreal : |f y + g y - (f x + g x)| / dist y x ≤
      |f y - f x| / dist y x + |g y - g x| / dist y x := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ dist_nonneg
    convert abs_add_le (f y - f x) (g y - g x) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (|f y-f x| / dist y x + |g y-g x| / dist y x) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (|f y-f x| / dist y x) +
        ENNReal.ofReal (|g y-g x| / dist y x) := ENNReal.ofReal_add (by positivity) (by positivity)
    _ ≤ _ := by
      apply add_le_add
      · exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)
      · exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)

lemma localSlope_add_le (f g : X → ℝ) (x : X) :
    localSlope (fun y => f y + g y) x ≤ localSlope f x + localSlope g x := by
  simp only [localSlope_eq_iInf_slopeApprox]
  rw [ENNReal.iInf_add_iInf (fun i j => ⟨max i j, add_le_add
    (slopeApprox_antitone f x (le_max_left i j))
    (slopeApprox_antitone g x (le_max_right i j))⟩)]
  exact iInf_mono fun n => slopeApprox_add_le f g n x

end WeakHessian

open Set
open scoped NNReal


namespace WeakHessian
variable {X : Type*} [PseudoMetricSpace X]

lemma lipschitz_mul_bounded {f g : X → ℝ} {L T : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith T g)
    {A B : ℝ} (hA : ∀ x, |f x| ≤ A) (hB : ∀ x, |g x| ≤ B) :
    LipschitzWith (L*‖B‖₊+‖A‖₊*T) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_add,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,Real.dist_eq]
  have hL := hf.dist_le_mul x y
  have hT := hg.dist_le_mul x y
  rw [Real.dist_eq] at hL hT
  calc
    |f x*g x-f y*g y| = |(f x-f y)*g x+f y*(g x-g y)| := by congr 1; ring
    _ ≤ |f x-f y| * |g x|+|f y| * |g x-g y| := by simpa only [abs_mul] using abs_add_le ((f x-f y)*g x) (f y*(g x-g y))
    _ ≤ ((L:ℝ)*dist x y)* |B|+|A| * ((T:ℝ)*dist x y) := by
      exact add_le_add
        (mul_le_mul hL ((hB x).trans (le_abs_self B)) (abs_nonneg _)
          (mul_nonneg L.coe_nonneg dist_nonneg))
        (mul_le_mul ((hA y).trans (le_abs_self A)) hT (abs_nonneg _) (abs_nonneg _))
    _ = ((L:ℝ)* |B|+|A| * (T:ℝ))*dist x y := by ring
lemma lipschitz_const_mul_real {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (c : ℝ) :
    LipschitzWith (‖c‖₊*L) (fun x => c*f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs]
  rw [← mul_sub,abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg _)

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_L2SlopeGraph
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

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_ne_top {f : X → ℝ} (hf : GloballyLipschitz f) (x : X) :
    localSlope f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top
      (localSlope_le_lipschitz hf.choose_spec x)

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_toReal_add_le {f g : X → ℝ}
    (hf : GloballyLipschitz f) (hg : GloballyLipschitz g) (x : X) :
    (localSlope (fun y => f y+g y) x).toReal ≤
      (localSlope f x).toReal+(localSlope g x).toReal := by
  rw [← ENNReal.toReal_add (localSlope_ne_top hf x) (localSlope_ne_top hg x)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨localSlope_ne_top hf x,
    localSlope_ne_top hg x⟩) (localSlope_add_le f g x)

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_toReal_const_mul (a : ℝ) (f : X → ℝ) (x : X) :
    (localSlope (fun y => a*f y) x).toReal = |a| * (localSlope f x).toReal := by
  rw [localSlope_const_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg a)]

def l2SlopeGraph (m : Measure X) : Set (WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :=
  {p | ∃ f : X → ℝ, GloballyLipschitz f ∧ ∃ hf : MemLp f 2 m,
    hf.toLp f = p.fst ∧ ∀ᵐ x ∂m, (localSlope f x).toReal ≤ p.snd x}

def l2RelaxedGraph (m : Measure X) : Set (WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)) :=
  closure (l2SlopeGraph m)

omit [BorelSpace X] in
lemma convex_l2SlopeGraph : Convex ℝ (l2SlopeGraph m) := by
  intro p hp q hq a b ha hb _hab
  obtain ⟨f,hf,hm,hp,hD⟩ := hp
  obtain ⟨g,hg,hn,hq,hE⟩ := hq
  have hfg : MemLp (fun x => a*f x+b*g x) 2 m := (hm.const_mul a).add (hn.const_mul b)
  refine ⟨fun x => a*f x+b*g x, ?_, hfg, ?_, ?_⟩
  · exact ⟨_, (lipschitz_const_mul_real hf.choose_spec a).add
      (lipschitz_const_mul_real hg.choose_spec b)⟩
  · apply Lp.ext
    filter_upwards [hfg.coeFn_toLp,
      Lp.coeFn_add (a • p.fst) (b • q.fst), Lp.coeFn_smul a p.fst,
      Lp.coeFn_smul b q.fst, hm.coeFn_toLp,hn.coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    change _ = (a • p.fst+b • q.fst) x
    rw [h1,h2,Pi.add_apply,h3,h4,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
    simp only [← hp,← hq,h5,h6]
  · have haf : GloballyLipschitz (fun x => a*f x) :=
      ⟨_,lipschitz_const_mul_real hf.choose_spec a⟩
    have hbg : GloballyLipschitz (fun x => b*g x) :=
      ⟨_,lipschitz_const_mul_real hg.choose_spec b⟩
    filter_upwards [hD,hE, Lp.coeFn_add (a • p.snd) (b • q.snd),
      Lp.coeFn_smul a p.snd, Lp.coeFn_smul b q.snd] with x hx hy hsum hpa hqb
    change _ ≤ (a • p.snd+b • q.snd) x
    rw [hsum, Pi.add_apply,hpa,hqb,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul]
    calc _ ≤ (localSlope (fun y => a*f y) x).toReal+
          (localSlope (fun y => b*g y) x).toReal := localSlope_toReal_add_le haf hbg x
      _ = a*(localSlope f x).toReal+b*(localSlope g x).toReal := by
        rw [localSlope_toReal_const_mul,localSlope_toReal_const_mul,
          abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

omit [BorelSpace X] in
lemma isClosed_l2RelaxedGraph : IsClosed (l2RelaxedGraph m) := isClosed_closure
omit [BorelSpace X] in
lemma convex_l2RelaxedGraph : Convex ℝ (l2RelaxedGraph m) :=
  (convex_l2SlopeGraph (m := m)).closure

lemma IsLocalWeakUpperGradient.mono {f D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hDE : D ≤ᵐ[m] E)
    (hE : LocallyL2 m E) : IsLocalWeakUpperGradient m f E := by
  refine ⟨hE,?_,?_⟩
  · filter_upwards [hD.2.1,hDE] with x hx hy
    exact hx.trans hy
  · intro π hπ hb
    apply (hD.2.2 π hπ hb).trans
    apply lintegral_mono_ae
    filter_upwards [hπ.ae_ae_eval_of_ae hDE] with γ hγ
    apply lintegral_mono_ae
    filter_upwards [hγ] with t ht
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal ht) le_rfl

lemma slopeGraph_isUpperGradient (hfinite : FiniteOnBoundedSets m)
    {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)} (hp : p ∈ l2SlopeGraph m) :
    IsLocalWeakUpperGradient m p.fst p.snd := by
  obtain ⟨f,hf,hm,hp,hD⟩ := hp
  have H := (localSlope_isLocalWeakUpperGradient hfinite hf.choose_spec).mono hD
    (fun o R _ => (Lp.memLp p.snd).restrict (Metric.ball o R))
  exact H.congr_ae (hp ▸ hm.coeFn_toLp.symm) Filter.EventuallyEq.rfl

lemma relaxedGraph_isUpperGradient (hfinite : FiniteOnBoundedSets m)
    {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)} (hp : p ∈ l2RelaxedGraph m) :
    IsLocalWeakUpperGradient m p.fst p.snd := by
  exact (closure_minimal (fun _ hp => slopeGraph_isUpperGradient hfinite hp)
    isClosed_l2GradientGraph) hp

omit [BorelSpace X] in
lemma exists_norm_minimal_relaxedGradient {f : Lp ℝ 2 m}
    (h : ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧
      ∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖ := by
  let S : Set (Lp ℝ 2 m) := {D | WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m}
  have hScl : IsClosed S := isClosed_l2RelaxedGraph.preimage
    ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      (continuous_const.prodMk continuous_id))
  have hSc : Convex ℝ S := by
    intro D hD E hE a b ha hb hab
    have H := convex_l2RelaxedGraph (m := m) hD hE ha hb hab
    change WithLp.toLp 2 (a • f+b • f,a • D+b • E) ∈ l2RelaxedGraph m at H
    rwa [← add_smul,hab,one_smul] at H
  obtain ⟨D,hD,hnorm⟩ := exists_norm_eq_iInf_of_complete_convex h hScl.isComplete hSc (0 : Lp ℝ 2 m)
  refine ⟨D,hD,fun E hE => ?_⟩
  rw [zero_sub,norm_neg] at hnorm
  rw [hnorm]
  have hlow : BddBelow (Set.range fun w : S => ‖(0 : Lp ℝ 2 m)-w‖) :=
    ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩
  calc
    _ ≤ ‖(0 : Lp ℝ 2 m)-E‖ := ciInf_le hlow (⟨E,hE⟩ : S)
    _ = ‖E‖ := by rw [zero_sub,norm_neg]
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SlopeApproxProduct
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
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

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


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

lemma slopeApprox_product_le {f g : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : X) :
    slopeApprox (fun y => f y*g y) n x ≤
      ENNReal.ofReal (|f x|+(L:ℝ)/(n+1))*slopeApprox g n x+
        ENNReal.ofReal |g x| * slopeApprox f n x := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hfx : |f y| ≤ |f x|+(L:ℝ)/(n+1) := by
    calc
      |f y| ≤ |f x|+|f y-f x| := by
        convert abs_add_le (f x) (f y-f x) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ring
      _ ≤ |f x|+(L:ℝ)*dist y x := add_le_add (le_refl _)
        (by simpa only [Real.dist_eq] using hf.dist_le_mul y x)
      _ ≤ _ := by
        apply add_le_add (le_refl _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hy.le L.coe_nonneg
  have hreal : |f y*g y-f x*g x|/dist y x ≤
      (|f x|+(L:ℝ)/(n+1))*(|g y-g x|/dist y x)+
        |g x| * (|f y-f x|/dist y x) := by
    calc _ = |f y*(g y-g x)+g x*(f y-f x)|/dist y x := by congr 2; ring
      _ ≤ (|f y| * |g y-g x|+|g x| * |f y-f x|)/dist y x := by
        apply div_le_div_of_nonneg_right _ dist_nonneg
        simpa only [abs_mul] using abs_add_le (f y*(g y-g x)) (g x*(f y-f x))
      _ = |f y| * (|g y-g x|/dist y x)+|g x| * (|f y-f x|/dist y x) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ENNReal.ofReal ((|f x|+(L:ℝ)/(n+1))*(|g y-g x|/dist y x)+
        |g x| * (|f y-f x|/dist y x)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (|f x|+(L:ℝ)/(n+1))*ENNReal.ofReal (|g y-g x|/dist y x)+
        ENNReal.ofReal |g x| * ENNReal.ofReal (|f y-f x|/dist y x) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ _ := add_le_add
      (mul_le_mul' le_rfl (show ENNReal.ofReal (|g y-g x|/dist y x) ≤ slopeApprox g n x from le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
      (mul_le_mul' le_rfl (show ENNReal.ofReal (|f y-f x|/dist y x) ≤ slopeApprox f n x from le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

lemma localSlope_product_le {f g : X → ℝ} {L T : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith T g) (x : X) :
    localSlope (fun y => f y*g y) x ≤ ENNReal.ofReal |f x| * localSlope g x+
      ENNReal.ofReal |g x| * localSlope f x := by
  have hf0 : localSlope f x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)
  have hg0 : localSlope g x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_lipschitz hg x)
  have ht (u : X → ℝ) : Tendsto (fun n : ℕ => slopeApprox u n x) atTop (𝓝 (localSlope u x)) := by
    rw [localSlope_eq_iInf_slopeApprox]
    exact tendsto_atTop_iInf (slopeApprox_antitone u x)
  have hfac : Tendsto (fun n : ℕ => ENNReal.ofReal (|f x|+(L:ℝ)/(n+1))) atTop
      (𝓝 (ENNReal.ofReal |f x|)) := by
    have H := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (L:ℝ) |>.const_add |f x|
    simp only [mul_zero,add_zero] at H
    simpa only [mul_one_div,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp H
  apply ge_of_tendsto' ((ENNReal.Tendsto.mul hfac (Or.inr hg0) (ht g)
    (Or.inr ENNReal.ofReal_ne_top)).add
      (ENNReal.Tendsto.mul (tendsto_const_nhds (x := ENNReal.ofReal |g x|)) (Or.inr hf0) (ht f)
        (Or.inr ENNReal.ofReal_ne_top)))
  intro n
  rw [localSlope_eq_iInf_slopeApprox (fun y => f y*g y)]
  exact (iInf_le (fun n : ℕ => slopeApprox (fun y => f y*g y) n x) n).trans
    (slopeApprox_product_le hf n x)
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_LipschitzMulCompact
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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open Set
open scoped NNReal ENNReal

variable {X : Type*} [MetricSpace X]

lemma lipschitz_mul_compact {φ f : X → ℝ} (hφ : GloballyLipschitz φ)
    (hf : GloballyLipschitz f) (hc : HasCompactSupport φ) :
    GloballyLipschitz (fun x => φ x*f x) := by
  obtain ⟨A,hA⟩ := hc.isCompact.image hφ.choose_spec.continuous |>.isBounded.subset_closedBall 0
  obtain ⟨B,hB⟩ := hc.isCompact.image hf.choose_spec.continuous |>.isBounded.subset_closedBall 0
  obtain ⟨n,hn⟩ := exists_nat_ge B
  let g := fun x => max (-(n:ℝ)) (min (f x) n)
  have hg : LipschitzWith hf.choose g :=
    (hf.choose_spec.min_const (n:ℝ)).const_max (-(n:ℝ))
  have hgb (x : X) : |g x| ≤ (n:ℝ) :=
    abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)⟩
  have hφb (x : X) : |φ x| ≤ |A| := by
    by_cases hx : φ x = 0
    · simp [hx]
    · have hx' := hA (mem_image_of_mem _ (subset_tsupport _ (Function.mem_support.mpr hx)))
      simp only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hx'
      exact hx'.trans (le_abs_self A)
  have heq : (fun x => φ x*f x) = (fun x => φ x*g x) := by
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    have hb := hB (mem_image_of_mem _ (subset_tsupport _ (Function.mem_support.mpr hx)))
    simp only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hb
    have hb' := abs_le.mp (hb.trans hn)
    simp only [g,min_eq_left hb'.2,max_eq_right hb'.1]
  rw [heq]
  exact ⟨_,lipschitz_mul_bounded hφ.choose_spec hg hφb hgb⟩

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_ActionIntervalIntegrable
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
namespace WeakHessianCalculus

lemma action_intervalIntegrable {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞) :
    IntervalIntegrable (fun t => (a t).toReal) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  exact (integrable_toReal_iff ha ((ae_lt_top' ha hfin.ne).mono fun _ h => h.ne)).mpr hfin.ne

lemma action_dist_primitive {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞) {q : ℝ → ℝ}
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (hqt : ENNReal.ofReal |q t - q s| ≤ ∫⁻ r in Icc s t, a r) :
    dist (q s) (q t) ≤ dist (∫ r in (0 : ℝ)..s, (a r).toReal)
      (∫ r in (0 : ℝ)..t, (a r).toReal) := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht.2
  have hstfin : (∫⁻ r in Icc s t, a r) ≠ ∞ :=
    ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hsub)
  have hast : AEMeasurable a (volume.restrict (Icc s t)) :=
    ha.mono_measure (Measure.restrict_mono_set _ hsub)
  have hti := action_intervalIntegrable ha hfin
  have hi_s : IntervalIntegrable (fun r => (a r).toReal) volume 0 s :=
    hti.mono_set (by simpa only [uIcc_of_le hs.1, uIcc_of_le zero_le_one]
      using (Icc_subset_Icc le_rfl hs.2))
  have hi_t : IntervalIntegrable (fun r => (a r).toReal) volume 0 t :=
    hti.mono_set (by simpa only [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
      using (Icc_subset_Icc le_rfl ht.2))
  have hreal : (∫⁻ r in Icc s t, a r).toReal = ∫ r in s..t, (a r).toReal := by
    rw [← integral_toReal hast (ae_lt_top' hast hstfin),
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
  calc
    dist (q s) (q t) = |q t - q s| := by rw [dist_comm, Real.dist_eq]
    _ ≤ (∫⁻ r in Icc s t, a r).toReal := by
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using ENNReal.toReal_mono hstfin hqt
    _ = (∫ r in (0 : ℝ)..t, (a r).toReal) - ∫ r in (0 : ℝ)..s, (a r).toReal :=
      hreal.trans (intervalIntegral.integral_interval_sub_left hi_t hi_s).symm
    _ ≤ _ := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _

lemma abs_deriv_le_of_dist_le {q A : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hq : DifferentiableAt ℝ q t)
    {a : ℝ} (hA : HasDerivAt A a t)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1,
      dist (q s) (q r) ≤ dist (A s) (A r)) :
    |deriv q t| ≤ |a| := by
  apply le_of_tendsto_of_tendsto hq.hasDerivAt.tendsto_slope.abs hA.tendsto_slope.abs
  have hm : ∀ᶠ s in 𝓝[≠] t, s ∈ Icc (0 : ℝ) 1 :=
    mem_of_superset (nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2)) Ioo_subset_Icc_self
  filter_upwards [hm] with s hs
  simp only [slope_def_field, abs_div]
  exact div_le_div_of_nonneg_right (by simpa only [Real.dist_eq] using
    (hdom s hs t (Ioo_subset_Icc_self ht))) (abs_nonneg _)

lemma ae_deriv_le_of_dense_action {q : ℝ → ℝ} {a : ℝ → ℝ≥0∞}
    (hq : AbsolutelyContinuousOnInterval q 0 1)
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    (d : ℕ → Icc (0 : ℝ) 1) (hd : DenseRange d)
    (hbound : ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |q (d j) - q (d i)| ≤ ∫⁻ t in Icc (d i : ℝ) (d j : ℝ), a t) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ENNReal.ofReal |deriv q t| ≤ a t := by
  let A : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, (a r).toReal
  have hi := action_intervalIntegrable ha hfin
  have hcA : Continuous (fun s : Icc (0 : ℝ) 1 => A s) := by
    apply (hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn.comp_continuous
      continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hcq : Continuous (fun s : Icc (0 : ℝ) 1 => q s) := by
    apply hq.continuousOn.comp_continuous continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hdense : ∀ i j, dist (q (d i)) (q (d j)) ≤ dist (A (d i)) (A (d j)) := by
    intro i j
    rcases lt_trichotomy (d i : ℝ) (d j : ℝ) with h|h|h
    · exact action_dist_primitive ha hfin (d i).property (d j).property h.le (hbound i j h)
    · simp only [h, dist_self, le_refl]
    · simpa only [dist_comm] using
        action_dist_primitive ha hfin (d j).property (d i).property h.le (hbound j i h)
  have hall : ∀ s r : Icc (0 : ℝ) 1, dist (q s) (q r) ≤ dist (A s) (A r) := by
    intro s r
    exact (hd.prodMap hd).induction_on (p := fun z : Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1 =>
      dist (q z.1) (q z.2) ≤ dist (A z.1) (A z.2)) (s,r)
      (isClosed_le ((hcq.comp continuous_fst).dist (hcq.comp continuous_snd))
        ((hcA.comp continuous_fst).dist (hcA.comp continuous_snd)))
      (fun ij => hdense ij.1 ij.2)
  have haa := hi.ae_hasDerivAt_integral
  have hqa := hq.ae_differentiableAt
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_of_ae haa, ae_restrict_of_ae hqa,
    ae_restrict_mem measurableSet_Ioo] with t hAt hqt ht
  have htt : t ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self ht
  have habs := abs_deriv_le_of_dist_le ht (hqt htt)
    (hAt htt 0 (by simp)) (fun s hs r hr => hall ⟨s,hs⟩ ⟨r,hr⟩)
  calc
    ENNReal.ofReal |deriv q t| ≤ ENNReal.ofReal (a t).toReal :=
      ENNReal.ofReal_le_ofReal (by simpa only [abs_of_nonneg ENNReal.toReal_nonneg] using habs)
    _ ≤ a t := ENNReal.ofReal_toReal_le

end WeakHessianCalculus

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

lemma absolutelyContinuous_of_dist_dom {f g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ s ∈ Set.uIcc a b, ∀ t ∈ Set.uIcc a b,
      dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hsmall => lt_of_le_of_lt ?_ (hbound E hE hsmall)⟩
  refine Finset.sum_le_sum fun i hi => ?_
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

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

def affineHomeomorph (a c : ℝ) (hc : c ≠ 0) : ℝ ≃ₜ ℝ :=
  (Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addLeft a)

@[simp] lemma affineHomeomorph_apply (a c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    affineHomeomorph a c hc t = a + c * t := rfl

lemma map_affineHomeomorph_volume (a c : ℝ) (hc : 0 < c) :
    Measure.map (affineHomeomorph a c hc.ne') volume =
      (ENNReal.ofReal c)⁻¹ • (volume : Measure ℝ) := by
  change Measure.map ((fun t : ℝ => a + t) ∘ (fun t : ℝ => c * t)) volume = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left hc.ne',
    Measure.map_smul, map_add_left_eq_self, abs_of_pos (inv_pos.mpr hc),
    ENNReal.ofReal_inv_of_pos hc]

lemma affineHomeomorph_preimage_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ) :
    affineHomeomorph a c hc.ne' ⁻¹' Set.Icc (a + c * s) (a + c * t) = Set.Icc s t := by
  ext u
  simp only [Set.mem_preimage, Set.mem_Icc, affineHomeomorph_apply, add_le_add_iff_left,
    mul_le_mul_iff_right₀ hc]

lemma lintegral_affine_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Icc s t, f (a + c * r)) =
      (ENNReal.ofReal c)⁻¹ * ∫⁻ r in Set.Icc (a + c * s) (a + c * t), f r := by
  let e := affineHomeomorph a c hc.ne'
  have hre : (Measure.map e volume).restrict (Set.Icc (a + c * s) (a + c * t)) =
      Measure.map e (volume.restrict (Set.Icc s t)) := by
    rw [e.measurableEmbedding.restrict_map, affineHomeomorph_preimage_Icc a c hc]
  calc
    (∫⁻ r in Set.Icc s t, f (a + c * r)) =
        ∫⁻ r, f r ∂Measure.map e (volume.restrict (Set.Icc s t)) :=
      (e.measurableEmbedding.lintegral_map f).symm
    _ = ∫⁻ r, f r ∂(Measure.map e volume).restrict (Set.Icc (a + c * s) (a + c * t)) := by rw [hre]
    _ = _ := by rw [map_affineHomeomorph_volume a c hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

lemma lintegral_scaled_affine_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Icc s t, ENNReal.ofReal c * f (a + c * r)) =
      ∫⁻ r in Set.Icc (a + c * s) (a + c * t), f r := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_affine_Icc a c hc,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, one_mul]

lemma lintegral_scaled_sq_affine_Icc (a c : ℝ) (hc : 0 < c) (s t : ℝ)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Set.Icc s t, (ENNReal.ofReal c * f (a + c * r)) ^ 2) =
      ENNReal.ofReal c * ∫⁻ r in Set.Icc (a + c * s) (a + c * t), (f r) ^ 2 := by
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness),
    lintegral_affine_Icc a c hc s t (fun r => f r ^ 2), pow_two]
  calc
    _ = ENNReal.ofReal c * (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹) *
        ∫⁻ r in Set.Icc (a + c * s) (a + c * t), f r ^ 2 := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, mul_one]

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
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma ofReal_sq_le_ofReal_sq (x : ℝ) : ENNReal.ofReal x ^ 2 ≤ ENNReal.ofReal (x ^ 2) := by
  by_cases hx : 0 ≤ x
  · rw [ENNReal.ofReal_pow hx]
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx), zero_pow (by norm_num : 2 ≠ 0)]
    exact bot_le

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EvalRealCoe
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

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma LocallyL2.min {D E : X → ℝ} (hD : LocallyL2 m D) (hE : LocallyL2 m E) :
    LocallyL2 m (fun x => min (D x) (E x)) :=
  fun o R hR => (hD o R hR).inf (hE o R hR)

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

omit [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma norm_sq_eq_lintegral_enorm (D : Lp ℝ 2 m) :
    ENNReal.ofReal (‖D‖ ^ 2) = ∫⁻ x, ‖D x‖ₑ ^ 2 ∂m := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def]
  exact eLpNorm_sq_eq_lintegral D (Lp.memLp D).aestronglyMeasurable

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RealClip
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

def realClip (n : ℕ) (r : ℝ) : ℝ := max (-(n:ℝ)) (min r n)
lemma realClip_lipschitz (n : ℕ) : LipschitzWith 1 (realClip n) :=
  (LipschitzWith.id.min_const (n:ℝ)).const_max (-(n:ℝ))
lemma realClip_zero (n : ℕ) : realClip n 0 = 0 := by simp [realClip]
lemma realClip_abs_le (n : ℕ) (r : ℝ) : |realClip n r| ≤ (n:ℝ) := by
  exact abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)⟩
lemma realClip_norm_le (n : ℕ) (r : ℝ) : ‖realClip n r‖ ≤ ‖r‖ := by
  simpa only [realClip_zero, sub_zero, NNReal.coe_one, one_mul] using
    (realClip_lipschitz n).norm_sub_le r 0
lemma realClip_tendsto (r : ℝ) : Tendsto (fun n => realClip n r) atTop (𝓝 r) := by
  have he : ∀ᶠ n : ℕ in atTop, |r| ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |r|))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp only [realClip, min_eq_left (abs_le.mp hn).2, max_eq_right (abs_le.mp hn).1]

lemma realClip_tendsto_Lp (f : Lp ℝ 2 m) :
    Tendsto (fun n => (realClip_lipschitz n).compLp (realClip_zero n) f) atTop (𝓝 f) := by
  let g : ℕ → X → ℝ := fun n x => realClip n (f x)
  have hg (n : ℕ) : MemLp (g n) 2 m :=
    (realClip_lipschitz n).comp_memLp (realClip_zero n) (Lp.memLp f)
  have hi : UnifIntegrable g 2 m := by
    intro ε hε
    obtain ⟨δ,hδ,hδf⟩ := (Lp.memLp f).eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    apply le_trans (eLpNorm_mono (fun x => ?_)) (hδf s hs hms)
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx,g] using realClip_norm_le n (f x)
    · simp only [indicator_of_notMem hx,le_refl]
  have ht : UnifTight g 2 m := by
    intro ε hε
    obtain ⟨s,hs,hms,hfs⟩ := (Lp.memLp f).exists_eLpNorm_indicator_compl_lt (by norm_num) (ENNReal.coe_ne_zero.mpr hε.ne')
    refine ⟨s,hms.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono (fun x => ?_)) hfs.le
    by_cases hx : x ∈ sᶜ
    · simpa only [indicator_of_mem hx,g] using realClip_norm_le n (f x)
    · simp only [indicator_of_notMem hx,le_refl]
  have hconv := tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hg n).aestronglyMeasurable) (Lp.memLp f) hi ht
      (Eventually.of_forall fun x => realClip_tendsto (f x))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  convert hconv using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  apply eLpNorm_congr_ae
  filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) f] with x hx
  exact congrArg (fun z => z-f x) hx

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RelaxedProx
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
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma slopeGraph_hom (a : ℝ) {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2SlopeGraph m) :
    WithLp.toLp 2 (a • p.fst,|a| • p.snd) ∈ l2SlopeGraph m := by
  obtain ⟨f,hf,hm,hfp,hD⟩ := hp
  have ha := hm.const_mul a
  refine ⟨fun x => a*f x,⟨_,lipschitz_const_mul_real hf.choose_spec a⟩,ha,?_,?_⟩
  · apply Lp.ext
    filter_upwards [ha.coeFn_toLp,Lp.coeFn_smul a p.fst,hm.coeFn_toLp] with x hx hy hz
    change _ = (a • p.fst) x
    rw [hx,hy,Pi.smul_apply,smul_eq_mul,←hfp,hz]
  · filter_upwards [hD,Lp.coeFn_smul |a| p.snd] with x hx hy
    change (localSlope (fun x => a*f x) x).toReal ≤ (|a| • p.snd) x
    rw [localSlope_toReal_const_mul,hy,Pi.smul_apply,smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)

omit [BorelSpace X] in
lemma relaxedGraph_hom (a : ℝ) {f D : Lp ℝ 2 m}
    (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (a • f,|a| • D) ∈ l2RelaxedGraph m := by
  let T : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
    fun p => WithLp.toLp 2 (a • p.fst,|a| • p.snd)
  have hT : Continuous T :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      (((WithLp.continuous_fst 2 _ _).const_smul a).prodMk
        ((WithLp.continuous_snd 2 _ _).const_smul |a|))
  have H : l2SlopeGraph m ⊆ T ⁻¹' l2RelaxedGraph m := fun p hp => subset_closure (slopeGraph_hom a hp)
  exact closure_minimal H (isClosed_l2RelaxedGraph.preimage hT) hD

omit [BorelSpace X] in
lemma relaxedGraph_add {f g D E : Lp ℝ 2 m}
    (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hE : WithLp.toLp 2 (g,E) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (f+g,D+E) ∈ l2RelaxedGraph m := by
  have H := convex_l2RelaxedGraph (m := m) hD hE
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have HH := relaxedGraph_hom 2 (f := (1/2 : ℝ) • f+(1/2 : ℝ) • g)
    (D := (1/2 : ℝ) • D+(1/2 : ℝ) • E) H
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2),smul_add,smul_smul,
    show (2 : ℝ)*(1/2)=1 by norm_num,one_smul] at HH
  exact HH

omit [BorelSpace X] in
lemma relaxedGraph_zero : WithLp.toLp 2 ((0 : Lp ℝ 2 m),0) ∈ l2RelaxedGraph m := by
  apply subset_closure
  refine ⟨fun _ => 0,⟨0,LipschitzWith.const 0⟩,MemLp.zero,?_,?_⟩
  · exact MemLp.toLp_zero _
  · filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
    change (localSlope (fun _ : X => (0 : ℝ)) x).toReal ≤ (0 : Lp ℝ 2 m) x
    simp only [localSlope_zero,hx,ENNReal.toReal_zero,Pi.zero_apply,le_refl]

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

structure RelaxedProx (u : Lp ℝ 2 m) (t : ℝ) (v D : Lp ℝ 2 m) : Prop where
  graph : WithLp.toLp 2 (v,D) ∈ l2RelaxedGraph m
  variation : ∀ q E : Lp ℝ 2 m, WithLp.toLp 2 (q,E) ∈ l2RelaxedGraph m →
    ⟪u-v,q-v⟫_ℝ ≤ t^2 * ⟪D,E-D⟫_ℝ

lemma exists_relaxedProx (u : Lp ℝ 2 m) {t : ℝ} (ht : t ≠ 0) :
    ∃ v D : Lp ℝ 2 m, RelaxedProx u t v D := by
  let T : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
    fun p => WithLp.toLp 2 (p.fst,t⁻¹ • p.snd)
  let S := T ⁻¹' l2RelaxedGraph m
  have hTc : Continuous T :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      ((WithLp.continuous_fst 2 _ _).prodMk ((WithLp.continuous_snd 2 _ _).const_smul t⁻¹))
  have hScl : IsClosed S := isClosed_l2RelaxedGraph.preimage hTc
  have hSc : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    have H := convex_l2RelaxedGraph (m := m) hp hq ha hb hab
    change WithLp.toLp 2 (a • p.fst+b • q.fst,
      a • (t⁻¹ • p.snd)+b • (t⁻¹ • q.snd)) ∈ l2RelaxedGraph m at H
    change WithLp.toLp 2 (a • p.fst+b • q.fst,t⁻¹ • (a • p.snd+b • q.snd)) ∈ l2RelaxedGraph m
    simpa only [smul_add,smul_comm t⁻¹ a,smul_comm t⁻¹ b] using H
  have hSne : S.Nonempty := ⟨0,by
    change WithLp.toLp 2 (0,t⁻¹ • (0 : Lp ℝ 2 m)) ∈ l2RelaxedGraph m
    simpa only [smul_zero] using (relaxedGraph_zero (m := m))⟩
  let z := WithLp.toLp 2 (u,(0 : Lp ℝ 2 m))
  obtain ⟨w,hw,hn⟩ := exists_norm_eq_iInf_of_complete_convex hSne hScl.isComplete hSc z
  let v := w.fst
  let D := t⁻¹ • w.snd
  have hwD : w.snd = t • D := by dsimp [D]; simp only [smul_smul,mul_inv_cancel₀ ht,one_smul]
  refine ⟨v,D,hw,?_⟩
  intro q E hE
  have hq : WithLp.toLp 2 (q,t • E) ∈ S := by
    change WithLp.toLp 2 (q,t⁻¹ • (t • E)) ∈ l2RelaxedGraph m
    simpa only [smul_smul,inv_mul_cancel₀ ht,one_smul] using hE
  have H := (norm_eq_iInf_iff_real_inner_le_zero hSc hw).mp hn _ hq
  rw [WithLp.prod_inner_apply] at H
  change ⟪u-v,q-v⟫_ℝ + ⟪0-w.snd,t • E-w.snd⟫_ℝ ≤ 0 at H
  rw [zero_sub,hwD,←smul_sub,inner_neg_left,real_inner_smul_left,real_inner_smul_right] at H
  nlinarith

lemma RelaxedProx.euler {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D) :
    ⟪u-v,v⟫_ℝ = t^2 * ‖D‖^2 := by
  have H0 := h.variation 0 0 relaxedGraph_zero
  simp only [zero_sub,inner_neg_right,real_inner_self_eq_norm_sq] at H0
  have H2 := h.variation ((2 : ℝ) • v) ((2 : ℝ) • D) (by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] using relaxedGraph_hom 2 h.graph)
  rw [show (2 : ℝ) • v-v=v by module,show (2 : ℝ) • D-D=D by module,
    real_inner_self_eq_norm_sq] at H2
  linarith

lemma RelaxedProx.dual {u v D q E : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D)
    (hE : WithLp.toLp 2 (q,E) ∈ l2RelaxedGraph m) :
    |⟪u-v,q⟫_ℝ| ≤ t^2 * ‖D‖ * ‖E‖ := by
  have H := h.variation (v+q) (D+E) (relaxedGraph_add h.graph hE)
  rw [add_sub_cancel_left,add_sub_cancel_left] at H
  have hneg : WithLp.toLp 2 (-q,E) ∈ l2RelaxedGraph m := by
    simpa only [abs_neg,abs_one,neg_one_smul,one_smul] using relaxedGraph_hom (-1) hE
  have Hneg := h.variation (v+ -q) (D+E) (relaxedGraph_add h.graph hneg)
  rw [add_sub_cancel_left,add_sub_cancel_left,inner_neg_right] at Hneg
  have HB := (abs_real_inner_le_norm D E).trans' (le_abs_self _)
  have HB' := mul_le_mul_of_nonneg_left HB (sq_nonneg t)
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma RelaxedProx.displacement {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D) :
    ‖u-v‖^2 + t^2 * ‖D‖^2 = ⟪u-v,u⟫_ℝ := by
  rw [←real_inner_self_eq_norm_sq,←h.euler,←inner_add_right,sub_add_cancel]

lemma RelaxedProx.comparison {u v D q E : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D)
    (hE : WithLp.toLp 2 (q,E) ∈ l2RelaxedGraph m) :
    ‖u-v‖^2 + t^2 * ‖D‖^2 ≤ ‖u-q‖^2 + t^2 * ‖E‖^2 := by
  have H := h.variation q E hE
  have HQ := norm_sub_sq_real u q
  have HV := norm_sub_sq_real u v
  have HVQ := norm_sub_sq_real v q
  have HDE := norm_sub_sq_real D E
  simp only [inner_sub_left,inner_sub_right,
    real_inner_self_eq_norm_sq] at H
  have Hsq := sq_nonneg ‖v-q‖
  have HE := mul_nonneg (sq_nonneg t) (sq_nonneg ‖D-E‖)
  rw [HDE] at HE
  nlinarith
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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

lemma cheegerEnergy_congr_ae {f g : X → ℝ} (h : f =ᵐ[m] g) :
    cheegerEnergy m f = cheegerEnergy m g := by
  have hm : MemLp f 2 m ↔ MemLp g 2 m := memLp_congr_ae h
  have he : ∀ u : X → ℝ, eLpNorm (fun x => u x - f x) 2 m =
      eLpNorm (fun x => u x - g x) 2 m := by
    intro u
    apply eLpNorm_congr_ae
    filter_upwards [h] with x hx
    simp only [hx]
  simp only [cheegerEnergy, hm, he]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalSlopeCompContraction
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

omit [MeasurableSpace X] in
lemma localSlope_comp_contraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η)
    (f : X → ℝ) (x : X) : localSlope (η ∘ f) x ≤ localSlope f x := by
  simp only [localSlope_eq_iInf_slopeApprox]
  apply iInf_mono
  intro n
  unfold slopeApprox
  apply iSup_mono
  intro y
  apply iSup_mono
  intro _
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ dist_nonneg
  simpa only [Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul] using hη.dist_le_mul (f y) (f x)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ConstLp
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter Set WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {m : Measure X}

lemma slopeGraph_normalContraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)} (hp : p ∈ l2SlopeGraph m) :
    WithLp.toLp 2 (hη.compLp hη0 p.fst,p.snd) ∈ l2SlopeGraph m := by
  obtain ⟨f,hf,hm,hfp,hD⟩ := hp
  have ha := hη.comp_memLp hη0 hm
  refine ⟨η ∘ f,⟨_,hη.comp hf.choose_spec⟩,ha,?_,?_⟩
  · apply Lp.ext
    filter_upwards [ha.coeFn_toLp,hη.coeFn_compLp hη0 p.fst,hm.coeFn_toLp] with x hx hy hz
    change _ = hη.compLp hη0 p.fst x
    rw [hx,hy,Function.comp_apply,Function.comp_apply,←hfp,hz]
  · filter_upwards [hD] with x hx
    exact (ENNReal.toReal_mono (localSlope_ne_top hf x) (localSlope_comp_contraction hη f x)).trans hx

lemma relaxedGraph_normalContraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    {f D : Lp ℝ 2 m} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m) :
    WithLp.toLp 2 (hη.compLp hη0 f,D) ∈ l2RelaxedGraph m := by
  let T : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) → WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
    fun p => WithLp.toLp 2 (hη.compLp hη0 p.fst,p.snd)
  have hT : Continuous T :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
      (((hη.lipschitzWith_compLp hη0).continuous.comp (WithLp.continuous_fst 2 _ _)).prodMk
        (WithLp.continuous_snd 2 _ _))
  have H : l2SlopeGraph m ⊆ T ⁻¹' l2RelaxedGraph m := fun p hp =>
    subset_closure (slopeGraph_normalContraction hη hη0 hp)
  exact closure_minimal H (isClosed_l2RelaxedGraph.preimage hT) hD

lemma realClip_pairing_bound (n : ℕ) {a b : ℝ} (ha : |a| ≤ (n:ℝ)) :
    (realClip n b-b)^2 ≤ (a-b)*(realClip n b-b) := by
  rcases abs_le.mp ha with ⟨ha0,ha1⟩
  by_cases hb : b ≤ n
  · by_cases hb' : -(n:ℝ) ≤ b
    · simp only [realClip,min_eq_left hb,max_eq_right hb',sub_self,mul_zero,zero_pow (by decide : 2 ≠ 0),le_refl]
    · have hb' := le_of_lt (lt_of_not_ge hb')
      simp only [realClip,min_eq_left hb,max_eq_left hb']
      nlinarith
  · have hb := le_of_lt (lt_of_not_ge hb)
    simp only [realClip,min_eq_right hb,max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n:ℝ) ≤ n)]
    nlinarith

lemma RelaxedProx.bounded {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D)
    (n : ℕ) (hu : ∀ᵐ x ∂m, |u x| ≤ (n:ℝ)) : ∀ᵐ x ∂m, |v x| ≤ (n:ℝ) := by
  let w := (realClip_lipschitz n).compLp (realClip_zero n) v
  have hg := relaxedGraph_normalContraction (realClip_lipschitz n) (realClip_zero n) h.graph
  have H := h.variation w D hg
  simp only [sub_self,inner_zero_right,mul_zero] at H
  have HI : ⟪w-v,w-v⟫_ℝ ≤ ⟪u-v,w-v⟫_ℝ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_mono_ae (L2.integrable_inner (w-v) (w-v) (𝕜 := ℝ))
      (L2.integrable_inner (u-v) (w-v) (𝕜 := ℝ))
    filter_upwards [Lp.coeFn_sub w v,Lp.coeFn_sub u v,
      (realClip_lipschitz n).coeFn_compLp (realClip_zero n) v,hu] with x hw huv hx hu
    simp only [RCLike.inner_apply,conj_trivial,hw,huv,Pi.sub_apply]
    change (w x-v x)*(w x-v x) ≤ (w x-v x)*(u x-v x)
    change (realClip_lipschitz n).compLp (realClip_zero n) v x = realClip n (v x) at hx
    change w x = realClip n (v x) at hx
    rw [hx]
    nlinarith [realClip_pairing_bound n hu (b := v x)]
  rw [real_inner_self_eq_norm_sq] at HI
  have he : w=v := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (w-v)]))
  have hae := (realClip_lipschitz n).coeFn_compLp (realClip_zero n) v
  change (w : X → ℝ) =ᵐ[m] realClip n ∘ (v : X → ℝ) at hae
  rw [he] at hae
  filter_upwards [hae] with x hx
  rw [hx,Function.comp_apply]
  exact realClip_abs_le n (v x)

variable [IsFiniteMeasure m]
def constLp (c : ℝ) : Lp ℝ 2 m := (memLp_const c).toLp (fun _ : X => c)
omit [MetricSpace X] in
lemma constLp_coe (c : ℝ) : (constLp (m := m) c : X → ℝ) =ᵐ[m] (fun _ => c) :=
  (memLp_const c).coeFn_toLp

lemma relaxedGraph_const (c : ℝ) : WithLp.toLp 2 (constLp (m := m) c,0) ∈ l2RelaxedGraph m := by
  apply subset_closure
  refine ⟨fun _ => c,⟨0,LipschitzWith.const c⟩,memLp_const c,rfl,?_⟩
  filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
  change (localSlope (fun _ : X => c) x).toReal ≤ (0 : Lp ℝ 2 m) x
  have hs : localSlope (fun _ : X => c) x = 0 :=
    le_antisymm (by simpa using localSlope_le_lipschitz (LipschitzWith.const c) x) bot_le
  simp only [hs,hx,ENNReal.toReal_zero,Pi.zero_apply,le_refl]

lemma RelaxedProx.mass {u v D : Lp ℝ 2 m} {t : ℝ} (h : RelaxedProx u t v D) :
    (∫ x, v x ∂m) = ∫ x, u x ∂m := by
  have H := h.dual (relaxedGraph_const (m := m) 1)
  simp only [norm_zero,mul_zero] at H
  rw [L2.inner_def] at H
  have he : (∫ x, ⟪(u-v) x,constLp (m := m) 1 x⟫_ℝ ∂m) =
      (∫ x, u x ∂m) - ∫ x, v x ∂m := by
    rw [←integral_sub ((Lp.memLp u).integrable (by norm_num)) ((Lp.memLp v).integrable (by norm_num))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u v,constLp_coe (m := m) 1] with x hx hy
    simp only [RCLike.inner_apply,conj_trivial,hx,hy,Pi.sub_apply,one_mul]
  rw [he] at H
  exact (sub_eq_zero.mp (le_antisymm (abs_le.mp H).2 (by linarith [(abs_le.mp H).1]))).symm
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_LinearDensity
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
  [IsProbabilityMeasure m]

def linearDensity (ε : ℝ) (u v : Lp ℝ 2 m) (s : ℝ) : Lp ℝ 2 m :=
  constLp 1 + ε • (u+s • (v-u))

lemma linearDensity_coe (ε : ℝ) (u v : Lp ℝ 2 m) (s : ℝ) :
    (linearDensity ε u v s : X → ℝ) =ᵐ[m] (fun x => 1+ε*(u x+s*(v x-u x))) := by
  filter_upwards [Lp.coeFn_add (constLp (m := m) 1) (ε • (u+s • (v-u))),
    constLp_coe (m := m) 1,Lp.coeFn_smul ε (u+s • (v-u)),
    Lp.coeFn_add u (s • (v-u)),Lp.coeFn_smul s (v-u),Lp.coeFn_sub v u] with x h1 h2 h3 h4 h5 h6
  simp only [linearDensity,h1,Pi.add_apply,h2,h3,h4,h5,h6,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]

lemma linearDensity_mass (ε : ℝ) (u v : Lp ℝ 2 m)
    (hu : ∫ x,u x ∂m = 0) (hv : ∫ x,v x ∂m = 0) (s : ℝ) :
    (∫ x,linearDensity ε u v s x ∂m) = 1 := by
  have hui := (Lp.memLp u).integrable (by norm_num)
  have hvi := (Lp.memLp v).integrable (by norm_num)
  rw [integral_congr_ae (linearDensity_coe ε u v s)]
  have hd : Integrable (fun x => v x-u x) m := hvi.sub hui
  have hs : Integrable (fun x => s*(v x-u x)) m := hd.const_mul s
  have ha : Integrable (fun x => u x+s*(v x-u x)) m := hui.add hs
  have hε : Integrable (fun x => ε*(u x+s*(v x-u x))) m := ha.const_mul ε
  calc
    _ = (∫ x,(1:ℝ) ∂m)+(∫ x,ε*(u x+s*(v x-u x)) ∂m) :=
      integral_add (integrable_const (1:ℝ)) hε
    _ = 1 := by
      rw [integral_const_mul,integral_add hui hs,integral_const_mul,integral_sub hvi hui,hu,hv]
      simp

lemma linearDensity_bounds {ε B s : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B) (hs : s ∈ Icc (0:ℝ) 1)
    {u v : Lp ℝ 2 m} (hu : ∀ᵐ x ∂m, |u x| ≤ B) (hv : ∀ᵐ x ∂m, |v x| ≤ B) :
    ∀ᵐ x ∂m, linearDensity ε u v s x ∈ Icc (1-ε*B) (1+ε*B) := by
  filter_upwards [linearDensity_coe ε u v s,hu,hv] with x hx hu hv
  rw [hx]
  have hl : -B ≤ u x+s*(v x-u x) := by
    have h1 := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 (sub_nonneg.mpr hs.2)
    have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hv).1 hs.1
    nlinarith
  have hr : u x+s*(v x-u x) ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left (abs_le.mp hu).2 (sub_nonneg.mpr hs.2)
    have h2 := mul_le_mul_of_nonneg_left (abs_le.mp hv).2 hs.1
    nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hl hε]
  · nlinarith [mul_le_mul hr (le_refl ε) hε hB]

lemma continuous_linearDensity (ε : ℝ) (u v : Lp ℝ 2 m) : Continuous (linearDensity ε u v) := by
  unfold linearDensity
  fun_prop

lemma linearDensity_affine_deriv (ε : ℝ) (u v : Lp ℝ 2 m) (s d r : ℝ) :
    HasDerivAt (fun a : ℝ => linearDensity ε u v (s+d*a)) ((ε*d) • (v-u)) r := by
  have H := ((((hasDerivAt_id r).const_mul d).const_add s).smul_const (v-u)).const_add u
  have HH := (H.const_smul ε).const_add (constLp (m := m) 1)
  simpa only [linearDensity,smul_smul,mul_one,id_eq] using! HH

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

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

lemma evalReal_of_mem {γ : Curve X} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    evalReal γ t = γ ⟨t,ht⟩ := by
  change γ (clampTime t) = γ ⟨t,ht⟩
  apply congrArg γ
  apply Subtype.ext
  simp only [clampTime, max_eq_right ht.1, min_eq_right ht.2]

lemma metricSpeed_le_of_deriv_control {γ : Curve X} {A : ℝ → ℝ} {v t : ℝ}
    (hA : HasDerivAt A v t)
    (hdom : ∀ᶠ s in 𝓝[≠] t, dist (evalReal γ s) (evalReal γ t) ≤ |A s-A t|) :
    metricSpeed γ t ≤ ENNReal.ofReal |v| := by
  have hlim : Tendsto (fun s => ENNReal.ofReal (|A s-A t| / |s-t|))
      (𝓝[≠] t) (𝓝 (ENNReal.ofReal |v|)) := by
    simpa only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
      Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
      ENNReal.tendsto_ofReal (hasDerivAt_iff_tendsto_slope.mp hA).norm
  calc metricSpeed γ t
    _ ≤ limsup (fun s => ENNReal.ofReal (|A s-A t| / |s-t|)) (𝓝[≠] t) := by
      refine limsup_le_limsup ?_
      filter_upwards [hdom] with s hs
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs (abs_nonneg _))
    _ = ENNReal.ofReal |v| := hlim.limsup_eq

end WeakHessian

open Set Filter Topology Bornology
open scoped InnerProductSpace

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

namespace WeakHessianTransport
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

lemma lsc_real_lintegral_le_liminf {μ : Measure X} {μs : ℕ → Measure X}
    {f : X → ℝ} (hf : LowerSemicontinuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hopen : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i => ∫⁻ x, ENNReal.ofReal (f x) ∂μs i) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (ae_of_all _ hf0) hf.measurable.aemeasurable]
  calc
    ∫⁻ t in Ioi (0:ℝ), μ {x | t < f x} ≤
        ∫⁻ t in Ioi (0:ℝ), atTop.liminf (fun i => μs i {x | t < f x}) :=
      lintegral_mono fun t => hopen _ (hf.isOpen_preimage t)
    _ ≤ atTop.liminf (fun i => ∫⁻ t in Ioi (0:ℝ), μs i {x | t < f x}) :=
      lintegral_liminf_le (fun n => Antitone.measurable (fun s t hst =>
        measure_mono fun x hx => hst.trans_lt hx))

lemma lsc_lintegral_le_liminf {μ : Measure X} {μs : ℕ → Measure X}
    {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f)
    (hopen : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf (fun i => ∫⁻ x, f x ∂μs i) := by
  let g : ℕ → ℝ≥0∞ → ℝ := fun n z => (min z (n:ℝ≥0∞)).toReal
  have hfin (n : ℕ) (z : ℝ≥0∞) : min z (n:ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_right _ _)
  have hgcont (n : ℕ) : Continuous (g n) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hc : Continuous (fun w : ℝ≥0∞ => min w (n:ℝ≥0∞)) := continuous_id.min continuous_const
    exact ContinuousAt.comp (g := ENNReal.toReal) (f := fun w : ℝ≥0∞ => min w (n:ℝ≥0∞))
      (ENNReal.continuousAt_toReal (hfin n z)) hc.continuousAt
  have hgmono (n : ℕ) : Monotone (g n) := fun a b hab =>
    ENNReal.toReal_mono (hfin n b) (min_le_min_right _ hab)
  have H (n : ℕ) : (∫⁻ x, min (f x) (n:ℝ≥0∞) ∂μ) ≤
      atTop.liminf (fun i => ∫⁻ x, f x ∂μs i) := by
    have h := lsc_real_lintegral_le_liminf ((hgcont n).comp_lowerSemicontinuous hf (hgmono n))
      (fun _ => ENNReal.toReal_nonneg) hopen
    have heq : (fun x => ENNReal.ofReal (g n (f x))) = fun x => min (f x) (n:ℝ≥0∞) := by
      ext x
      exact ENNReal.ofReal_toReal (hfin n (f x))
    simp only [Function.comp_def] at h
    rw [heq] at h
    exact h.trans (liminf_le_liminf (Eventually.of_forall (fun i => lintegral_mono (fun _ => min_le_left _ _))))
  have hsup : (fun x => ⨆ n : ℕ, min (f x) (n:ℝ≥0∞)) = f := by
    ext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x, (⨆ n : ℕ, min (f x) (n:ℝ≥0∞)) ∂μ := by rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, min (f x) (n:ℝ≥0∞) ∂μ :=
      lintegral_iSup (fun n => hf.measurable.min measurable_const)
        (fun m n hmn x => min_le_min_left _ (by exact_mod_cast hmn))
    _ ≤ _ := iSup_le H

lemma lsc_lintegral_le_liminf_of_tendsto [PseudoMetrizableSpace X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    ∫⁻ x, f x ∂(μ:Measure X) ≤ atTop.liminf (fun i => ∫⁻ x, f x ∂(μs i:Measure X)) :=
  lsc_lintegral_le_liminf hf (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG)

end WeakHessianTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

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

def joinControl (u v : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 1/2 then 2*u (2*r) else 2*v (2*r-1)

lemma measurable_joinControl {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v) :
    Measurable (joinControl u v) := by
  exact Measurable.ite measurableSet_Iic
    (measurable_const.mul (hu.comp (measurable_const.mul measurable_id)))
    (measurable_const.mul (hv.comp ((measurable_const.mul measurable_id).sub measurable_const)))

lemma joinControl_sq (u v : ℝ → ℝ) :
    (fun r => (joinControl u v r)^2) = fun r => 2*joinControl (fun s => (u s)^2) (fun s => (v s)^2) r := by
  funext r
  simp only [joinControl]
  split_ifs <;> ring

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

lemma clampTime_val_eq {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) : (clampTime r : ℝ) = r := by
  simp only [clampTime, min_eq_right hr.2, max_eq_right hr.1]

end WeakHessian

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_NonnegativeParallelogram
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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianFunctional
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def energyPolar (q : V → ℝ) (f g : V) : ℝ := (q (f+g) - q (f-g))/4

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ClosedQuadraticEnergy
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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace WeakHessianFunctional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ClosedQuadraticEnergy (Q : E → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous Q
  zero : Q 0 = 0
  smul : ∀ (c : ℝ) (f : E), Q (c • f) = ENNReal.ofReal (c^2) * Q f
  parallelogram : ∀ f g, Q f < ∞ → Q g < ∞ →
    Q (f+g) + Q (f-g) = 2 * Q f + 2 * Q g

end WeakHessianFunctional

open Set Filter Bornology
open scoped Topology

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
open WeakHessian MeasureTheory
open scoped InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (m : Measure X) [IsFiniteMeasure m]

omit [CompactSpace X] in
lemma integrable_localSlope_sq {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable (fun x => (localSlope f x).toReal^2) m := by
  apply Integrable.of_bound (((measurable_localSlope hf.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable)
    ((L:ℝ)^2)
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have H := ENNReal.toReal_mono (by simp : (L:ℝ≥0∞) ≠ ∞) (localSlope_le_lipschitz hf x)
  simpa only [ENNReal.coe_toReal] using (sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg).mpr H

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

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma boundedContinuous_bounds (f : X →ᵇ ℝ) : ∀ x, -‖f‖ ≤ f x ∧ f x ≤ ‖f‖ := by
  intro x
  simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x

end WeakHessianTransport

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CompactBounded
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
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

namespace WeakHessianTransport
variable {Z : Type*} [MetricSpace Z]

def compactToBounded : C_c(Z,ℝ) →ₗ[ℝ] (Z →ᵇ ℝ) where
  toFun := CompactlySupportedContinuousMap.toBoundedContinuousFunction
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp] lemma compactToBounded_apply (f : C_c(Z,ℝ)) (x : Z) : compactToBounded f x = f x := rfl

variable [ProperSpace Z]

lemma compact_thickenedIndicator {s : Set Z} (hs : IsCompact s) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun x => (thickenedIndicator hδ s x : ℝ)) := by
  have hc : IsCompact (Metric.cthickening δ s) := hs.cthickening
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  apply Metric.thickening_subset_cthickening δ s
  by_contra h
  exact hx (by simp only [thickenedIndicator_zero hδ s h, NNReal.coe_zero])

def ballCutoff (o : Z) (n : ℕ) : C_c(Z,ℝ) :=
  ⟨⟨fun x => (thickenedIndicator (by norm_num : (0:ℝ)<1) (Metric.closedBall o n) x : ℝ),
    NNReal.continuous_coe.comp (thickenedIndicator (by norm_num : (0:ℝ)<1) (Metric.closedBall o n)).continuous⟩,
    compact_thickenedIndicator (isCompact_closedBall o n) (by norm_num)⟩

lemma ballCutoff_nonneg (o : Z) (n : ℕ) (x : Z) : 0 ≤ ballCutoff o n x := NNReal.coe_nonneg _
lemma ballCutoff_le_one (o : Z) (n : ℕ) (x : Z) : ballCutoff o n x ≤ 1 :=
  NNReal.coe_le_coe.mpr (thickenedIndicator_le_one _ _ _)
lemma ballCutoff_eq_one (o : Z) (n : ℕ) {x : Z} (hx : x ∈ Metric.closedBall o n) :
    ballCutoff o n x = 1 := by
  change (thickenedIndicator _ _ x : ℝ) = 1
  rw [thickenedIndicator_one _ _ hx]
  rfl

lemma tendsto_ballCutoff (o : Z) (x : Z) : Tendsto (fun n => ballCutoff o n x) atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (dist x o)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (ballCutoff_eq_one o n (hN.le.trans (Nat.cast_le.mpr hn))).symm

def boundedMulCompact (f : Z →ᵇ ℝ) (η : C_c(Z,ℝ)) : C_c(Z,ℝ) :=
  ⟨⟨fun x => f x*η x, f.continuous.mul η.continuous⟩,
    η.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right⟩

variable [MeasurableSpace Z] [BorelSpace Z] [Nonempty Z]

lemma exists_finite_measure_le_positive_functional
    (g : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g) :
    ∃ q : Measure Z, IsFiniteMeasure q ∧
      (∀ f : C_c(Z,ℝ), (∫ x, f x ∂q) = g (compactToBounded f)) ∧
      (∀ f : Z →ᵇ ℝ, (∀ x, 0 ≤ f x) → (∫ x, f x ∂q) ≤ g f) := by
  let Λ : C_c(Z,ℝ) →ₚ[ℝ] ℝ :=
    { g.comp compactToBounded with monotone' := fun f h hfh => hg (fun x => hfh x) }
  let q := RealRMK.rieszMeasure Λ
  let o : Z := Classical.arbitrary Z
  have hCc (f : C_c(Z,ℝ)) : (∫ x, f x ∂q) = g (compactToBounded f) :=
    RealRMK.integral_rieszMeasure Λ f
  have hb (n : ℕ) : q (Metric.closedBall o n) ≤
      ENNReal.ofReal (g (BoundedContinuousFunction.const Z 1)) := by
    exact (RealRMK.rieszMeasure_le_of_eq_one Λ (ballCutoff_nonneg o n)
      (isCompact_closedBall o n) (fun x hx => ballCutoff_eq_one o n hx)).trans
      (ENNReal.ofReal_le_ofReal (hg (fun x => ballCutoff_le_one o n x)))
  have huniv : (⋃ n : ℕ, Metric.closedBall o (n:ℝ)) = univ := by
    ext x
    simp only [mem_iUnion,Metric.mem_closedBall,mem_univ,iff_true]
    obtain ⟨n,hn⟩ := exists_nat_gt (dist x o)
    exact ⟨n,hn.le⟩
  have hmon : Monotone (fun n : ℕ => Metric.closedBall o (n:ℝ)) :=
    fun n k hnk => Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hnk)
  have htotal : q univ ≤ ENNReal.ofReal (g (BoundedContinuousFunction.const Z 1)) := by
    rw [← huniv,hmon.directed_le.measure_iUnion]
    exact iSup_le hb
  have hfinite : IsFiniteMeasure q := ⟨htotal.trans_lt ENNReal.ofReal_lt_top⟩
  let := hfinite
  refine ⟨q,hfinite,hCc,?_⟩
  intro f hf
  have hi (n : ℕ) : (∫ x, boundedMulCompact f (ballCutoff o n) x ∂q) ≤ g f := by
    rw [hCc]
    apply hg
    intro x
    exact mul_le_of_le_one_right (hf x) (ballCutoff_le_one o n x)
  have hl : Tendsto (fun n => ∫ x, boundedMulCompact f (ballCutoff o n) x ∂q)
      atTop (𝓝 (∫ x, f x ∂q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (boundedMulCompact f (ballCutoff o n)).continuous.aestronglyMeasurable
    · exact integrable_const ‖f‖
    · intro n
      exact ae_of_all _ fun x => by
        change ‖f x*ballCutoff o n x‖ ≤ ‖f‖
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg o n x)]
        exact (mul_le_of_le_one_right (norm_nonneg _) (ballCutoff_le_one o n x)).trans
          (f.norm_coe_le_norm x)
    · exact ae_of_all _ fun x => by
        change Tendsto (fun n => f x*ballCutoff o n x) atTop (𝓝 (f x))
        simpa only [mul_one] using (tendsto_const_nhds.mul (tendsto_ballCutoff o x))
  exact le_of_tendsto' hl hi
end WeakHessianTransport

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedMarginalSum
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
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def boundedMarginalSum : ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ((X×Y) →ᵇ ℝ) where
  toFun fg := fg.1.compContinuous ⟨Prod.fst,continuous_fst⟩ +
    fg.2.compContinuous ⟨Prod.snd,continuous_snd⟩
  map_add' a b := by ext p; change (a.1 p.1+b.1 p.1)+(a.2 p.2+b.2 p.2) = _; simp; ring
  map_smul' r a := by ext p; change r*a.1 p.1+r*a.2 p.2 = r*(a.1 p.1+a.2 p.2); ring

@[simp] lemma boundedMarginalSum_apply (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) (p : X×Y) :
    boundedMarginalSum fg p = fg.1 p.1 + fg.2 p.2 := rfl

lemma exists_boundedMarginal_majorant (f : (X×Y) →ᵇ ℝ) :
    ∃ fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ), f ≤ boundedMarginalSum fg := by
  refine ⟨(BoundedContinuousFunction.const X ‖f‖,0),fun p => ?_⟩
  change f p ≤ ‖f‖+0
  simpa only [add_zero] using (le_abs_self (f p)).trans (f.norm_coe_le_norm p)

def compactTensor (f : C_c(X,ℝ)) (g : C_c(Y,ℝ)) : C_c(X×Y,ℝ) :=
  ⟨⟨fun p => f p.1*g p.2,by fun_prop⟩, by
    apply (f.hasCompactSupport.prod g.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ ((isClosed_tsupport f).prod (isClosed_tsupport g))
    intro p hp
    exact ⟨subset_closure (fun h => hp (by simp [h])),subset_closure (fun h => hp (by simp [h]))⟩⟩

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

def boundedIntegral (μ : Measure X) [IsFiniteMeasure μ] : (X →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
  map_smul' r f := integral_smul r f

lemma boundedIntegral_mono (μ : Measure X) [IsFiniteMeasure μ] :
    Monotone (boundedIntegral μ) := fun f g hfg => integral_mono (f.integrable μ) (g.integrable μ) hfg

def boundedMarginalIntegral (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ((X →ᵇ ℝ) × (Y →ᵇ ℝ)) →ₗ[ℝ] ℝ :=
  (boundedIntegral μ).comp (LinearMap.fst ℝ _ _) + (boundedIntegral ν).comp (LinearMap.snd ℝ _ _)

@[simp] lemma boundedMarginalIntegral_apply (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
    boundedMarginalIntegral μ ν fg = (∫ x,fg.1 x ∂μ)+(∫ y,fg.2 y ∂ν) := rfl

variable [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]

lemma integral_boundedMarginalSum (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ)) :
    boundedIntegral (μ.prod ν) (boundedMarginalSum fg) = boundedMarginalIntegral μ ν fg := by
  change (∫ p,boundedMarginalSum fg p ∂μ.prod ν) = _
  rw [integral_prod _ ((boundedMarginalSum fg).integrable _)]
  simp only [boundedMarginalSum_apply,boundedMarginalIntegral_apply]
  have H (x : X) : (∫ y,fg.1 x+fg.2 y ∂ν) = fg.1 x+∫ y,fg.2 y ∂ν := by
    rw [integral_add (integrable_const _) (fg.2.integrable ν)]; simp
  simp_rw [H]
  rw [integral_add (fg.1.integrable μ) (integrable_const _)]
  simp

variable [ProperSpace X] [ProperSpace Y]

lemma exists_probability_of_positive_marginal_functional
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : ((X×Y) →ᵇ ℝ) →ₗ[ℝ] ℝ) (hg : Monotone g)
    (hmarg : ∀ fg, g (boundedMarginalSum fg) = boundedMarginalIntegral μ ν fg) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      ∀ f : (X×Y) →ᵇ ℝ, (∫ p,f p ∂q) = g f := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  obtain ⟨q,hq,hCc,hle⟩ := exists_finite_measure_le_positive_functional g hg
  let := hq
  have hc (r : ℝ) : g (BoundedContinuousFunction.const (X×Y) r) = r := by
    have H := hmarg (BoundedContinuousFunction.const X r,0)
    have he : boundedMarginalSum (BoundedContinuousFunction.const X r,(0 : Y →ᵇ ℝ)) =
        BoundedContinuousFunction.const (X×Y) r := by ext; simp
    rw [he] at H
    simpa only [boundedMarginalIntegral_apply,BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,integral_zero,add_zero,integral_const,probReal_univ,
      one_smul] using H
  have hup : q.real univ ≤ 1 := by
    simpa [hc] using hle (BoundedContinuousFunction.const (X×Y) 1) (fun _ => zero_le_one)
  let a : X := Classical.arbitrary X
  let b : Y := Classical.arbitrary Y
  have hcut (n : ℕ) : (∫ x,ballCutoff a n x ∂μ)+(∫ y,ballCutoff b n y ∂ν)-1 ≤ q.real univ := by
    have H := hg (show boundedMarginalSum (compactToBounded (ballCutoff a n),
        compactToBounded (ballCutoff b n))-BoundedContinuousFunction.const (X×Y) 1 ≤
        compactToBounded (compactTensor (ballCutoff a n) (ballCutoff b n)) from by
      intro p
      change ballCutoff a n p.1+ballCutoff b n p.2-1 ≤ ballCutoff a n p.1*ballCutoff b n p.2
      nlinarith [mul_nonneg (sub_nonneg.mpr (ballCutoff_le_one a n p.1))
        (sub_nonneg.mpr (ballCutoff_le_one b n p.2))])
    rw [map_sub,hmarg,hc,←hCc] at H
    apply H.trans
    have HI := integral_mono (μ := q) (compactTensor (ballCutoff a n) (ballCutoff b n)).integrable
      (integrable_const (1:ℝ)) (fun p => show ballCutoff a n p.1*ballCutoff b n p.2 ≤ 1 from
        (mul_le_of_le_one_right (ballCutoff_nonneg a n p.1) (ballCutoff_le_one b n p.2)).trans
          (ballCutoff_le_one a n p.1))
    simpa using HI
  have hlimX : Tendsto (fun n => ∫ x,ballCutoff a n x ∂μ) atTop (𝓝 1) := by
    have H := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1:ℝ))
      (fun n => (ballCutoff a n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun x => by change ‖ballCutoff a n x‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg a n x)]; exact ballCutoff_le_one a n x)
      (ae_of_all _ fun x => tendsto_ballCutoff a x)
    simpa using H
  have hlimY : Tendsto (fun n => ∫ y,ballCutoff b n y ∂ν) atTop (𝓝 1) := by
    have H := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : Y => (1:ℝ))
      (fun n => (ballCutoff b n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => ae_of_all _ fun y => by change ‖ballCutoff b n y‖ ≤ 1; rw [Real.norm_eq_abs,abs_of_nonneg (ballCutoff_nonneg b n y)]; exact ballCutoff_le_one b n y)
      (ae_of_all _ fun y => tendsto_ballCutoff b y)
    simpa using H
  have hlo : 1 ≤ q.real univ := by simpa using le_of_tendsto' ((hlimX.add hlimY).sub_const 1) hcut
  have hprob : IsProbabilityMeasure q := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top q univ) (by simp)).mp
    simpa only [ENNReal.toReal_one,Measure.real] using le_antisymm hup hlo⟩
  let := hprob
  refine ⟨q,hprob,?_⟩
  intro f
  have H := hle (f+BoundedContinuousFunction.const (X×Y) ‖f‖) (fun p => by
    change 0 ≤ f p+‖f‖
    have := (abs_le.mp (f.norm_coe_le_norm p)).1
    linarith)
  have I := hle (-f+BoundedContinuousFunction.const (X×Y) ‖f‖) (fun p => by
    change 0 ≤ -f p+‖f‖
    have := (abs_le.mp (f.norm_coe_le_norm p)).2
    linarith)
  rw [map_add,hc] at H
  rw [map_add,map_neg,hc] at I
  change (∫ p,f p+‖f‖ ∂q) ≤ _ at H
  change (∫ p,-f p+‖f‖ ∂q) ≤ _ at I
  rw [integral_add (f.integrable q) (integrable_const _)] at H
  rw [show (∫ p,-f p+‖f‖ ∂q) = (∫ p,-f p ∂q)+(∫ _ : X×Y,‖f‖ ∂q) from
    integral_add (show Integrable (fun p => -f p) q from (f.integrable q).neg) (integrable_const _),integral_neg] at I
  simp only [integral_const,probReal_univ,one_smul] at H I
  linarith

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_UpperEnvelope
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set

namespace WeakHessianTransport
variable {A E : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup E] [Module ℝ E]

lemma exists_sublinear_support (N : E → ℝ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, N (r • x) = r * N x)
    (hadd : ∀ x y, N (x+y) ≤ N x + N y) (x : E) :
    ∃ g : E →ₗ[ℝ] ℝ, g x = N x ∧ ∀ y, g y ≤ N y := by
  have hzero : N 0 = 0 := by
    have H := hhom 2 (by norm_num) 0
    simp only [smul_zero] at H
    linarith
  have hcompat : ∀ r : ℝ, r • x = 0 → r • N x = 0 := by
    intro r hr
    rcases smul_eq_zero.mp hr with hr | hx
    · simp [hr]
    · simp [hx,hzero]
  let p : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' x (N x) hcompat
  have hdom : ∀ y : p.domain, p y ≤ N y := by
    rintro ⟨y,hy⟩
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hy
    change LinearPMap.mkSpanSingleton' x (N x) hcompat ⟨r • x, _⟩ ≤ N (r • x)
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    rcases lt_trichotomy 0 r with hr | hr | hr
    · rw [hhom r hr x]
    · simp [← hr,hzero]
    · have H := hadd x (-x)
      rw [add_neg_cancel, hzero] at H
      have heq : r • x = (-r) • (-x) := by simp
      rw [heq, hhom (-r) (by linarith) (-x)]
      have H' := mul_le_mul_of_nonneg_left H (show 0 ≤ -r by linarith)
      nlinarith
  obtain ⟨g,hgp,hg⟩ := exists_extension_of_le_sublinear p N hhom hadd hdom
  refine ⟨g, ?_, hg⟩
  have hx : x ∈ p.domain := Submodule.mem_span_singleton_self x
  have H := hgp ⟨x,hx⟩
  simpa only [p, LinearPMap.mkSpanSingleton'_apply_self] using H

variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]

def upperEnvelope (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (x : E) : ℝ :=
  sInf {r | ∃ a : A, x ≤ T a ∧ r = c a}

variable (T : A →ₗ[ℝ] E) (c : A →ₗ[ℝ] ℝ) (l : E →ₗ[ℝ] ℝ)
  (hl : Monotone l) (hcomp : ∀ a, l (T a) = c a)
  (hmajor : ∀ x : E, ∃ a : A, x ≤ T a)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hmajor in
lemma envelope_nonempty (x : E) : {r | ∃ a : A, x ≤ T a ∧ r = c a}.Nonempty := by
  obtain ⟨a,ha⟩ := hmajor x
  exact ⟨c a, a, ha, rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp in
lemma envelope_bddBelow (x : E) : BddBelow {r | ∃ a : A, x ≤ T a ∧ r = c a} := by
  refine ⟨l x, ?_⟩
  rintro r ⟨a,ha,rfl⟩
  simpa only [hcomp] using hl ha

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma lower_le_envelope (x : E) : l x ≤ upperEnvelope T c x := by
  apply le_csInf (envelope_nonempty T c hmajor x)
  rintro r ⟨a,ha,rfl⟩
  simpa only [hcomp] using hl ha

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp in
lemma envelope_le (x : E) (a : A) (ha : x ≤ T a) : upperEnvelope T c x ≤ c a :=
  csInf_le (envelope_bddBelow T c l hl hcomp x) ⟨a,ha,rfl⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_image (a : A) : upperEnvelope T c (T a) = c a := by
  exact le_antisymm (envelope_le T c l hl hcomp _ a le_rfl)
    (by simpa only [hcomp] using lower_le_envelope T c l hl hcomp hmajor (T a))

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_zero : upperEnvelope T c (0 : E) = 0 := by
  simpa only [map_zero] using envelope_image T c l hl hcomp hmajor 0

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_mono : Monotone (upperEnvelope T c) := by
  intro x y hxy
  apply le_csInf (envelope_nonempty T c hmajor y)
  rintro r ⟨a,ha,rfl⟩
  exact envelope_le T c l hl hcomp x a (hxy.trans ha)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
include hmajor in
lemma envelope_lt {x : E} {r : ℝ} (hr : upperEnvelope T c x < r) :
    ∃ a : A, x ≤ T a ∧ c a < r := by
  obtain ⟨s,⟨a,ha,rfl⟩,hs⟩ := exists_lt_of_csInf_lt (envelope_nonempty T c hmajor x) hr
  exact ⟨a,ha,hs⟩

omit [PosSMulMono ℝ E] in
include hl hcomp hmajor in
lemma envelope_add (x y : E) :
    upperEnvelope T c (x+y) ≤ upperEnvelope T c x + upperEnvelope T c y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,har⟩ := envelope_lt T c hmajor (x := x) (r := upperEnvelope T c x+ε/2) (by linarith)
  obtain ⟨b,hb,hbr⟩ := envelope_lt T c hmajor (x := y) (r := upperEnvelope T c y+ε/2) (by linarith)
  have H := envelope_le T c l hl hcomp (x+y) (a+b) (by simpa only [map_add] using add_le_add ha hb)
  rw [map_add] at H
  linarith

omit [IsOrderedAddMonoid E] in
include hl hcomp hmajor in
lemma envelope_smul (r : ℝ) (hr : 0 < r) (x : E) :
    upperEnvelope T c (r • x) = r * upperEnvelope T c x := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a,ha,har⟩ := envelope_lt T c hmajor (x := x)
      (r := upperEnvelope T c x+ε/r) (lt_add_of_pos_right _ (div_pos hε hr))
    have H := envelope_le T c l hl hcomp (r • x) (r • a)
      (by simpa only [map_smul] using smul_le_smul_of_nonneg_left ha hr.le)
    rw [map_smul, smul_eq_mul] at H
    have H' := mul_lt_mul_of_pos_left har hr
    have heq : r*(upperEnvelope T c x+ε/r) = r*upperEnvelope T c x+ε := by field_simp
    rw [heq] at H'
    linarith
  · apply le_csInf (envelope_nonempty T c hmajor (r • x))
    rintro s ⟨a,ha,rfl⟩
    have hax : x ≤ T (r⁻¹ • a) := by
      have H := smul_le_smul_of_nonneg_left ha (inv_nonneg.mpr hr.le)
      simpa only [map_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using H
    have H := envelope_le T c l hl hcomp x (r⁻¹ • a) hax
    rw [map_smul, smul_eq_mul] at H
    have H' := mul_le_mul_of_nonneg_left H hr.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using H'

include hl hcomp hmajor in

lemma exists_envelope_support (x : E) :
    ∃ g : E →ₗ[ℝ] ℝ, Monotone g ∧ (∀ a, g (T a) = c a) ∧
      g x = upperEnvelope T c x := by
  obtain ⟨g,hgx,hg⟩ := exists_sublinear_support (upperEnvelope T c)
    (envelope_smul T c l hl hcomp hmajor) (envelope_add T c l hl hcomp hmajor) x
  have hpos : ∀ y : E, 0 ≤ y → 0 ≤ g y := by
    intro y hy
    have H := hg (-y)
    have H' := envelope_mono T c l hl hcomp hmajor (neg_nonpos.mpr hy)
    rw [envelope_zero T c l hl hcomp hmajor] at H'
    rw [map_neg] at H
    linarith
  refine ⟨g, ?_, ?_, hgx⟩
  · intro y z hyz
    have H := hpos (z-y) (sub_nonneg.mpr hyz)
    rw [map_sub] at H
    linarith
  · intro a
    have H := hg (T a)
    have H' := hg (T (-a))
    rw [envelope_image T c l hl hcomp hmajor] at H H'
    rw [map_neg, map_neg, map_neg] at H'
    linarith

end WeakHessianTransport

open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

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
open Set MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

local instance boundedPosSMulMono : PosSMulMono ℝ ((X×Y) →ᵇ ℝ) where
  smul_le_smul_of_nonneg_left scalar nonneg left right pointwise := fun point =>
    mul_le_mul_of_nonneg_left (a := scalar) (b := left point) (c := right point)
      (pointwise point) nonneg

lemma bounded_marginals_of_integral_identity (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : Measure (X×Y)} [IsFiniteMeasure q]
    (hq : ∀ fg, (∫ p,boundedMarginalSum fg p ∂q) = boundedMarginalIntegral μ ν fg) :
    q.map Prod.fst = μ ∧ q.map Prod.snd = ν := by
  constructor
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_fst.aemeasurable f.continuous.aestronglyMeasurable]
    have H := hq (compactToBounded f,0)
    simpa only [boundedMarginalSum_apply,boundedMarginalIntegral_apply,compactToBounded_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,add_zero,integral_zero] using H
  · apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := q) (f := f) measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
    have H := hq (0,compactToBounded f)
    simpa only [boundedMarginalSum_apply,boundedMarginalIntegral_apply,compactToBounded_apply,
      BoundedContinuousFunction.coe_zero,Pi.zero_apply,zero_add,integral_zero] using H

lemma bounded_kantorovich_duality (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (cost : (X×Y) →ᵇ ℝ) :
    ∃ q : Measure (X×Y), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      ∀ ε : ℝ, 0 < ε → ∃ fg : (X →ᵇ ℝ) × (Y →ᵇ ℝ),
        boundedMarginalSum fg ≤ cost ∧
        (∫ p,cost p ∂q) < boundedMarginalIntegral μ ν fg+ε := by
  let T := boundedMarginalSum (X := X) (Y := Y)
  let c := boundedMarginalIntegral μ ν
  let l := boundedIntegral (μ.prod ν)
  have hl : Monotone l := boundedIntegral_mono _
  have hcomp : ∀ fg,l (T fg) = c fg := integral_boundedMarginalSum μ ν
  have hmajor : ∀ f,∃ fg,f ≤ T fg := exists_boundedMarginal_majorant
  obtain ⟨g,hg,hgmarg,hgcost⟩ := exists_envelope_support T c l hl hcomp hmajor (-cost)
  obtain ⟨q,hq,hgq⟩ := exists_probability_of_positive_marginal_functional μ ν g hg hgmarg
  let := hq
  have hqsum (fg) : (∫ p,boundedMarginalSum fg p ∂q) = boundedMarginalIntegral μ ν fg :=
    (hgq (T fg)).trans (hgmarg fg)
  obtain ⟨h0,h1⟩ := bounded_marginals_of_integral_identity μ ν hqsum
  have hcq : (∫ p,cost p ∂q) = -upperEnvelope T c (-cost) := by
    have H := (hgq (-cost)).trans hgcost
    change (∫ p,-cost p ∂q) = _ at H
    rw [integral_neg] at H
    linarith
  refine ⟨q,hq,h0,h1,?_⟩
  intro ε hε
  obtain ⟨fg,hfg,hfgc⟩ := envelope_lt T c hmajor
    (x := -cost) (r := upperEnvelope T c (-cost)+ε) (by linarith)
  refine ⟨-fg,?_,?_⟩
  · change T (-fg) ≤ cost
    rw [map_neg]
    simpa only [neg_neg] using neg_le_neg hfg
  · change (∫ p,cost p ∂q) < c (-fg)+ε
    rw [hcq,map_neg]
    linarith
end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
def truncatedQuadraticCost (n : ℕ) : (X×X) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun p => min (dist p.1 p.2^2/2) (n:ℝ))
    (by fun_prop) n (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (by positivity) (Nat.cast_nonneg n))]
      exact min_le_right _ _)

omit [ProperSpace X] [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma truncatedQuadraticCost_apply (n : ℕ) (p : X×X) :
    truncatedQuadraticCost n p = min (dist p.1 p.2^2/2) (n:ℝ) := rfl

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
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [ProperSpace X] [ProperSpace Y]
  [TopologicalSpace.SeparableSpace X] [TopologicalSpace.SeparableSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

lemma probability_isTight_of_marginals (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (ProbabilityMeasure (X×Y)))
    (h0 : ∀ q ∈ S,(q : Measure (X×Y)).map Prod.fst = μ)
    (h1 : ∀ q ∈ S,(q : Measure (X×Y)).map Prod.snd = ν) :
    IsTightMeasureSet {((q:ProbabilityMeasure (X×Y)) : Measure (X×Y)) | q ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hh : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨K,hK,hKm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := μ)) (ε/2) hh
  obtain ⟨L,hL,hLm⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := ν)) (ε/2) hh
  refine ⟨K×ˢL,hK.prod hL,?_⟩
  rintro _ ⟨q,hq,rfl⟩
  have he : (K×ˢL)ᶜ = (Prod.fst ⁻¹' Kᶜ) ∪ (Prod.snd ⁻¹' Lᶜ) := by ext p; simp only [mem_compl_iff,mem_prod,not_and_or,mem_union,mem_preimage]
  calc
    (q:Measure (X×Y)) (K×ˢL)ᶜ ≤ (q:Measure (X×Y)) (Prod.fst ⁻¹' Kᶜ)+(q:Measure (X×Y)) (Prod.snd ⁻¹' Lᶜ) := by rw [he]; exact measure_union_le _ _
    _ = μ Kᶜ+ν Lᶜ := by rw [←Measure.map_apply measurable_fst hK.measurableSet.compl,
        ←Measure.map_apply measurable_snd hL.measurableSet.compl,h0 q hq,h1 q hq]
    _ ≤ ε/2+ε/2 := add_le_add (hKm μ (mem_singleton μ)) (hLm ν (mem_singleton ν))
    _ = ε := ENNReal.add_halves ε

lemma exists_coupling_limit (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (qs : ℕ → ProbabilityMeasure (X×Y))
    (h0 : ∀ n,(qs n : Measure (X×Y)).map Prod.fst = μ)
    (h1 : ∀ n,(qs n : Measure (X×Y)).map Prod.snd = ν) :
    ∃ q : ProbabilityMeasure (X×Y), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (qs ∘ φ) atTop (𝓝 q) ∧
      (q:Measure (X×Y)).map Prod.fst = μ ∧ (q:Measure (X×Y)).map Prod.snd = ν := by
  have ht := probability_isTight_of_marginals μ ν (range qs)
    (by rintro _ ⟨n,rfl⟩; exact h0 n) (by rintro _ ⟨n,rfl⟩; exact h1 n)
  obtain ⟨q,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  refine ⟨q,φ,hφ,hlim,?_,?_⟩
  · have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (qs ∘ φ) q hlim
      (continuous_fst : Continuous (Prod.fst : X×Y → X))
    have he : (fun n => (qs (φ n)).map continuous_fst.aemeasurable) = fun _ : ℕ => (⟨μ,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure X) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using h0 (φ n)
    change Tendsto (fun n => (qs (φ n)).map continuous_fst.aemeasurable) atTop _ at H
    rw [he] at H
    simpa using congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique H tendsto_const_nhds)
  · have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (qs ∘ φ) q hlim
      (continuous_snd : Continuous (Prod.snd : X×Y → Y))
    have he : (fun n => (qs (φ n)).map continuous_snd.aemeasurable) = fun _ : ℕ => (⟨ν,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : ProbabilityMeasure Y) := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa using h1 (φ n)
    change Tendsto (fun n => (qs (φ n)).map continuous_snd.aemeasurable) atTop _ at H
    rw [he] at H
    simpa using congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique H tendsto_const_nhds)
end WeakHessianTransport

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_DensityMeasure
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
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

namespace WeakHessianTransport
variable {X : Type*} [MeasurableSpace X] (m : Measure X)

def densityMeasure (ρ : Lp ℝ 2 m) : Measure X := m.withDensity (fun x => ENNReal.ofReal (ρ x))

lemma integral_densityMeasure (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x) (f : X → ℝ) :
    ∫ x, f x ∂densityMeasure m ρ = ∫ x, ρ x*f x ∂m := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (Lp.aestronglyMeasurable ρ).aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

lemma densityMeasure_le {ρ : Lp ℝ 2 m} {B : ℝ} (hρ : ∀ᵐ x ∂m, ρ x ≤ B) :
    densityMeasure m ρ ≤ ENNReal.ofReal B • m := by
  rw [densityMeasure, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [hρ] with x hx
  exact ENNReal.ofReal_le_ofReal hx

variable [IsFiniteMeasure m]
lemma densityMeasure_probability (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x)
    (hmass : ∫ x, ρ x ∂m = 1) : IsProbabilityMeasure (densityMeasure m ρ) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memLp ρ)) hρ,
    hmass, ENNReal.ofReal_one]

def densityProbability (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x)
    (hmass : ∫ x, ρ x ∂m = 1) : ProbabilityMeasure X :=
  ⟨densityMeasure m ρ, densityMeasure_probability m ρ hρ hmass⟩

end WeakHessianTransport

namespace WeakHessianTransport
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  (m : Measure X) [IsFiniteMeasure m]
lemma integral_densityMeasure_boundedContinuous (ρ : Lp ℝ 2 m) (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x)
    (f : X →ᵇ ℝ) :
    ∫ x,f x ∂densityMeasure m ρ = ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ⟫_ℝ := by
  rw [integral_densityMeasure m ρ hρ,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 m ℝ f] with x hx
  simp only [hx,RCLike.inner_apply,conj_trivial]

lemma continuous_boundedDensityProbability {T : Type*} [TopologicalSpace T]
    {ρ : T → Lp ℝ 2 m} (hcont : Continuous ρ)
    (hρ : ∀ t, ∀ᵐ x ∂m, 0 ≤ ρ t x) (hmass : ∀ t,∫ x,ρ t x ∂m = 1) :
    Continuous (fun t => densityProbability m (ρ t) (hρ t) (hmass t)) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have heq : (fun t => ∫ x,f x ∂(densityProbability m (ρ t) (hρ t) (hmass t) : Measure X)) =
      (fun t => ⟪BoundedContinuousFunction.toLp 2 m ℝ f,ρ t⟫_ℝ) := by
    funext t
    exact integral_densityMeasure_boundedContinuous m (ρ t) (hρ t) f
  rw [heq]
  exact continuous_const.inner hcont
end WeakHessianTransport

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_DualTransportPairing
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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


open Set Filter
open scoped Topology ENNReal NNReal


open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace


open Set Filter Bornology
open scoped Topology


namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma dualTransport_pairing_le
    {q ρ A : ℝ → E} {e : ℝ → ℝ} {a b α M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hα : 0 < α)
    (hq : ContinuousOn q (Icc a b)) (hρ : ContinuousOn ρ (Icc a b))
    (hyoung : ∀ t ∈ Ico a b, -α*e t + ⟪q t,A t⟫_ℝ ≤ M)
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt ρ (A t) (Ici t) t)
    (hinc : ∀ t ∈ Ico a b, ∀ s ∈ Ioc t b,
      ⟪q s-q t,ρ t⟫_ℝ ≤ -(s-t)*t/s*α*e t) :
    ⟪q b,ρ b⟫_ℝ - ⟪q a,ρ a⟫_ℝ ≤ (b-a)*M := by
  let J : ℝ → ℝ := fun t => ⟪q t,ρ t⟫_ℝ
  have hJ : ContinuousOn J (Icc a b) := hq.inner hρ
  have HB : ∀ t, HasDerivAt (fun s => J a + M*(s-a)) M t := by
    intro t
    simpa only [mul_one, id_eq] using! (((hasDerivAt_id t).sub_const a).const_mul M).const_add (J a)
  have hbound : ∀ t ∈ Ico a b, ∀ r : ℝ, M < r →
      ∃ᶠ s in 𝓝[>] t, slope J t s < r := by
    intro t ht r hr
    have ht0 : 0 < t := ha.trans_le ht.1
    have hqs : Tendsto q (𝓝[>] t) (𝓝 (q t)) :=
      (hq t (Ico_subset_Icc_self ht)).mono_left
        (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht))
    have hρs : Tendsto (slope ρ t) (𝓝[>] t) (𝓝 (A t)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp (hderiv t ht).Ioi_of_Ici
    have hl : Tendsto (fun s : ℝ => -t/s*α*e t + ⟪q s,slope ρ t s⟫_ℝ)
        (𝓝[>] t) (𝓝 (-α*e t + ⟪q t,A t⟫_ℝ)) := by
      have hrat : Tendsto (fun s : ℝ => -t/s*α*e t)
          (𝓝[>] t) (𝓝 (-α*e t)) := by
        have H : Tendsto (fun s : ℝ => -t/s*α*e t)
            (𝓝[>] t) (𝓝 (-t/t*α*e t)) :=
          (((tendsto_const_nhds.div (tendsto_id.mono_left nhdsWithin_le_nhds) ht0.ne').mul_const α).mul_const
            (e t))
        simpa [ht0.ne'] using H
      exact hrat.add (hqs.inner hρs)
    have hy : -α*e t + ⟪q t,A t⟫_ℝ ≤ M := hyoung t ht
    have hev : ∀ᶠ s in 𝓝[>] t, slope J t s < r := by
      filter_upwards [hl.eventually_lt_const (hy.trans_lt hr), Ioc_mem_nhdsGT ht.2] with s hs hsI
      apply lt_of_le_of_lt _ hs
      have hi := (div_le_div_of_nonneg_right (hinc t ht s hsI) (sub_nonneg.mpr hsI.1.le))
      have heq : slope J t s = ⟪q s-q t,ρ t⟫_ℝ/(s-t) + ⟪q s,slope ρ t s⟫_ℝ := by
        simp only [slope_def_field, slope_def_module, real_inner_smul_right, inner_sub_left,
          inner_sub_right, J]
        ring
      rw [heq]
      have he : (-(s-t)*t/s*α*e t)/(s-t) =
          -t/s*α*e t := by
        field_simp [sub_ne_zero.mpr hsI.1.ne']
      rw [he] at hi
      linarith
    exact hev.frequently
  have H := image_le_of_liminf_slope_right_le_deriv_boundary hJ
    (show J a ≤ J a+M*(a-a) by simp)
    (by fun_prop : ContinuousOn (fun s => J a+M*(s-a)) (Icc a b))
    (fun t _ => (HB t).hasDerivWithinAt) hbound (right_mem_Icc.mpr hab)
  calc
    _ ≤ M*(b-a) := by change J b-J a ≤ M*(b-a); linarith
    _ = _ := by ring

end WeakHessianFunctional

end

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

omit [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X]
  [IsProbabilityMeasure ν] in
lemma integral_densityMeasure_lp' (ρ : Lp ℝ 2 ν) (hρ : ∀ᵐ x ∂ν,0 ≤ ρ x) (f : Lp ℝ 2 ν) :
    (∫ x,f x ∂densityMeasure ν ρ) = ⟪f,ρ⟫_ℝ := by
  rw [integral_densityMeasure ν ρ hρ,L2.inner_def]
  simp only [RCLike.inner_apply,conj_trivial]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_BoundedMulLp
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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma memLp_mul_bounded {f g : X → ℝ} (hf : MemLp f 2 m)
    (hg : AEStronglyMeasurable g m) {B : ℝ} (hb : ∀ᵐ x ∂m, |g x| ≤ B) :
    MemLp (fun x => f x * g x) 2 m := by
  apply (hf.const_mul B).mono (hf.aestronglyMeasurable.mul hg)
  filter_upwards [hb] with x hx
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  calc
    |f x| * |g x| ≤ |f x| * |B| :=
      mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)
    _ = |B| * |f x| := mul_comm _ _

def boundedMulLp {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, |φ x| ≤ B) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(memLp_mul_bounded (Lp.memLp (f+g)) hφ hB).coeFn_toLp,
          Lp.coeFn_add f g,Lp.coeFn_add
            ((memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x))
            ((memLp_mul_bounded (Lp.memLp g) hφ hB).toLp (fun x => g x*φ x)),
          (memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp,
          (memLp_mul_bounded (Lp.memLp g) hφ hB).coeFn_toLp] with x hx hfg hsum hf hg
        simp only [hx,hfg,hsum,hf,hg,Pi.add_apply,add_mul]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(memLp_mul_bounded (Lp.memLp (c • f)) hφ hB).coeFn_toLp,
          Lp.coeFn_smul c f,Lp.coeFn_smul c
            ((memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x)),
          (memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp] with x hx hcf hsm hf
        simp only [hx,hcf,hsm,hf,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc] }
    |B| (by
      intro f
      change ‖(memLp_mul_bounded (Lp.memLp f) hφ hB).toLp (fun x => f x*φ x)‖ ≤ |B| * ‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp,hB] with x hx hb
      simp only [hx,Real.norm_eq_abs,abs_mul]
      calc |f x| * |φ x| ≤ |f x| * |B| :=
            mul_le_mul_of_nonneg_left (hb.trans (le_abs_self B)) (abs_nonneg _)
        _ = _ := mul_comm _ _)

lemma boundedMulLp_ae {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, |φ x| ≤ B) (f : Lp ℝ 2 m) :
    boundedMulLp hφ hB f =ᵐ[m] (fun x => f x*φ x) :=
  (memLp_mul_bounded (Lp.memLp f) hφ hB).coeFn_toLp

end WeakHessian

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma realAbs_lipschitz : LipschitzWith 1 (abs : ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y

end WeakHessian

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_BoundedMulLpTendsto
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
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
lemma boundedMulLp_tendsto {φ : ℕ → X → ℝ}
    (hφ : ∀ n,AEStronglyMeasurable (φ n) m)
    (hφ1 : ∀ n,∀ᵐ x ∂m,|φ n x| ≤ 1)
    (hconv : ∀ᵐ x ∂m,Tendsto (fun n => φ n x) atTop (𝓝 1)) (f : Lp ℝ 2 m) :
    Tendsto (fun n => boundedMulLp (hφ n) (hφ1 n) f) atTop (𝓝 f) := by
  let g : ℕ → X → ℝ := fun n x => f x*φ n x
  have hg (n : ℕ) : MemLp (g n) 2 m := memLp_mul_bounded (Lp.memLp f) (hφ n) (hφ1 n)
  have hdom (n : ℕ) : ∀ᵐ x ∂m,‖g n x‖ ≤ ‖f x‖ := by
    filter_upwards [hφ1 n] with x hx
    calc ‖g n x‖ = |f x| *|φ n x| := by simp [g]
         _ ≤ |f x| *1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
         _ = ‖f x‖ := by simp
  have hi : UnifIntegrable g 2 m := by
    intro ε hε
    obtain ⟨δ,hδ,hδf⟩ := (Lp.memLp f).eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    apply le_trans (eLpNorm_mono_ae ?_) (hδf s hs hms)
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs] using hx
    · simp only [indicator_of_notMem hxs,le_refl]
  have ht : UnifTight g 2 m := by
    intro ε hε
    obtain ⟨supportSet, hsupportSet, hfinite, hbound⟩ :=
      (unifTight_const (ι := ℕ) (by norm_num) (Lp.memLp f)).exists_measurableSet_indicator (ENNReal.coe_ne_zero.mpr hε.ne')
    refine ⟨supportSet,hfinite.ne,fun n => ?_⟩
    apply le_trans
      (eLpNorm_mono_ae ?_) (hbound n)
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ supportSetᶜ
    · simpa only [indicator_of_mem hxs] using hx
    · simp only [indicator_of_notMem hxs,le_refl]
  have hc : ∀ᵐ x ∂m,Tendsto (fun n => g n x) atTop (𝓝 (f x)) := hconv.mono fun x hx => by
    simpa only [mul_one] using hx.const_mul (f x)
  have H := tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hg n).aestronglyMeasurable) (Lp.memLp f) hi ht hc
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  apply eLpNorm_congr_ae
  filter_upwards [boundedMulLp_ae (hφ n) (hφ1 n) f] with x hx
  simp only [Pi.sub_apply,hx,g]
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ExtendLp
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m ν : Measure X}

def zeroExtendLp {s : Set X} (hs : MeasurableSet s) :
    Lp ℝ 2 (m.restrict s) →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := fun f => ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp
        (s.indicator (f : X → ℝ))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [((memLp_indicator_iff_restrict hs).mpr (Lp.memLp (f+g))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp,
          ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add
            (((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator (f : X → ℝ)))
            (((memLp_indicator_iff_restrict hs).mpr (Lp.memLp g)).toLp (s.indicator (g : X → ℝ))),
          (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)] with x hfg hf hg hadd hlocal
        rw [hfg,hadd,Pi.add_apply,hf,hg]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx,hlocal hx,Pi.add_apply]
        · simp only [indicator_of_notMem hx,add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [((memLp_indicator_iff_restrict hs).mpr (Lp.memLp (c • f))).coeFn_toLp,
          ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c
            (((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator (f : X → ℝ))),
          (ae_restrict_iff' hs).mp (Lp.coeFn_smul c f)] with x hcf hf hsm hlocal
        simp only [RingHom.id_apply]
        rw [hcf,hsm,Pi.smul_apply,hf]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx,hlocal hx,Pi.smul_apply]
        · simp only [indicator_of_notMem hx,smul_zero] }
    1 (by
      intro f
      change ‖((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator (f : X → ℝ))‖ ≤ 1*‖f‖
      rw [one_mul, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs]
      exact le_rfl)

lemma zeroExtendLp_ae {s : Set X} (hs : MeasurableSet s) (f : Lp ℝ 2 (m.restrict s)) :
    zeroExtendLp hs f =ᵐ[m] s.indicator (f : X → ℝ) :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).coeFn_toLp

def cutoffChangeLp {s : Set X} (hs : MeasurableSet s) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict s ≤ c • ν) {φ : X → ℝ}
    (hφ : AEStronglyMeasurable φ (m.restrict s)) {B : ℝ}
    (hB : ∀ᵐ x ∂m.restrict s, |φ x| ≤ B) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 m :=
  (zeroExtendLp hs).comp ((boundedMulLp hφ hB).comp (Lp.LpToLpOfMeasureLeSMul hc hlocal))

lemma cutoffChangeLp_ae {s : Set X} (hs : MeasurableSet s) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict s ≤ c • ν) {φ : X → ℝ}
    (hφ : AEStronglyMeasurable φ (m.restrict s)) {B : ℝ}
    (hB : ∀ᵐ x ∂m.restrict s, |φ x| ≤ B)
    (hz : ∀ x ∉ s, φ x = 0) (f : Lp ℝ 2 ν) :
    cutoffChangeLp hs hc hlocal hφ hB f =ᵐ[m] (fun x => f x*φ x) := by
  filter_upwards [zeroExtendLp_ae hs
    (boundedMulLp hφ hB (Lp.LpToLpOfMeasureLeSMul hc hlocal f)),
    (ae_restrict_iff' hs).mp (boundedMulLp_ae hφ hB (Lp.LpToLpOfMeasureLeSMul hc hlocal f)),
    (ae_restrict_iff' hs).mp (Lp.coeFn_LpToLpOfMeasureLeSMul hc hlocal f)] with x hx hy hz'
  change (zeroExtendLp hs (boundedMulLp hφ hB (Lp.LpToLpOfMeasureLeSMul hc hlocal f))) x = _
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs,hy hxs,hz' hxs]
  · rw [indicator_of_notMem hxs,hz x hxs,mul_zero]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalizedSlopeGraphMap
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
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X]

lemma localSlope_congr_nhds {f g : X → ℝ} {x : X} (h : f =ᶠ[𝓝 x] g) :
    localSlope f x = localSlope g x := by
  have hx : f x = g x := h.self_of_nhds
  apply Filter.limsup_congr
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  rw [hy,hx]

lemma localSlope_const (c : ℝ) (x : X) : localSlope (fun _ : X => c) x = 0 := by
  simpa [localSlope] using (Filter.limsup_const_bot (f := 𝓝[≠] x) (α := ℝ≥0∞))

lemma localSlope_zero_of_notMem_tsupport {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) :
    localSlope f x = 0 := by
  rw [localSlope_congr_nhds (g := fun _ : X => (0 : ℝ)) ?_,localSlope_const]
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

lemma localSlope_toReal_product_le {f g : X → ℝ} (hf : GloballyLipschitz f)
    (hg : GloballyLipschitz g) (x : X) :
    (localSlope (fun y => f y*g y) x).toReal ≤
      |f x| *(localSlope g x).toReal+|g x| *(localSlope f x).toReal := by
  have H := ENNReal.toReal_mono (show ENNReal.ofReal |f x| *localSlope g x+
      ENNReal.ofReal |g x| *localSlope f x ≠ ∞ by
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hg x),
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hf x)⟩)
    (localSlope_product_le hf.choose_spec hg.choose_spec x)
  simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hg x))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (localSlope_ne_top hf x)),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] using H

variable [MeasurableSpace X] [BorelSpace X] {m ν : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma localSlope_toReal_bound {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ∀ x, |(localSlope φ x).toReal| ≤ L := by
  intro x
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hφ x)).trans_eq
    (ENNReal.coe_toReal L)

lemma slopeGraph_localized {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {B : ℝ}
    (hφB : ∀ x, |φ x| ≤ B) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict (tsupport φ) ≤ c • ν)
    {f D : Lp ℝ 2 ν} (hD : WithLp.toLp 2 (f,D) ∈ l2SlopeGraph ν) :
    WithLp.toLp 2
      (cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) f,
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) D+
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
        (ae_of_all _ (localSlope_toReal_bound hφ))
        (realAbs_lipschitz.compLp abs_zero f)) ∈ l2SlopeGraph m := by
  let T := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB)
  let S := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ (localSlope_toReal_bound hφ))
  have hT (u : Lp ℝ 2 ν) : T u =ᵐ[m] (fun x => u x*φ x) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => image_eq_zero_of_notMem_tsupport hx) u
  have hS (u : Lp ℝ 2 ν) : S u =ᵐ[m] (fun x => u x*(localSlope φ x).toReal) :=
    cutoffChangeLp_ae _ hc hlocal _ _ (fun _ hx => by rw [localSlope_zero_of_notMem_tsupport hx,ENNReal.toReal_zero]) u
  let p := WithLp.toLp 2 (f,D)
  obtain ⟨u,hu,huν,hup,hDu⟩ := hD
  have hmul : GloballyLipschitz (fun x => φ x*u x) := lipschitz_mul_compact ⟨L,hφ⟩ hu hφc
  have hucoe : ∀ᵐ x ∂ν, p.fst x = u x := by rw [← hup]; exact huν.coeFn_toLp
  have hgcoe : T p.fst =ᵐ[m] (fun x => φ x*u x) := by
    filter_upwards [hT p.fst,(ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le hucoe)] with x hx hy
    rw [hx]
    by_cases hxs : x ∈ tsupport φ
    · rw [hy hxs,mul_comm]
    · simp only [image_eq_zero_of_notMem_tsupport hxs,mul_zero,zero_mul]
  have hgm : MemLp (fun x => φ x*u x) 2 m := (Lp.memLp (T p.fst)).ae_eq hgcoe
  refine ⟨_,hmul,hgm,Lp.ext (hgm.coeFn_toLp.trans hgcoe.symm),?_⟩
  filter_upwards [hT p.snd,hS (realAbs_lipschitz.compLp abs_zero p.fst),
    Lp.coeFn_add (T p.snd) (S (realAbs_lipschitz.compLp abs_zero p.fst)),
    (ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le hDu),
    (ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le hucoe),
    (ae_restrict_iff' (isClosed_tsupport φ).measurableSet).mp
      ((Measure.absolutelyContinuous_of_le_smul hlocal).ae_le
        (realAbs_lipschitz.coeFn_compLp abs_zero p.fst))] with x ht hs hadd hd huf hab
  change (localSlope (fun x => φ x*u x) x).toReal ≤
    (T p.snd+S (realAbs_lipschitz.compLp abs_zero p.fst)) x
  rw [hadd,Pi.add_apply,ht,hs]
  have H := localSlope_toReal_product_le ⟨L,hφ⟩ hu x
  rw [abs_of_nonneg (hφ0 x)] at H
  by_cases hxs : x ∈ tsupport φ
  · rw [show (realAbs_lipschitz.compLp abs_zero p.fst) x = |u x| from
      (hab hxs).trans (congrArg abs (huf hxs))]
    exact H.trans (add_le_add (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hd hxs) (hφ0 x)) le_rfl)
  · simpa only [image_eq_zero_of_notMem_tsupport hxs,
      localSlope_zero_of_notMem_tsupport hxs,ENNReal.toReal_zero,mul_zero,zero_mul,add_zero]
      using H

omit [MetricSpace X] [BorelSpace X] in
def localizedSlopeGraphMap (T S : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 m)
    (p : WithLp 2 (Lp ℝ 2 ν × Lp ℝ 2 ν)) : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) :=
  WithLp.toLp 2 (T p.fst,T p.snd+S (realAbs_lipschitz.compLp abs_zero p.fst))

omit [MetricSpace X] [BorelSpace X] in
lemma continuous_localizedSlopeGraphMap (T S : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 m) :
    Continuous (localizedSlopeGraphMap T S) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 m) (Lp ℝ 2 m)).symm.continuous.comp
    ((T.continuous.comp (WithLp.continuous_fst 2 (Lp ℝ 2 ν) (Lp ℝ 2 ν))).prodMk
     ((T.continuous.comp (WithLp.continuous_snd 2 (Lp ℝ 2 ν) (Lp ℝ 2 ν))).add
      (S.continuous.comp ((realAbs_lipschitz.continuous_compLp abs_zero).comp
        (WithLp.continuous_fst 2 (Lp ℝ 2 ν) (Lp ℝ 2 ν))))))

lemma relaxedGraph_localized {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {B : ℝ}
    (hφB : ∀ x, |φ x| ≤ B) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hlocal : m.restrict (tsupport φ) ≤ c • ν)
    {f D : Lp ℝ 2 ν} (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph ν) :
    WithLp.toLp 2
      (cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) f,
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB) D+
       cutoffChangeLp ((isClosed_tsupport φ).measurableSet) hc hlocal
        (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
        (ae_of_all _ (localSlope_toReal_bound hφ))
        (realAbs_lipschitz.compLp abs_zero f)) ∈ l2RelaxedGraph m := by
  let T := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    hφ.continuous.aestronglyMeasurable (ae_of_all _ hφB)
  let S := cutoffChangeLp (isClosed_tsupport φ).measurableSet hc hlocal
    (measurable_localSlope hφ.continuous).ennreal_toReal.aestronglyMeasurable
    (ae_of_all _ (localSlope_toReal_bound hφ))
  let P := localizedSlopeGraphMap T S
  have hP := continuous_localizedSlopeGraphMap T S
  have hraw : l2SlopeGraph ν ⊆ P ⁻¹' l2RelaxedGraph m := by
    intro p hp
    change WithLp.toLp 2 (T p.fst,T p.snd+S (realAbs_lipschitz.compLp abs_zero p.fst)) ∈ l2RelaxedGraph m
    apply subset_closure
    exact slopeGraph_localized hφ hφc hφ0 hφB hc hlocal (f := p.fst) (D := p.snd) hp
  have H := closure_minimal hraw (isClosed_l2RelaxedGraph.preimage hP) hD
  exact H
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

def imLp : Lp ℂ 2 m →L[ℝ] Lp ℝ 2 m := Complex.imCLM.compLpL 2 m

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

lemma localSlope_eq_zero_of_notMem_tsupport {f : X → ℝ} {x : X} (hx : x ∉ tsupport f) :
    localSlope f x = 0 := by
  have hn : ∀ᶠ y in 𝓝 x, f y = 0 := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  calc
    localSlope f x = localSlope (fun _ : X => (0:ℝ)) x := by
      apply Filter.limsup_congr
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with y hy
      simp only [hy, image_eq_zero_of_notMem_tsupport hx, sub_self]
    _ = 0 := localSlope_zero x

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

def relaxedDomain (m : Measure X) : Submodule ℝ (Lp ℝ 2 m) where
  carrier := {f | ∃ D : Lp ℝ 2 m,WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m}
  zero_mem' := ⟨0,relaxedGraph_zero⟩
  add_mem' := by
    rintro f g ⟨D,hD⟩ ⟨E,hE⟩
    exact ⟨D+E,relaxedGraph_add hD hE⟩
  smul_mem' := by
    rintro a f ⟨D,hD⟩
    exact ⟨|a| • D,relaxedGraph_hom a hD⟩

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RunningMin
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
namespace WeakHessianCalculus

def runningMin {X : Type*} (u : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => u 0
  | n+1 => fun x => min (runningMin u n x) (u (n+1) x)

lemma runningMin_mem {X : Type*} {S : Set (X → ℝ)} {u : ℕ → X → ℝ}
    (hu : ∀ n, u n ∈ S)
    (hmin : ∀ f ∈ S, ∀ g ∈ S, (fun x => min (f x) (g x)) ∈ S) :
    ∀ n, runningMin u n ∈ S := by
  intro n
  induction n with
  | zero => exact hu 0
  | succ n ih => exact hmin _ ih _ (hu (n+1))

lemma runningMin_antitone {X : Type*} (u : ℕ → X → ℝ) (x : X) :
    Antitone (fun n => runningMin u n x) :=
  antitone_nat_of_succ_le (fun _ => min_le_left _ _)

lemma runningMin_le {X : Type*} (u : ℕ → X → ℝ) (n : ℕ) (x : X) :
    runningMin u n x ≤ u n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

end WeakHessianCalculus

end
end InlinedFile0

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

lemma RelaxedProx.sub_const {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D) (c : ℝ) :
    RelaxedProx (u-constLp c) t (v-constLp c) D := by
  have hneg : WithLp.toLp 2 (-constLp (m := ν) c,0) ∈ l2RelaxedGraph ν := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_smul,smul_zero] using
      relaxedGraph_hom (-1) (relaxedGraph_const (m := ν) c)
  refine ⟨?_,?_⟩
  · simpa only [add_zero,sub_eq_add_neg] using relaxedGraph_add h.graph hneg
  · intro q E hE
    have H := h.variation (q+constLp c) E (by
      simpa only [add_zero] using relaxedGraph_add hE (relaxedGraph_const (m := ν) c))
    rw [show (u-constLp c)-(v-constLp c)=u-v by abel,
      show q-(v-constLp c)=q+constLp c-v by abel]
    exact H

omit [MetricSpace X] in
lemma centeredLp_mass (u : Lp ℝ 2 ν) :
    (∫ x,(u-constLp (m := ν) (∫ y,u y ∂ν) : Lp ℝ 2 ν) x ∂ν) = 0 := by
  have he : (fun x => (u-constLp (m := ν) (∫ y,u y ∂ν) : Lp ℝ 2 ν) x) =ᵐ[ν]
      fun x => u x-(∫ y,u y ∂ν) := by
    filter_upwards [Lp.coeFn_sub u (constLp (∫ y,u y ∂ν)),constLp_coe (m := ν) (∫ y,u y ∂ν)] with x hx hy
    simp only [hx,Pi.sub_apply,hy]
  rw [integral_congr_ae he,integral_sub ((Lp.memLp u).integrable (by norm_num)) (integrable_const _)]
  simp

omit [MetricSpace X] in
lemma centeredLp_bound {u : Lp ℝ 2 ν} {B : ℝ} (hu : ∀ᵐ x ∂ν,|u x| ≤ B) (c : ℝ) :
    ∀ᵐ x ∂ν,|(u-constLp (m := ν) c : Lp ℝ 2 ν) x| ≤ B+|c| := by
  filter_upwards [Lp.coeFn_sub u (constLp c),constLp_coe (m := ν) c,hu] with x hx hy hu
  simp only [hx,Pi.sub_apply,hy]
  exact (abs_sub _ _).trans (add_le_add hu le_rfl)

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_AeMinimumDominated
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
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessianCalculus

lemma exists_ae_minimum_dominated {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (S : Set (X → ℝ)) (B : X → ℝ) (hB : Integrable B ν) (hS : S.Nonempty)
    (hmeas : ∀ f ∈ S, AEMeasurable f ν)
    (hbound : ∀ f ∈ S, ∀ x, 0 ≤ f x ∧ f x ≤ B x)
    (hmin : ∀ f ∈ S, ∀ g ∈ S, (fun x => min (f x) (g x)) ∈ S)
    (hclosed : ∀ (u : ℕ → X → ℝ), (∀ n, u n ∈ S) → ∀ d : X → ℝ,
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (d x))) → d ∈ S) :
    ∃ d ∈ S, ∀ f ∈ S, ∀ᵐ x ∂ν, d x ≤ f x := by
  have hi : ∀ f ∈ S, Integrable f ν := by
    intro f hf
    apply hB.mono' (hmeas f hf).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound f hf x).1] using (hbound f hf x).2
  let E : Set ℝ := (fun f : X → ℝ => ∫ x, f x ∂ν) '' S
  have hE : E.Nonempty := hS.image _
  have hEb : BddBelow E := ⟨0, by
    rintro e ⟨f, hf, rfl⟩
    exact integral_nonneg (fun x => (hbound f hf x).1)⟩
  obtain ⟨e, _heanti, helim, he⟩ := exists_seq_tendsto_sInf hE hEb
  choose u hu hue using he
  let v := runningMin u
  have hv : ∀ n, v n ∈ S := runningMin_mem hu hmin
  let d : X → ℝ := fun x => ⨅ n, v n x
  have hvb : ∀ x, BddBelow (Set.range (fun n => v n x)) := by
    intro x
    exact ⟨0, fun _ ⟨n, hn⟩ => hn ▸ (hbound _ (hv n) x).1⟩
  have hdlim : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (d x)) :=
    fun x => tendsto_atTop_ciInf (runningMin_antitone u x) (hvb x)
  have hd : d ∈ S := hclosed v hv d hdlim
  have hevle : ∀ n, (∫ x, v n x ∂ν) ≤ e n := by
    intro n
    rw [← hue n]
    exact integral_mono (hi _ (hv n)) (hi _ (hu n)) (runningMin_le u n)
  have hlow : ∀ f ∈ S, sInf E ≤ ∫ x, f x ∂ν :=
    fun f hf => csInf_le hEb ⟨f,hf,rfl⟩
  have hvilim : Tendsto (fun n => ∫ x, v n x ∂ν) atTop (𝓝 (sInf E)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds helim
      (fun n => hlow _ (hv n)) hevle
  have hlimint : Tendsto (fun n => ∫ x, v n x ∂ν) atTop (𝓝 (∫ x, d x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun n => (hmeas _ (hv n)).aestronglyMeasurable) hB
    · intro n
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound _ (hv n) x).1] using
          (hbound _ (hv n) x).2
    · exact ae_of_all _ hdlim
  have hdenergy : (∫ x, d x ∂ν) = sInf E := tendsto_nhds_unique hlimint hvilim
  refine ⟨d, hd, ?_⟩
  intro f hf
  let z : X → ℝ := fun x => min (d x) (f x)
  have hz : z ∈ S := hmin _ hd _ hf
  have hze : (∫ x, z x ∂ν) = ∫ x, d x ∂ν := le_antisymm
    (integral_mono (hi _ hz) (hi _ hd) (fun x => min_le_left _ _))
    (hdenergy ▸ hlow _ hz)
  have hzero : (∫ x, d x - z x ∂ν) = 0 := by
    rw [integral_sub (hi _ hd) (hi _ hz), hze, sub_self]
  have hnon : ∀ᵐ x ∂ν, 0 ≤ d x - z x := ae_of_all _ fun _ => sub_nonneg.mpr (min_le_left _ _)
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnon ((hi _ hd).sub (hi _ hz))).mp hzero
  filter_upwards [heq] with x hx
  exact le_trans (le_of_eq (sub_eq_zero.mp hx)) (min_le_right _ _)



end WeakHessianCalculus

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_RadialCutoff
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
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_probability_reference (m : Measure X) (o : X) (hm : m ≠ 0)
    (hfinite : ∀ B : Set X, Bornology.IsBounded B → m B < ∞) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ ν ≪ m ∧ m ≪ ν ∧
      (∃ C : ℝ≥0, ν ≤ (C:ℝ≥0∞) • m) ∧
      ∀ B : Set X, Bornology.IsBounded B → ∃ C : ℝ≥0, m.restrict B ≤ (C:ℝ≥0∞) • ν := by
  let B : ℕ → Set X := fun n => Metric.ball o (n+1)
  obtain ⟨c,hc,hcs⟩ := ENNReal.exists_pos_tsum_mul_lt_of_countable
    (by norm_num : (1:ℝ≥0∞) ≠ 0) (fun n : ℕ => 1+m (B n))
    (fun n => ENNReal.add_ne_top.mpr ⟨by simp,(hfinite _ Metric.isBounded_ball).ne⟩)
  let μ : Measure X := Measure.sum (fun n => (c n:ℝ≥0∞) • m.restrict (B n))
  have hsum : (∑' n,(c n:ℝ≥0∞)) < 1 := (ENNReal.tsum_le_tsum fun n => by
    calc (c n:ℝ≥0∞) = 1*(c n:ℝ≥0∞) := by simp
         _ ≤ (1+m (B n))*(c n:ℝ≥0∞) := by gcongr; exact le_add_right le_rfl).trans_lt hcs
  have hμ : μ ≤ m := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [show μ s = ∑' n,(c n:ℝ≥0∞)*(m.restrict (B n)) s by
      simp only [μ,Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]]
    calc
      _ ≤ ∑' n,(c n:ℝ≥0∞)*m s := ENNReal.tsum_le_tsum fun n => by
        gcongr; exact Measure.restrict_le_self
      _ = (∑' n,(c n:ℝ≥0∞))*m s := by rw [ENNReal.tsum_mul_right]
      _ ≤ 1*m s := by gcongr
      _ = m s := one_mul _
  have hμfin : μ univ < ∞ := by
    have H : μ univ ≤ ∑' n,(1+m (B n))*(c n:ℝ≥0∞) := by
      simp only [μ,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
        smul_eq_mul,Measure.restrict_apply_univ]
      apply ENNReal.tsum_le_tsum
      intro n
      calc (c n:ℝ≥0∞)*m (B n) = m (B n)*(c n:ℝ≥0∞) := mul_comm _ _
           _ ≤ (1+m (B n))*(c n:ℝ≥0∞) := by gcongr; exact le_add_left le_rfl
    exact H.trans_lt (hcs.trans (by simp))
  have hloc (n : ℕ) : m.restrict (B n) ≤ (c n:ℝ≥0∞)⁻¹ • μ := by
    calc m.restrict (B n) = (c n:ℝ≥0∞)⁻¹ • ((c n:ℝ≥0∞) • m.restrict (B n)) := by
           rw [smul_smul,ENNReal.inv_mul_cancel (by exact_mod_cast (hc n).ne') ENNReal.coe_ne_top,one_smul]
         _ ≤ (c n:ℝ≥0∞)⁻¹ • μ := by
           gcongr
           exact Measure.le_sum (fun index => (c index:ℝ≥0∞) • m.restrict (B index)) n
  have hmμ : m ≪ μ := by
    intro s hs
    have hBn (n : ℕ) : m (s ∩ B n) = 0 := by
      have H := (Measure.absolutelyContinuous_of_le_smul (hloc n)) hs
      rw [Measure.restrict_apply' (show MeasurableSet (B n) from Metric.isOpen_ball.measurableSet)] at H
      exact H
    rw [show s = ⋃ n,s ∩ B n by
      rw [← inter_iUnion,show (⋃ n,B n)=univ from Metric.iUnion_ball_nat_succ o,inter_univ]]
    exact measure_iUnion_null hBn
  have hμne : μ ≠ 0 := by
    intro hz
    apply hm
    exact Measure.absolutelyContinuous_zero_iff.mp (hz ▸ hmμ)
  let : IsFiniteMeasure μ := ⟨hμfin⟩
  let : NeZero μ := ⟨hμne⟩
  let ν : Measure X := (μ univ)⁻¹ • μ
  have hνm : ν ≤ (μ univ)⁻¹ • m := by dsimp [ν]; gcongr
  have hμν : μ = μ univ • ν := by
    simp only [ν,smul_smul,ENNReal.mul_inv_cancel (NeZero.ne (μ univ)) hμfin.ne,one_smul]
  refine ⟨ν,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),Measure.absolutelyContinuous_of_le_smul hνm,
    hmμ.trans ?_,?_,?_⟩
  · rw [hμν]
    exact Measure.smul_absolutelyContinuous
  · refine ⟨((μ univ)⁻¹).toNNReal,?_⟩
    simpa only [ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr (NeZero.ne _))] using hνm
  · intro A hA
    obtain ⟨R,hR⟩ := hA.subset_ball o
    obtain ⟨n,hn⟩ := exists_nat_gt R
    have hAB : A ⊆ B n := hR.trans (Metric.ball_subset_ball (by exact le_trans hn.le (by linarith)))
    have H : m.restrict A ≤ ((c n:ℝ≥0∞)⁻¹*μ univ) • ν := by
      calc m.restrict A ≤ m.restrict (B n) := Measure.restrict_mono hAB le_rfl
           _ ≤ (c n:ℝ≥0∞)⁻¹ • μ := hloc n
           _ = (c n:ℝ≥0∞)⁻¹ • (μ univ • ν) := congrArg (fun ρ : Measure X => (c n:ℝ≥0∞)⁻¹ • ρ) hμν
           _ = _ := smul_smul _ _ _
    have hC : (c n:ℝ≥0∞)⁻¹*μ univ ≠ ∞ := ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast (hc n).ne')) hμfin.ne
    exact ⟨((c n:ℝ≥0∞)⁻¹*μ univ).toNNReal,by simpa only [ENNReal.coe_toNNReal hC] using H⟩
end WeakHessian

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
def radialCutoff (o : X) (n : ℕ) (x : X) : ℝ := max 0 (1-dist x o/((n:ℝ)+1))
lemma radialCutoff_nonneg (o : X) (n : ℕ) (x : X) : 0 ≤ radialCutoff o n x := le_max_left _ _
lemma radialCutoff_le_one (o : X) (n : ℕ) (x : X) : radialCutoff o n x ≤ 1 := by
  apply max_le zero_le_one
  have H : 0 ≤ dist x o/((n:ℝ)+1) := by positivity
  linarith
lemma radialCutoff_lipschitz (o : X) (n : ℕ) :
    LipschitzWith (((n:ℝ≥0)+1)⁻¹) (radialCutoff o n) := by
  apply LipschitzWith.const_max _ 0
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have ha : 0 < (n:ℝ)+1 := by positivity
  simp only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,Real.dist_eq]
  rw [show (1-dist x o/((n:ℝ)+1))-(1-dist y o/((n:ℝ)+1)) =
      (dist y o-dist x o)/((n:ℝ)+1) by ring,abs_div,abs_of_pos ha,inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by simpa only [dist_comm] using abs_dist_sub_le y x o) ha.le
lemma radialCutoff_compact [ProperSpace X] (o : X) (n : ℕ) :
    HasCompactSupport (radialCutoff o n) := by
  apply HasCompactSupport.intro (isCompact_closedBall o ((n:ℝ)+1))
  intro x hx
  have H : (n:ℝ)+1 < dist x o := lt_of_not_ge hx
  apply max_eq_left
  have : 1 < dist x o/((n:ℝ)+1) := (lt_div_iff₀ (by positivity)).mpr (by simpa using H)
  linarith
lemma radialCutoff_tendsto (o : X) (x : X) :
    Tendsto (fun n => radialCutoff o n x) atTop (𝓝 1) := by
  have H := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (dist x o)
  have HH : Tendsto (fun n : ℕ => 1-dist x o/((n:ℝ)+1)) atTop (𝓝 1) := by
    simpa only [mul_one_div,mul_zero,sub_zero] using tendsto_const_nhds.sub H
  simpa only [radialCutoff,max_eq_right zero_le_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)).max HH
end WeakHessian

end

end OAI
end


