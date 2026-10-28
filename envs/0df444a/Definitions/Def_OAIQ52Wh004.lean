-- Prove2me | Definitions.Def_OAIQ52Wh004
-- name    : OAIQ52Wh004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:42:45.366686+00:00
-- url     : https://prove2.me/theorems/1050c98b-8c21-4fd4-a213-3271ea536540
-- title:
--   Definitions bundle OAIQ52Wh004 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 19 definitions and 104 theorems. The definitions and types are `OAI.WeakHessian.EntropyCell.uniformCap`, `OAI.WeakHessian.OriginalTestGraphCore`, `OAI.WeakHessian.clipSquareLp`, `OAI.WeakHessian.decayCutoffLp`, `OAI.WeakHessian.expMulLp`, `OAI.WeakHessian.integrableDensityProbability`, `OAI.WeakHessian.planGradientEnergy`, `OAI.WeakHessian.planKineticCost`, `OAI.WeakHessian.planMoment`, `OAI.WeakHessian.smoothDensity`, `OAI.WeakHessian.timeAverageLaw`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.IsFormGenerator`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.domain`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.form`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.realEnergy`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.resolvent`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.resolventDomain`, `OAI.WeakHessianFunctional.ClosedQuadraticEnergy.resolventLinear`, `OAI.WeakHessianFunctional.NonnegativeParallelogram.bilin`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_ELpNormSq`, `WeakHessian_Curvature_DecayWeight`, `WeakHessian_Entropy_AveragedDensity`, `WeakHessian_Entropy_EntropyCell`, `WeakHessian_Entropy_NonnegativeParallelogram`, `WeakHessian_Entropy_SmoothDensity`, `WeakHessian_Geodesics_CdLogMidpointBall`, `WeakHessian_Geodesics_MidpointSigmaLower`, `WeakHessian_HeatFlow_EulerStepGenerator`, `WeakHessian_HeatFlow_FormGenerator`, `WeakHessian_HeatFlow_FormGeneratorSymmetric`, `WeakHessian_HeatFlow_HeatInverseSymbol`, `WeakHessian_HeatFlow_HeatProbability`, `WeakHessian_HeatFlow_HeatSymbol`, `WeakHessian_HeatFlow_ScaledResolventCfc`, `WeakHessian_HeatFlow_WeightedHeatPairing`, `WeakHessian_LocalBounds_ClosedQuadraticEnergy`, `WeakHessian_LocalBounds_CoreAlgebra`, `WeakHessian_LocalBounds_DecayTimesNatTwo`, `WeakHessian_LocalBounds_Domain`, `WeakHessian_LocalBounds_EulerStep`, `WeakHessian_LocalBounds_ExpMulLp`, `WeakHessian_LocalBounds_ExpNegQuadraticBound`, `WeakHessian_LocalBounds_GraphReuse`, `WeakHessian_LocalBounds_MinNatTendsto`, `WeakHessian_LocalBounds_MulBounded`, `WeakHessian_LocalBounds_RadialRoots`, `WeakHessian_LocalBounds_ReLp`, `WeakHessian_LocalBounds_SlopeApproxAntitone`, `WeakHessian_LocalBounds_SquareTimePairing`, `WeakHessian_Measure_AeIntegralPositiveLipschitz`, `WeakHessian_Measure_DecayCutoffLp`, `WeakHessian_Measure_InlinedFile0`, `WeakHessian_Measure_RadialCutoffLp`, `WeakHessian_Sobolev_AddConst`, `WeakHessian_Transport_ActionDistPrimitiveValues`, `WeakHessian_Transport_AeEvalAe`, `WeakHessian_Transport_AeProdMetricSpeed`, `WeakHessian_Transport_MeasurableVariableIntervalAction`, `WeakHessian_Transport_PlanIncrement`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`; the bundles `OAIQ52Wh000`, `OAIQ52Wh001` and `OAIQ52Wh002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ52Wh005` and `OAIQ52Wh006`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh000
import Definitions.Def_OAIQ52Wh001
import Definitions.Def_OAIQ52Wh002

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

lemma IsMinimalLocalWeakUpperGradient.change_measure {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    {f W : X → ℝ} (hw : IsMinimalLocalWeakUpperGradient m f W) :
    IsMinimalLocalWeakUpperGradient ν f W := by
  refine ⟨hw.1.of_measure_le_smul hν, ?_⟩
  intro W' hw'
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (hw.2 W' (hw'.of_measure_le_smul hm))

lemma minimalLocalWeakUpperGradient_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f W : X → ℝ) : IsMinimalLocalWeakUpperGradient m f W ↔
      IsMinimalLocalWeakUpperGradient ν f W :=
  ⟨fun h => h.change_measure hm hν, fun h => h.change_measure hν hm⟩

omit [MeasurableSpace X] [BorelSpace X] in

lemma lipschitz_endpoint_bound {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {γ : Curve X} (hγ : IsAC2 γ) :
    ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, (L : ℝ≥0∞) * metricSpeed γ t := by
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
    _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, (L : ℝ≥0∞) * metricSpeed γ t := by
      apply lintegral_mono
      intro t
      simpa only [← ofReal_norm, Real.norm_eq_abs]
        using deriv_comp_le_metricSpeed_all hf γ t

lemma lipschitz_isLocalWeakUpperGradient (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    IsLocalWeakUpperGradient m f (fun _ => (L : ℝ)) := by
  refine ⟨?_, ae_of_all m fun _ => L.coe_nonneg, ?_⟩
  · intro o R _hR
    let _ : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        hfinite (Metric.ball o R) Metric.isBounded_ball⟩
    exact memLp_const _
  · intro π hπ _hb
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1] with γ hγ
    simpa only [ENNReal.ofReal_coe_nnreal] using lipschitz_endpoint_bound hf hγ

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

lemma IsMinimalLocalWeakUpperGradient.congr_ae {f g D E : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) (hfg : f =ᵐ[m] g)
    (hDE : D =ᵐ[m] E) : IsMinimalLocalWeakUpperGradient m g E := by
  refine ⟨hD.1.congr_ae hfg hDE, ?_⟩
  intro E' hE'
  have hmin := hD.2 _ (hE'.congr_ae hfg.symm Filter.EventuallyEq.rfl)
  filter_upwards [hmin, hDE] with x hx he
  rwa [← he]

lemma exists_isMinimal_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    (∃ D, IsMinimalLocalWeakUpperGradient m f D) ↔
      ∃ D, IsMinimalLocalWeakUpperGradient m g D := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D, hD.congr_ae hfg Filter.EventuallyEq.rfl⟩
  · rintro ⟨D, hD⟩
    exact ⟨D, hD.congr_ae hfg.symm Filter.EventuallyEq.rfl⟩

lemma localSobolev_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    LocalSobolev m f ↔ LocalSobolev m g :=
  ⟨fun h => ⟨h.1.ae_eq hfg, (exists_isMinimal_congr_ae hfg).mp h.2⟩,
    fun h => ⟨h.1.ae_eq hfg.symm, (exists_isMinimal_congr_ae hfg).mpr h.2⟩⟩

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

lemma exists_upperGradient_of_cheeger_lt (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : MemLp f 2 m) {B : ℝ} (hB : 0 ≤ B)
    (he : cheegerEnergy m f < ENNReal.ofReal (B ^ 2 / 2)) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧ ‖D‖ ≤ B := by
  rw [cheegerEnergy, ite_eq_left hf, sInf_lt_iff] at he
  obtain ⟨a, ⟨fs, hfs, hconv, ha⟩, hab⟩ := he
  let u : ℕ → Lp ℝ 2 m := fun n => (hfs n).2.toLp (fs n)
  have hu : Tendsto u atTop (𝓝 (hf.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs (fun n => (hfs n).2) f hf).mpr hconv
  have hfreq : ∃ᶠ n in atTop, u n ∈ {u : Lp ℝ 2 m | ∃ D : Lp ℝ 2 m,
      IsLocalWeakUpperGradient m u D ∧ ‖D‖ ≤ B} := by
    have H := frequently_lt_of_liminf_lt (f := atTop) (b := ENNReal.ofReal (B ^ 2 / 2)) (u := fun n => (2 : ℝ≥0∞)⁻¹ *
      (∫⁻ x, localSlope (fs n) x ^ 2 ∂m)) (h := by simpa only [← ha] using hab)
    apply H.mono
    intro n hn
    obtain ⟨L, hL⟩ := (hfs n).1
    exact lipschitz_mem_upperGradient_sublevel hfinite hL (hfs n).2 hB hn.le
  obtain ⟨D, hD, hDB⟩ := (isClosed_upperGradient_sublevel (m := m) B).mem_of_frequently_of_tendsto hfreq hu
  exact ⟨D, hD.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, hDB⟩

lemma exists_upperGradient_energy_le_cheeger (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : MemLp f 2 m) (he : cheegerEnergy m f < ∞) :
    ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f D ∧
      ENNReal.ofReal (‖D‖ ^ 2 / 2) ≤ cheegerEnergy m f := by
  let a := (cheegerEnergy m f).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have haB : a < (a + 2) ^ 2 / 2 := by nlinarith [sq_nonneg a]
  have hE : cheegerEnergy m f < ENNReal.ofReal ((a + 2) ^ 2 / 2) := by
    rw [← ENNReal.ofReal_toReal he.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr haB
  obtain ⟨D₀, hD₀, _⟩ := exists_upperGradient_of_cheeger_lt hfinite hf (by linarith : 0 ≤ a + 2) hE
  obtain ⟨D, hD, hmin⟩ := exists_norm_minimal_upperGradient
    (f := hf.toLp f) ⟨D₀, hD₀.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl⟩
  refine ⟨D, hD.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrt : r = ∞
  · rw [hrt]
    exact le_top
  let B : ℝ := Real.sqrt (2 * r.toReal)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBs : B ^ 2 / 2 = r.toReal := by
    dsimp only [B]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * r.toReal)]
    ring
  have hEB : cheegerEnergy m f < ENNReal.ofReal (B ^ 2 / 2) := by
    rwa [hBs, ENNReal.ofReal_toReal hrt]
  obtain ⟨E, hE, hEn⟩ := exists_upperGradient_of_cheeger_lt hfinite hf hB hEB
  have hDE : ‖D‖ ≤ B :=
    (hmin E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)).trans hEn
  calc
    ENNReal.ofReal (‖D‖ ^ 2 / 2) ≤ ENNReal.ofReal (B ^ 2 / 2) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [norm_nonneg D]
    _ = r := by rw [hBs, ENNReal.ofReal_toReal hrt]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_MidpointSigmaLower
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma cd_midpoint_ball_volume {m : Measure X} {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {R D : ℝ}
    (hR : 0 < R) (hD : 2*R ≤ D) :
    midpointTauLower K N D * (m (Metric.ball o R))^(1/N) ≤
      (m (Metric.ball o (3*R/4)))^(1/N) := by
  let : SigmaFinite m := sigmaFinite_of_finiteOnBoundedSets m hfin o
  let A := Metric.ball o (R/12)
  let B := Metric.ball o R
  let Q := Metric.ball o (3*R/4)
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hQ : MeasurableSet Q := Metric.isOpen_ball.measurableSet
  have hApos : 0 < m A := hfull A Metric.isOpen_ball ⟨o, Metric.mem_ball_self (by positivity)⟩
  have hBpos : 0 < m B := hfull B Metric.isOpen_ball ⟨o, Metric.mem_ball_self hR⟩
  have hAfin : m A ≠ ∞ := (hfin A Metric.isBounded_ball).ne
  have hBfin : m B ≠ ∞ := (hfin B Metric.isBounded_ball).ne
  let μ₀ := normalizedRestriction m A
  let μ₁ := normalizedRestriction m B
  let : IsProbabilityMeasure μ₀ := normalizedRestriction_probability m hApos.ne' hAfin
  let : IsProbabilityMeasure μ₁ := normalizedRestriction_probability m hBpos.ne' hBfin
  have hmem₀ : ∀ᵐ x ∂μ₀, x ∈ A := normalizedRestriction_ae_mem m hA
  have hmem₁ : ∀ᵐ x ∂μ₁, x ∈ B := normalizedRestriction_ae_mem m hB
  have hmom₀ : HasSecondMoment μ₀ := hasSecondMoment_of_ae_dist_le o (R/12)
    (hmem₀.mono (fun _ hx => hx.le))
  have hmom₁ : HasSecondMoment μ₁ := hasSecondMoment_of_ae_dist_le o R
    (hmem₁.mono (fun _ hx => hx.le))
  obtain ⟨π, hπ, hgeo, hopt, hrenyi⟩ := hCD μ₀ μ₁ inferInstance inferInstance
    hmom₀ hmom₁ (normalizedRestriction_ac m A) (normalizedRestriction_ac m B)
  let := hπ
  let t : Time := ⟨1/2, by norm_num, by norm_num⟩
  have hends := hopt.1.interpolation_endpoints
  have he₀ : ∀ᵐ γ ∂π, γ timeZero ∈ A := by
    apply ae_of_ae_map (continuous_eval_const timeZero).measurable.aemeasurable
    simpa only [← hends.1, interpolation] using hmem₀
  have he₁ : ∀ᵐ γ ∂π, γ timeOne ∈ B := by
    apply ae_of_ae_map (continuous_eval_const timeOne).measurable.aemeasurable
    simpa only [← hends.2, interpolation] using hmem₁
  have hdens : ∀ᵐ γ ∂π, μ₁.rnDeriv m (γ timeOne) = (m B)⁻¹ := by
    apply ae_of_ae_map (p := fun x => μ₁.rnDeriv m x = (m B)⁻¹)
      (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ y ∂interpolation π timeOne, μ₁.rnDeriv m y = (m B)⁻¹
    rw [hends.2]
    exact rnDeriv_normalizedRestriction hB hBpos.ne'
  have hlength : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D := by
    filter_upwards [he₀, he₁] with γ h₀ h₁
    have hd := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o] at hd
    change dist (γ timeZero) o < R/12 at h₀
    change dist (γ timeOne) o < R at h₁
    linarith
  have hmid : ∀ᵐ γ ∂π, γ t ∈ Q := by
    filter_upwards [hgeo, he₀, he₁] with γ hg h₀ h₁
    have hd := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o] at hd
    have hw := dist_triangle (γ t) (γ timeZero) o
    rw [hg t timeZero] at hw
    change dist (γ timeZero) o < R/12 at h₀
    change dist (γ timeOne) o < R at h₁
    change dist (γ t) o < 3*R/4
    change dist (γ t) o ≤ |(1/2 : ℝ)-0| *
      dist (γ timeZero) (γ timeOne) + dist (γ timeZero) o at hw
    norm_num only [sub_zero, abs_of_pos (by norm_num : 0 < (1/2 : ℝ))] at hw
    linarith
  have hmidsupp : (interpolation π t) Qᶜ = 0 := by
    apply ae_iff.mp
    apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hQ).mpr
    exact hmid
  let := interpolation_probability π t
  have hu : renyiIntegral m (interpolation π t) N ≤ (m Q)^(1/N) :=
    renyiIntegral_le_support hQ hmidsupp hN
  have hl := hrenyi N le_rfl t
  refine le_trans ?_ (hl.trans hu)
  have hid : ((m B)⁻¹)^(-1/N) = (m B)^(1/N) := by
    rw [ENNReal.inv_rpow, show -1/N = -(1/N) by ring, ENNReal.rpow_neg, inv_inv]
  calc
    midpointTauLower K N D * (m B)^(1/N) =
        ∫⁻ _ : Curve X, midpointTauLower K N D * (m B)^(1/N) ∂π := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hlength, hdens] with γ hlen hrho
      refine le_trans ?_ (le_add_left le_rfl)
      rw [hrho, hid]
      exact mul_le_mul_left
        (tauCoeff_midpoint_lower hN (by linarith) dist_nonneg hlen) _

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DecayTimesNatTwo
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

lemma log_midpointTauLower {K N D : ℝ} (hN : 1 < N) :
    Real.log (midpointTauLower K N D).toReal =
      -Real.log 2-D*Real.sqrt (|K|/(N-1))*(N-1)/N := by
  have hN0 : N ≠ 0 := ne_of_gt (by linarith)
  have hs := midpointSigmaLower_pos K (N-1) D
  rw [midpointTauLower,ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/2:ℝ)),ENNReal.toReal_ofReal hs.le,
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : 0 < (1/2:ℝ)) _))
      (ne_of_gt (Real.rpow_pos_of_pos hs _)),
    Real.log_rpow (by norm_num : 0 < (1/2:ℝ)),Real.log_rpow hs]
  rw [midpointSigmaLower,
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (mul_ne_zero (by norm_num) (Real.exp_ne_zero _)),
    Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_one,Real.log_exp]
  field_simp
  ring

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_CdLogMidpointBall
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma cd_log_midpoint_ball {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {R : ℝ} (hR : 0 < R) :
    Real.log (m (Metric.ball o R)).toReal ≤
      Real.log (m (Metric.ball o (3*R/4))).toReal+N*Real.log 2+
        2*Real.sqrt (|K|/(N-1))*(N-1)*R := by
  have hN0 : 0 < N := by linarith
  have hp (r : ℝ) (hr : 0 < r) : 0 < (m (Metric.ball o r)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hr⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have hfin' := hfin (Metric.ball o (3*R/4)) Metric.isBounded_ball
  have H := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ 1/N) hfin'.ne)
    (cd_midpoint_ball_volume hN hcd hfull hfin o hR (le_refl (2*R)))
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at H
  have htpos : 0 < (midpointTauLower K N (2*R)).toReal :=
    ENNReal.toReal_pos (midpointTauLower_pos _ _ _).ne' (midpointTauLower_ne_top hN)
  have HH := Real.log_le_log (mul_pos htpos (Real.rpow_pos_of_pos (hp R hR) _)) H
  rw [Real.log_mul htpos.ne' (Real.rpow_pos_of_pos (hp R hR) _).ne',
    Real.log_rpow (hp R hR),Real.log_rpow (hp (3*R/4) (by positivity)),log_midpointTauLower hN] at HH
  have HN := mul_le_mul_of_nonneg_left HH hN0.le
  field_simp at HN
  rw [mul_comm R 3] at HN
  nlinarith

lemma cd_log_iterated_ball {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    Real.log (m (Metric.ball o R)).toReal ≤
      Real.log (m (Metric.ball o ((3/4:ℝ)^n*R))).toReal+N*Real.log 2*(n:ℝ)+
        8*Real.sqrt (|K|/(N-1))*(N-1)*R*(1-(3/4:ℝ)^n) := by
  induction n generalizing R with
  | zero => simp
  | succ n ih =>
    have HI := ih (R := 3*R/4) (by positivity)
    have HM := cd_log_midpoint_ball hN hcd hfull hfin o hR
    have he : (3/4:ℝ)^n*(3*R/4) = (3/4:ℝ)^(n+1)*R := by rw [pow_succ]; ring
    rw [he] at HI
    simp only [Nat.cast_add,Nat.cast_one,pow_succ] at HI ⊢
    nlinarith

lemma cd_log_ball_volume_le_linear {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {n : ℕ} (hn : 0 < n) :
    Real.log (m (Metric.ball o (n:ℝ))).toReal ≤
      Real.log (m (Metric.ball o 2)).toReal+
        (N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1))*(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr : 0 < (3/4:ℝ)^n*(n:ℝ) := by positivity
  have H := cd_log_iterated_ball hN hcd hfull hfin o hnR n
  have hp : 0 < (m (Metric.ball o ((3/4:ℝ)^n*(n:ℝ)))).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hr⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have Hlog := Real.log_le_log hp (ENNReal.toReal_mono (hfin (Metric.ball o 2) Metric.isBounded_ball).ne
    (measure_mono (Metric.ball_subset_ball (decay_times_nat_le_two n))))
  have HC : 0 ≤ 8*Real.sqrt (|K|/(N-1))*(N-1)*(n:ℝ) := by positivity
  nlinarith [mul_nonneg HC (pow_nonneg (by norm_num : 0 ≤ (3/4:ℝ)) n)]

lemma cd_ball_volume_bound {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (n : ℕ) :
    m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal ((m (Metric.ball o 2)).toReal*
      Real.exp ((N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1))*(n:ℝ))) := by
  by_cases hn : n = 0
  · subst n; simp
  have hnR : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : 0 < (m (Metric.ball o (n:ℝ))).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self hnR⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have hp2 : 0 < (m (Metric.ball o 2)).toReal :=
    ENNReal.toReal_pos (hfull _ Metric.isOpen_ball ⟨o,Metric.mem_ball_self (by norm_num : (0:ℝ) < 2)⟩).ne'
      (hfin _ Metric.isBounded_ball).ne
  have H := Real.exp_le_exp.mpr (cd_log_ball_volume_le_linear hN hcd hfull hfin o (Nat.pos_of_ne_zero hn))
  rw [Real.exp_log hp,Real.exp_add,Real.exp_log hp2] at H
  rw [← ENNReal.ofReal_toReal (hfin (Metric.ball o (n:ℝ)) Metric.isBounded_ball).ne]
  exact ENNReal.ofReal_le_ofReal H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatSymbol
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
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional

lemma heatSymbol_of_pos {t s : ℝ} (ht : 0 ≤ t) (hs : 0 < s) :
    heatSymbol t s = Real.exp (t-t/s) := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  · rw [heatSymbol, ite_eq_right ht.ne', expNegInvGlue, ite_eq_right (not_le.mpr (div_pos hs ht)),
      ← Real.exp_add, inv_div, sub_eq_add_neg]

lemma heatSymbol_nonpos {t s : ℝ} (ht : 0 < t) (hs : s ≤ 0) : heatSymbol t s = 0 := by
  rw [heatSymbol, ite_eq_right ht.ne', expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs ht.le),
    mul_zero]

lemma heatSymbol_le_one {t s : ℝ} (ht : 0 ≤ t) (hs : s ≤ 1) : heatSymbol t s ≤ 1 := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  by_cases hsp : 0 < s
  · rw [heatSymbol_of_pos ht.le hsp, Real.exp_le_one_iff]
    have he : t ≤ t/s := (le_div_iff₀ hsp).mpr (by nlinarith)
    linarith
  · rw [heatSymbol_nonpos ht (not_lt.mp hsp)]
    exact zero_le_one

lemma heatSymbol_add {t u s : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    heatSymbol (t+u) s = heatSymbol t s * heatSymbol u s := by
  rcases ht.eq_or_lt with ht | ht
  · simp [← ht]
  rcases hu.eq_or_lt with hu | hu
  · simp [← hu]
  by_cases hs : 0 < s
  · rw [heatSymbol_of_pos (by positivity) hs, heatSymbol_of_pos ht.le hs,
      heatSymbol_of_pos hu.le hs, ← Real.exp_add]
    congr 1
    ring
  · simp only [heatSymbol_nonpos ht (not_lt.mp hs),
      heatSymbol_nonpos hu (not_lt.mp hs), heatSymbol_nonpos (add_pos ht hu) (not_lt.mp hs), mul_zero]

lemma heatSymbol_resolvent_error {t s : ℝ} (ht : 0 ≤ t) (hs : s ∈ Icc (0:ℝ) 1) :
    |(heatSymbol t s - 1)*s| ≤ t := by
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (heatSymbol_le_one ht hs.2)) hs.1)]
  rcases hs.1.eq_or_lt with hsz | hsz
  · simpa [← hsz] using ht
  rw [heatSymbol_of_pos ht hsz]
  have H := Real.add_one_le_exp (t-t/s)
  have H' := mul_le_mul_of_nonneg_right H hsz.le
  have he : (t/s)*s = t := div_mul_cancel₀ _ hsz.ne'
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hs.2)]


open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolventHeat_add (R : H →L[ℂ] H) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    resolventHeat R (t+u) = resolventHeat R t * resolventHeat R u := by
  change cfc (heatSymbol (t+u)) R = cfc (heatSymbol t) R*cfc (heatSymbol u) R
  rw [← cfc_mul _ _ _ (heatSymbol_continuous t).continuousOn
    (heatSymbol_continuous u).continuousOn]
  exact cfc_congr fun _ _ => heatSymbol_add ht hu

lemma resolventHeat_norm_le_one {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) : ‖resolventHeat R t‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (heatSymbol_nonneg _ _)]
  exact heatSymbol_le_one ht (resolvent_spectrum_bounds hR hR1 hs).2

lemma resolventHeat_range_error {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) :
    ‖(resolventHeat R t-1)*R‖ ≤ t := by
  have hb : ‖cfc (fun s => (heatSymbol t s-1)*s) R‖ ≤ t := by
    apply norm_cfc_le ht
    intro s hs
    exact heatSymbol_resolvent_error ht (resolvent_spectrum_bounds hR hR1 hs)
  rw [cfc_mul (fun s => heatSymbol t s-1) (fun s : ℝ => s) R ((heatSymbol_continuous t).sub continuous_const).continuousOn
    continuous_id.continuousOn, cfc_sub (heatSymbol t) (fun _ => 1) R (heatSymbol_continuous t).continuousOn
    continuous_const.continuousOn, cfc_const 1 R hR.isSelfAdjoint,
    map_one] at hb
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  rw [hid] at hb
  exact hb

lemma resolventHeat_range_error_apply {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (v : H) :
    ‖resolventHeat R t (R v)-R v‖ ≤ t*‖v‖ := by
  calc
    _ = ‖((resolventHeat R t-1)*R) v‖ := rfl
    _ ≤ ‖(resolventHeat R t-1)*R‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ t*‖v‖ := mul_le_mul_of_nonneg_right (resolventHeat_range_error hR hR1 ht) (norm_nonneg _)

lemma resolventHeat_contractive {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (u v : H) :
    dist (resolventHeat R t u) (resolventHeat R t v) ≤ dist u v := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  calc
    _ ≤ ‖resolventHeat R t‖ * ‖u-v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1*‖u-v‖ := mul_le_mul_of_nonneg_right (resolventHeat_norm_le_one hR hR1 ht) (norm_nonneg _)
    _ = _ := one_mul _

end WeakHessianFunctional

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EulerStep
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
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional

lemma eulerApproximation_tendsto {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => eulerApproximation t n s) atTop (𝓝 (heatSymbol t s)) := by
  rcases hs.1.eq_or_lt with hsz | hsp
  · simp only [← hsz, eulerApproximation, eulerStep, zero_div,
      zero_pow (pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0)), heatSymbol_nonpos ht le_rfl]
    exact tendsto_const_nhds
  let a : ℝ := t*(s⁻¹-1)
  have H := (Real.tendsto_one_add_div_pow_exp a).inv₀ (Real.exp_ne_zero a)
  have Hp : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have He : (Real.exp a)⁻¹ = heatSymbol t s := by
    rw [← Real.exp_neg, heatSymbol_of_pos ht.le hsp]
    congr 1
    dsimp [a]
    simp only [div_eq_mul_inv]
    ring
  rw [He] at H
  convert H.comp Hp using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [eulerApproximation, eulerStep_of_pos _ hsp]
  simp only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat, inv_pow]
  congr 2
  dsimp [a]
  ring

lemma eulerApproximation_uniform {t : ℝ} (ht : 0 < t) :
    TendstoUniformlyOn (eulerApproximation t) (heatSymbol t) atTop (Icc (0:ℝ) 1) := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (fun n => (eulerStep_continuousOn (by positivity : 0 < t/(2:ℝ)^n)).pow (2^n))
    (fun s hs => eulerApproximation_antitone ht hs) (heatSymbol_continuous t).continuousOn
  exact fun s hs => eulerApproximation_tendsto ht hs

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_EulerStepGenerator
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
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cfc_eulerApproximation_tendsto {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => (cfc (eulerStep (t/(2:ℝ)^n)) R)^(2^n:ℕ))
      atTop (𝓝 (resolventHeat R t)) := by
  have hsub : spectrum ℝ R ⊆ Icc (0:ℝ) 1 := fun _ hs => resolvent_spectrum_bounds hR hR1 hs
  have H := tendsto_cfc_fun ((eulerApproximation_uniform ht).mono hsub)
    (Filter.Eventually.of_forall (fun n =>
      ((eulerStep_continuousOn (by positivity : 0 < t/(2:ℝ)^n)).pow (2^n)).mono hsub))
  change Tendsto _ atTop (𝓝 (cfc (heatSymbol t) R))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact (cfc_pow _ _ _ ((eulerStep_continuousOn (by positivity : 0 < t/(2:ℝ)^n)).mono hsub) hR.isSelfAdjoint).symm

end WeakHessianFunctional

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

variable {q : V → ℝ} (hq : NonnegativeParallelogram q)
include hq

lemma NonnegativeParallelogram.polar_comm (f g : V) : energyPolar q f g = energyPolar q g f := by
  have h : q (f-g) = q (g-f) := by rw [← neg_sub g f, hq.neg]
  simp only [energyPolar, add_comm f g, h]

lemma NonnegativeParallelogram.polar_add_left (f g h : V) :
    energyPolar q (f+g) h = energyPolar q f h + energyPolar q g h := by
  unfold energyPolar
  have h1 := hq.parallelogram (f+g+h) (f-h)
  have h2 := hq.parallelogram (f+g-h) (f+h)
  have h3 := hq.parallelogram (g+h) h
  have h4 := hq.parallelogram (g-h) h
  abel_nf at *
  simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_one] at *
  linarith

lemma NonnegativeParallelogram.polar_bound (f g : V) :
    |energyPolar q f g| ≤ (q f + q g)/2 := by
  rw [abs_le]
  have H := hq.parallelogram f g
  have hp := hq.nonneg (f+g)
  have hm := hq.nonneg (f-g)
  unfold energyPolar
  constructor <;> linarith

lemma NonnegativeParallelogram.polar_smul_left (a : ℝ) (f g : V) :
    energyPolar q (a • f) g = a * energyPolar q f g := by
  let T : ℝ →+ ℝ := AddMonoidHom.mk' (fun r => energyPolar q (r • f) g) (fun r s => by
    simpa only [add_smul] using hq.polar_add_left (r • f) (s • f) g)
  have hbound : IsBounded (T '' Metric.ball 0 1) := by
    apply (Metric.isBounded_closedBall (x := (0:ℝ)) (r := ((q f+q g)/2))).subset
    rintro y ⟨t, ht, rfl⟩
    change dist (energyPolar q (t • f) g) 0 ≤ (q f+q g)/2
    rw [Real.dist_eq, sub_zero]
    have H := hq.polar_bound (t • f) g
    rw [hq.smul] at H
    have ht' : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have htsq : t^2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
    have hf := hq.nonneg f
    nlinarith
  have hcont : Continuous T := T.continuous_of_isBounded_nhds_zero (Metric.ball_mem_nhds 0 (by norm_num)) hbound
  have H := map_real_smul T hcont a (1:ℝ)
  simpa only [smul_eq_mul, mul_one, T, AddMonoidHom.mk'_apply, one_smul] using H

def NonnegativeParallelogram.bilin : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (energyPolar q) hq.polar_add_left hq.polar_smul_left
    (fun f g h => by rw [hq.polar_comm, hq.polar_add_left, hq.polar_comm g,
      hq.polar_comm h])
    (fun a f g => by
      simp only [smul_eq_mul]
      rw [hq.polar_comm, hq.polar_smul_left, hq.polar_comm g])

lemma NonnegativeParallelogram.polar_self (f : V) : energyPolar q f f = q f := by
  have H := hq.smul 2 f
  have heq : (2:ℝ) • f = f+f := by module
  rw [heq] at H
  simp only [energyPolar, sub_self, hq.zero]
  linarith

lemma NonnegativeParallelogram.polar_add (f g : V) :
    q (f+g) = q f + 2 * energyPolar q f g + q g := by
  have H := hq.parallelogram f g
  unfold energyPolar
  linarith

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

variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
include hQ

lemma ClosedQuadraticEnergy.add_lt_top {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    Q (f+g) < ∞ := by
  have H := hQ.parallelogram f g hf hg
  have ht : 2 * Q f + 2 * Q g < ∞ := by finiteness
  exact (le_add_right le_rfl).trans_lt (H ▸ ht)

lemma ClosedQuadraticEnergy.sub_lt_top {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    Q (f-g) < ∞ := by
  have H := hQ.parallelogram f g hf hg
  have ht : 2 * Q f + 2 * Q g < ∞ := by finiteness
  exact (le_add_left le_rfl).trans_lt (H ▸ ht)

lemma ClosedQuadraticEnergy.midpoint_lt_top {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    Q ((1/2 : ℝ) • (f+g)) < ∞ := by
  rw [hQ.smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hQ.add_lt_top hf hg)

lemma ClosedQuadraticEnergy.midpoint_le {f g : E} (hf : Q f < ∞) (hg : Q g < ∞) :
    (Q ((1/2 : ℝ) • (f+g))).toReal ≤ (Q f).toReal / 2 + (Q g).toReal / 2 := by
  have H := congrArg ENNReal.toReal (hQ.parallelogram f g hf hg)
  rw [ENNReal.toReal_add (hQ.add_lt_top hf hg).ne (hQ.sub_lt_top hf hg).ne,
    ENNReal.toReal_add (by finiteness) (by finiteness)] at H
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at H
  rw [hQ.smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have := ENNReal.toReal_nonneg (a := Q (f-g))
  norm_num
  nlinarith

lemma ClosedQuadraticEnergy.proximal_midpoint {u f g : E}
    (hf : Q f < ∞) (hg : Q g < ∞) :
    (proximalFunctional Q u ((1/2:ℝ) • (f+g))).toReal + ‖f-g‖^2/8 ≤
      ((proximalFunctional Q u f).toReal + (proximalFunctional Q u g).toReal)/2 := by
  rw [proximalFunctional_toReal (hQ.midpoint_lt_top hf hg),
    proximalFunctional_toReal hf, proximalFunctional_toReal hg]
  have H := hQ.midpoint_le hf hg
  have hn := parallelogram_law_with_norm_mul ℝ (f-u) (g-u)
  simp only [← pow_two] at hn
  have e1 : f-u + (g-u) = (2:ℝ) • ((1/2:ℝ) • (f+g)-u) := by module
  have e2 : f-u - (g-u) = f-g := by abel
  rw [e1, e2, norm_smul] at hn
  norm_num at hn
  simp only [smul_add] at H ⊢
  nlinarith

lemma ClosedQuadraticEnergy.lowerSemicontinuous_proximal (u : E) :
    LowerSemicontinuous (proximalFunctional Q u) := by
  exact hQ.lowerSemicontinuous.add
    (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous (fun f : E => ‖f-u‖^2/2))).lowerSemicontinuous

lemma ClosedQuadraticEnergy.exists_minimizer [CompleteSpace E] (u : E) :
    ∃ f : E, ∀ g : E, proximalFunctional Q u f ≤ proximalFunctional Q u g := by
  let J := proximalFunctional Q u
  let a : ℝ≥0∞ := ⨅ f : E, J f
  have hJ0 : J 0 < ∞ := proximalFunctional_lt_top (by rw [hQ.zero]; simp)
  have ha : a < ∞ := (iInf_le J 0).trans_lt hJ0
  let δ : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have hδpos : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex : ∀ n, ∃ f, J f < ENNReal.ofReal (a.toReal + δ n) := by
    intro n
    apply iInf_lt_iff.mp
    change a < ENNReal.ofReal (a.toReal + δ n)
    apply (ENNReal.toReal_lt_toReal ha.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith [hδpos n]
  choose fs hs using hex
  have hJfin : ∀ n, J (fs n) < ∞ := fun n => (hs n).trans ENNReal.ofReal_lt_top
  have hQfin : ∀ n, Q (fs n) < ∞ := fun n => (le_add_right le_rfl).trans_lt (hJfin n)
  have hsmall : ∀ n, (J (fs n)).toReal < a.toReal + δ n := by
    intro n
    have H := (ENNReal.toReal_lt_toReal (hJfin n).ne ENNReal.ofReal_ne_top).mpr (hs n)
    rwa [ENNReal.toReal_ofReal (by positivity)] at H
  have hsq : ∀ n k, ‖fs n - fs k‖^2 ≤ 4 * (δ n + δ k) := by
    intro n k
    have H := hQ.proximal_midpoint (u := u) (hQfin n) (hQfin k)
    have hmid := hQ.midpoint_lt_top (hQfin n) (hQfin k)
    have hlo : a.toReal ≤ (J ((1/2:ℝ) • (fs n + fs k))).toReal :=
      (ENNReal.toReal_le_toReal ha.ne (proximalFunctional_lt_top hmid).ne).mpr (iInf_le J _)
    change (J _).toReal + _ ≤ ((J _).toReal + (J _).toReal)/2 at H
    linarith [hsmall n, hsmall k]
  have hC : CauchySeq fs := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hsmallδ : ∀ᶠ n in atTop, δ n < ε^2/16 :=
      hδ.eventually_lt_const (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hsmallδ
    refine ⟨N, fun n hn k hk => ?_⟩
    rw [dist_eq_norm]
    have := hsq n k
    have := hN n hn
    have := hN k hk
    nlinarith [norm_nonneg (fs n-fs k)]
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hC
  have hr : Tendsto (fun n => ENNReal.ofReal (a.toReal + δ n)) atTop (𝓝 a) := by
    have H := (ENNReal.continuous_ofReal.tendsto (a.toReal + 0)).comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a.toReal) atTop (𝓝 a.toReal)).add hδ)
    simpa only [add_zero, ENNReal.ofReal_toReal ha.ne, Function.comp_def] using H
  have hmin : (f, a) ∈ {p : E × ℝ≥0∞ | J p.1 ≤ p.2} :=
    (hQ.lowerSemicontinuous_proximal u).isClosed_epigraph.mem_of_tendsto
      (f := fun n => (fs n, ENNReal.ofReal (a.toReal + δ n)))
      (by simpa only [nhds_prod_eq] using hf.prodMk hr) (Eventually.of_forall fun n => (hs n).le)
  exact ⟨f, fun g => hmin.trans (iInf_le J g)⟩

lemma ClosedQuadraticEnergy.minimizer_unique {u f g : E}
    (hf : ∀ v, proximalFunctional Q u f ≤ proximalFunctional Q u v)
    (hg : ∀ v, proximalFunctional Q u g ≤ proximalFunctional Q u v) : f = g := by
  let J := proximalFunctional Q u
  have hJ0 : J 0 < ∞ := proximalFunctional_lt_top (by rw [hQ.zero]; simp)
  have hJf : J f < ∞ := (hf 0).trans_lt hJ0
  have hJg : J g < ∞ := (hg 0).trans_lt hJ0
  have hQf : Q f < ∞ := (le_add_right le_rfl).trans_lt hJf
  have hQg : Q g < ∞ := (le_add_right le_rfl).trans_lt hJg
  have H := hQ.proximal_midpoint (u := u) hQf hQg
  have hm := hQ.midpoint_lt_top hQf hQg
  have hfm : (J f).toReal ≤ (J ((1/2:ℝ) • (f+g))).toReal :=
    (ENNReal.toReal_le_toReal hJf.ne (proximalFunctional_lt_top hm).ne).mpr (hf _)
  have hgf : (J g).toReal ≤ (J f).toReal :=
    (ENNReal.toReal_le_toReal hJg.ne hJf.ne).mpr (hg f)
  change (J _).toReal + _ ≤ ((J _).toReal + (J _).toReal)/2 at H
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (f-g)]

end WeakHessianFunctional

open Set Filter Bornology
open scoped Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Domain
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

def ClosedQuadraticEnergy.domain : Submodule ℝ E where
  carrier := {f | Q f < ∞}
  zero_mem' := by simp [hQ.zero]
  add_mem' := hQ.add_lt_top
  smul_mem' := by
    intro a f hf
    change Q (a • f) < ∞
    rw [hQ.smul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

def ClosedQuadraticEnergy.realEnergy (f : hQ.domain) : ℝ := (Q f).toReal

lemma ClosedQuadraticEnergy.realEnergy_quadratic :
    NonnegativeParallelogram hQ.realEnergy where
  nonneg _ := ENNReal.toReal_nonneg
  smul a f := by
    change (Q (a • (f:E))).toReal = _
    rw [hQ.smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
    rfl
  parallelogram f g := by
    have H := congrArg ENNReal.toReal (hQ.parallelogram f g f.property g.property)
    rw [ENNReal.toReal_add (hQ.add_lt_top f.property g.property).ne
      (hQ.sub_lt_top f.property g.property).ne,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) f.property.ne)
        (ENNReal.mul_ne_top (by norm_num) g.property.ne)] at H
    simpa only [ClosedQuadraticEnergy.realEnergy, Submodule.coe_add, Submodule.coe_sub,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat] using H

def ClosedQuadraticEnergy.form : hQ.domain →ₗ[ℝ] hQ.domain →ₗ[ℝ] ℝ :=
  hQ.realEnergy_quadratic.bilin

lemma ClosedQuadraticEnergy.form_apply (f g : hQ.domain) :
    hQ.form f g = energyPolar hQ.realEnergy f g := rfl

lemma ClosedQuadraticEnergy.form_comm (f g : hQ.domain) : hQ.form f g = hQ.form g f :=
  hQ.realEnergy_quadratic.polar_comm f g

lemma ClosedQuadraticEnergy.form_self (f : hQ.domain) :
    hQ.form f f = hQ.realEnergy f := hQ.realEnergy_quadratic.polar_self f

lemma ClosedQuadraticEnergy.realEnergy_add (f g : hQ.domain) :
    hQ.realEnergy (f+g) = hQ.realEnergy f + 2*hQ.form f g + hQ.realEnergy g :=
  hQ.realEnergy_quadratic.polar_add f g

lemma ClosedQuadraticEnergy.proximal_expansion (u : E) (f v : hQ.domain) (t : ℝ) :
    (proximalFunctional Q u (f + t • v)).toReal =
      (proximalFunctional Q u f).toReal +
      t * (2*hQ.form f v + ⟪(f:E)-u, (v:E)⟫_ℝ) +
      t^2 * (hQ.realEnergy v + ‖(v:E)‖^2/2) := by
  have hft : Q ((f:E)+t • (v:E)) < ∞ := (f+t • v).property
  rw [proximalFunctional_toReal hft, proximalFunctional_toReal f.property]
  change hQ.realEnergy (f+t • v) + ‖(f:E) + t • (v:E)-u‖^2/2 = _
  rw [hQ.realEnergy_add, hQ.realEnergy_quadratic.smul]
  have hn : ‖(f:E) + t • (v:E)-u‖^2 =
      ‖(f:E)-u‖^2 + 2*t*⟪(f:E)-u,(v:E)⟫_ℝ + t^2*‖(v:E)‖^2 := by
    have e : (f:E) + t • (v:E)-u = ((f:E)-u) + t • (v:E) := by module
    rw [e, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      inner_smul_right, real_inner_comm (v:E) ((f:E)-u), real_inner_self_eq_norm_sq]
    ring
  rw [hn, map_smul, smul_eq_mul]
  change hQ.realEnergy f + _ + _ + _ = hQ.realEnergy f + _ + _ + _
  ring

lemma ClosedQuadraticEnergy.minimizer_iff_euler (u : E) (f : hQ.domain) :
    (∀ g : E, proximalFunctional Q u f ≤ proximalFunctional Q u g) ↔
      ∀ v : hQ.domain, 2*hQ.form f v + ⟪(f:E)-u,(v:E)⟫_ℝ = 0 := by
  constructor
  · intro hf v
    let a := hQ.realEnergy v + ‖(v:E)‖^2/2
    let b := 2*hQ.form f v + ⟪(f:E)-u,(v:E)⟫_ℝ
    let c := (proximalFunctional Q u f).toReal
    have hmin : IsLocalMin (fun t : ℝ => c + t*b + t^2*a) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      have H := (ENNReal.toReal_le_toReal (proximalFunctional_lt_top f.property).ne
        (proximalFunctional_lt_top (f+t • v).property).ne).mpr (hf (f+t • v))
      simp only [Submodule.coe_add, Submodule.coe_smul] at H
      rw [hQ.proximal_expansion] at H
      simpa [a,b,c] using H
    have hd : HasDerivAt (fun t : ℝ => c + t*b + t^2*a) b 0 := by
      convert (((hasDerivAt_const (0:ℝ) c).add ((hasDerivAt_id (0:ℝ)).mul_const b)).add
        (((hasDerivAt_id (0:ℝ)).pow 2).mul_const a)) using 1 <;> first | rfl | simp
    exact hmin.hasDerivAt_eq_zero hd
  · intro hf g
    by_cases hg : Q g < ∞
    · let v : hQ.domain := ⟨g-(f:E), hQ.sub_lt_top hg f.property⟩
      have heq : (f:E)+(1:ℝ) • (v:E) = g := by simp [v]
      apply (ENNReal.toReal_le_toReal (proximalFunctional_lt_top f.property).ne
        (proximalFunctional_lt_top hg).ne).mp
      have H := hQ.proximal_expansion u f v 1
      rw [heq, hf v] at H
      have hnonneg := hQ.realEnergy_quadratic.nonneg v
      nlinarith [sq_nonneg ‖(v:E)‖]
    · have hg' : Q g = ∞ := eq_top_iff.mpr (not_lt.mp hg)
      simp [proximalFunctional, hg']

variable [CompleteSpace E]

def ClosedQuadraticEnergy.resolvent (u : E) : E :=
  Classical.choose (hQ.exists_minimizer u)

lemma ClosedQuadraticEnergy.resolvent_minimizes (u : E) :
    ∀ g, proximalFunctional Q u (hQ.resolvent u) ≤ proximalFunctional Q u g :=
  Classical.choose_spec (hQ.exists_minimizer u)

lemma ClosedQuadraticEnergy.resolvent_finite (u : E) : Q (hQ.resolvent u) < ∞ := by
  have H := hQ.resolvent_minimizes u 0
  have h0 : proximalFunctional Q u 0 < ∞ := proximalFunctional_lt_top (by simp [hQ.zero])
  exact (le_add_right le_rfl).trans_lt (H.trans_lt h0)

def ClosedQuadraticEnergy.resolventDomain (u : E) : hQ.domain :=
  ⟨hQ.resolvent u, hQ.resolvent_finite u⟩

lemma ClosedQuadraticEnergy.resolvent_euler (u : E) (v : hQ.domain) :
    2*hQ.form (hQ.resolventDomain u) v + ⟪hQ.resolvent u-u, (v:E)⟫_ℝ = 0 :=
  (hQ.minimizer_iff_euler u (hQ.resolventDomain u)).mp (hQ.resolvent_minimizes u) v

lemma ClosedQuadraticEnergy.resolvent_add (u w : E) :
    hQ.resolvent (u+w) = hQ.resolvent u + hQ.resolvent w := by
  apply hQ.minimizer_unique (hQ.resolvent_minimizes (u+w))
  apply (hQ.minimizer_iff_euler (u+w) (hQ.resolventDomain u+hQ.resolventDomain w)).mpr
  intro v
  have hu := hQ.resolvent_euler u v
  have hw := hQ.resolvent_euler w v
  simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
  change 2 * (hQ.form (hQ.resolventDomain u) v + hQ.form (hQ.resolventDomain w) v) +
    ⟪hQ.resolvent u + hQ.resolvent w - (u+w), (v:E)⟫_ℝ = 0
  have heq : hQ.resolvent u + hQ.resolvent w - (u+w) =
    (hQ.resolvent u-u)+(hQ.resolvent w-w) := by abel
  rw [heq, inner_add_left]
  linarith

lemma ClosedQuadraticEnergy.resolvent_smul (a : ℝ) (u : E) :
    hQ.resolvent (a • u) = a • hQ.resolvent u := by
  apply hQ.minimizer_unique (hQ.resolvent_minimizes (a • u))
  apply (hQ.minimizer_iff_euler (a • u) (a • hQ.resolventDomain u)).mpr
  intro v
  have hu := hQ.resolvent_euler u v
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_smul]
  change 2 * (a * hQ.form (hQ.resolventDomain u) v) +
    ⟪a • hQ.resolvent u-a • u,(v:E)⟫_ℝ = 0
  rw [← smul_sub, real_inner_smul_left]
  calc
    _ = a * (2 * hQ.form (hQ.resolventDomain u) v + ⟪hQ.resolvent u-u,(v:E)⟫_ℝ) := by ring
    _ = 0 := by rw [hu, mul_zero]

lemma ClosedQuadraticEnergy.resolvent_zero : hQ.resolvent 0 = 0 := by
  simpa only [zero_smul] using hQ.resolvent_smul 0 (0:E)

lemma ClosedQuadraticEnergy.resolvent_firm (u w : E) :
    ‖hQ.resolvent u-hQ.resolvent w‖^2 ≤
      ⟪u-w,hQ.resolvent u-hQ.resolvent w⟫_ℝ := by
  let v := hQ.resolventDomain u-hQ.resolventDomain w
  have hu := hQ.resolvent_euler u v
  have hw := hQ.resolvent_euler w v
  have hform : hQ.form (hQ.resolventDomain u) v - hQ.form (hQ.resolventDomain w) v =
      hQ.realEnergy v := by rw [← LinearMap.sub_apply, ← map_sub, hQ.form_self]
  have hinner : ⟪hQ.resolvent u-u,(v:E)⟫_ℝ - ⟪hQ.resolvent w-w,(v:E)⟫_ℝ =
      ‖hQ.resolvent u-hQ.resolvent w‖^2 - ⟪u-w,hQ.resolvent u-hQ.resolvent w⟫_ℝ := by
    rw [← inner_sub_left]
    have heq : hQ.resolvent u-u-(hQ.resolvent w-w) =
      (hQ.resolvent u-hQ.resolvent w)-(u-w) := by abel
    rw [heq, inner_sub_left]
    change ⟪hQ.resolvent u-hQ.resolvent w,hQ.resolvent u-hQ.resolvent w⟫_ℝ - _ = _
    rw [real_inner_self_eq_norm_sq]
    rfl
  have hnonneg := hQ.realEnergy_quadratic.nonneg v
  linarith

lemma ClosedQuadraticEnergy.resolvent_nonexpansive (u w : E) :
    ‖hQ.resolvent u-hQ.resolvent w‖ ≤ ‖u-w‖ := by
  have hf := hQ.resolvent_firm u w
  have hc := real_inner_le_norm (u-w) (hQ.resolvent u-hQ.resolvent w)
  nlinarith [norm_nonneg (hQ.resolvent u-hQ.resolvent w), norm_nonneg (u-w)]

def ClosedQuadraticEnergy.resolventLinear : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := hQ.resolvent
      map_add' := hQ.resolvent_add
      map_smul' := hQ.resolvent_smul } 1
    (fun u => by
      change ‖hQ.resolvent u‖ ≤ 1 * ‖u‖
      simpa only [hQ.resolvent_zero, sub_zero, one_mul] using hQ.resolvent_nonexpansive u 0)

lemma ClosedQuadraticEnergy.resolvent_symmetric (u w : E) :
    ⟪hQ.resolvent u,w⟫_ℝ = ⟪u,hQ.resolvent w⟫_ℝ := by
  have hu := hQ.resolvent_euler u (hQ.resolventDomain w)
  have hw := hQ.resolvent_euler w (hQ.resolventDomain u)
  rw [hQ.form_comm] at hu
  change 2 * _ + ⟪hQ.resolvent u-u,hQ.resolvent w⟫_ℝ = 0 at hu
  change 2 * _ + ⟪hQ.resolvent w-w,hQ.resolvent u⟫_ℝ = 0 at hw
  rw [inner_sub_left] at hu hw
  rw [real_inner_comm (hQ.resolvent u) (hQ.resolvent w),
    real_inner_comm (hQ.resolvent u) w] at hw
  linarith

end WeakHessianFunctional

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_FormGenerator
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

namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.resolvent_injective
    (hd : hQ.domain.topologicalClosure = ⊤) : Function.Injective hQ.resolvent := by
  intro u w huw
  have hv : u-w ∈ hQ.domainᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hu := hQ.resolvent_euler u ⟨v,hv⟩
    have hw := hQ.resolvent_euler w ⟨v,hv⟩
    have he : hQ.resolventDomain u = hQ.resolventDomain w := Subtype.ext huw
    rw [he] at hu
    rw [huw] at hu
    rw [inner_sub_left] at hu hw
    rw [inner_sub_right, real_inner_comm u v, real_inner_comm w v]
    linarith
  rw [Submodule.topologicalClosure_eq_top_iff.mp hd] at hv
  exact sub_eq_zero.mp hv

lemma ClosedQuadraticEnergy.resolvent_range_dense
    (hd : hQ.domain.topologicalClosure = ⊤) :
    hQ.resolventLinear.toLinearMap.range.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply hQ.resolvent_injective hd
  rw [hQ.resolvent_zero]
  have hz : ∀ w, ⟪hQ.resolvent u,w⟫_ℝ = 0 := by
    intro w
    rw [hQ.resolvent_symmetric, real_inner_comm (hQ.resolvent w) u]
    exact (Submodule.mem_orthogonal _ _).mp hu (hQ.resolvent w) ⟨w,rfl⟩
  exact inner_self_eq_zero.mp (hz (hQ.resolvent u))

lemma ClosedQuadraticEnergy.resolvent_positive : hQ.resolventLinear.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨hQ.resolvent_symmetric, ?_⟩
  intro u
  have H := hQ.resolvent_firm u 0
  rw [hQ.resolvent_zero, sub_zero, sub_zero, real_inner_comm] at H
  exact (sq_nonneg _).trans H

lemma ClosedQuadraticEnergy.resolvent_le_one :
    (1 - hQ.resolventLinear).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  constructor
  · intro u w
    change ⟪u-hQ.resolvent u,w⟫_ℝ = ⟪u,w-hQ.resolvent w⟫_ℝ
    rw [inner_sub_left, inner_sub_right, hQ.resolvent_symmetric]
  · intro u
    change 0 ≤ ⟪u-hQ.resolvent u,u⟫_ℝ
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
    have H := hQ.resolvent_nonexpansive u 0
    rw [hQ.resolvent_zero, sub_zero, sub_zero] at H
    have hc := real_inner_le_norm (hQ.resolvent u) u
    nlinarith [norm_nonneg u]

def ClosedQuadraticEnergy.IsFormGenerator (u A : E) : Prop :=
  ∃ hu : Q u < ∞, ∀ v : hQ.domain,
    2*hQ.form ⟨u,hu⟩ v = -⟪A,(v:E)⟫_ℝ

lemma ClosedQuadraticEnergy.isFormGenerator_resolvent (u : E) :
    hQ.IsFormGenerator (hQ.resolvent u) (hQ.resolvent u-u) := by
  refine ⟨hQ.resolvent_finite u, ?_⟩
  intro v
  have h := hQ.resolvent_euler u v
  change 2*hQ.form (hQ.resolventDomain u) v = _
  linarith

lemma ClosedQuadraticEnergy.isFormGenerator_iff (u A : E) :
    hQ.IsFormGenerator u A ↔ hQ.resolvent (u-A) = u := by
  constructor
  · rintro ⟨hu, hgen⟩
    apply hQ.minimizer_unique (hQ.resolvent_minimizes (u-A))
    apply (hQ.minimizer_iff_euler (u-A) ⟨u,hu⟩).mpr
    intro v
    rw [hgen v]
    change -⟪A,(v:E)⟫_ℝ + ⟪u-(u-A),(v:E)⟫_ℝ = 0
    simp only [sub_sub_cancel]
    ring
  · intro h
    have H := hQ.isFormGenerator_resolvent (u-A)
    rw [h, sub_sub_cancel] at H
    exact H

lemma ClosedQuadraticEnergy.formGenerator_smul {u A : E} (c : ℝ)
    (hu : hQ.IsFormGenerator u A) : hQ.IsFormGenerator (c • u) (c • A) := by
  rw [hQ.isFormGenerator_iff, ← smul_sub, hQ.resolvent_smul,
    (hQ.isFormGenerator_iff _ _).mp hu]

end WeakHessianFunctional

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

section QuadraticScaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)
variable [CompleteSpace E]
include hQ

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.scale {t : ℝ} (ht : 0 < t) :
    ClosedQuadraticEnergy (fun u => ENNReal.ofReal t*Q u) where
  lowerSemicontinuous := (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
    hQ.lowerSemicontinuous (fun _ _ h => mul_le_mul_right h _)
  zero := by rw [hQ.zero, mul_zero]
  smul := by intro c u; rw [hQ.smul]; ac_rfl
  parallelogram := by
    intro u v hu hv
    rw [← mul_add, hQ.parallelogram u v ((ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mp hu)
      ((ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mp hv), mul_add]
    congr 1 <;> ac_rfl

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.scale_form {t : ℝ} (ht : 0 < t) (u v : E)
    (hu : Q u < ∞) (hv : Q v < ∞) :
    (hQ.scale ht).form ⟨u,(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mpr hu⟩
      ⟨v,(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mpr hv⟩ =
      t*hQ.form ⟨u,hu⟩ ⟨v,hv⟩ := by
  rw [ClosedQuadraticEnergy.form_apply, ClosedQuadraticEnergy.form_apply]
  simp only [energyPolar, ClosedQuadraticEnergy.realEnergy, Submodule.coe_add,
    Submodule.coe_sub, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le]
  ring

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.scale_isFormGenerator_iff {t : ℝ} (ht : 0 < t) (u A : E) :
    (hQ.scale ht).IsFormGenerator u (t • A) ↔ hQ.IsFormGenerator u A := by
  constructor
  · rintro ⟨hu,hgen⟩
    have hu' := (ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mp hu
    refine ⟨hu', ?_⟩
    intro v
    have H := hgen ⟨(v:E),(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mpr v.property⟩
    rw [hQ.scale_form ht u v hu' v.property, real_inner_smul_left] at H
    change 2*hQ.form ⟨u,hu'⟩ v = -⟪A,(v:E)⟫_ℝ
    nlinarith
  · rintro ⟨hu,hgen⟩
    refine ⟨(ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht u).mpr hu, ?_⟩
    intro v
    have hv := (ClosedQuadraticEnergy.scale_lt_top_iff (Q := Q) ht v).mp v.property
    have H := hgen ⟨(v:E),hv⟩
    rw [hQ.scale_form ht u v hu hv, real_inner_smul_left]
    nlinarith

lemma ClosedQuadraticEnergy.scaled_resolvent_iff {t : ℝ} (ht : 0 < t) (u v : E) :
    (hQ.scale ht).resolvent u = v ↔ hQ.IsFormGenerator v (t⁻¹ • (v-u)) := by
  rw [← hQ.scale_isFormGenerator_iff ht]
  simp only [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  rw [(hQ.scale ht).isFormGenerator_iff, sub_sub_cancel]

end QuadraticScaling

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

end WeakHessianFunctional

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_ScaledResolventCfc
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
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.resolvent_normal_fixed
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    (hηQ : ∀ f : Lp ℝ 2 m, Q (hη.compLp hη0 f) ≤ Q f) (u : Lp ℝ 2 m)
    (hu : hη.compLp hη0 u = u) : hη.compLp hη0 (hQ.resolvent u) = hQ.resolvent u := by
  let f := hQ.resolvent u
  let g := hη.compLp hη0 f
  have hn : ‖g-u‖ ≤ ‖f-u‖ := by
    simpa only [hu, NNReal.coe_one, one_mul] using hη.norm_compLp_sub_le hη0 f u
  have hj : proximalFunctional Q u g ≤ proximalFunctional Q u f := by
    apply add_le_add (hηQ f)
    apply ENNReal.ofReal_le_ofReal
    nlinarith [norm_nonneg (g-u), norm_nonneg (f-u)]
  exact hQ.minimizer_unique (fun v => hj.trans (hQ.resolvent_minimizes u v))
    (hQ.resolvent_minimizes u)

end WeakHessianFunctional

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

variable [MeasurableSpace X] {m : Measure X}
lemma slope_energy_const_mul (c : ℝ) (f : X → ℝ) :
    (2:ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope (fun y => c * f y) x ^ 2 ∂m) =
      ENNReal.ofReal (c^2) * ((2:ℝ≥0∞)⁻¹ * (∫⁻ x, localSlope f x ^ 2 ∂m)) := by
  simp_rw [localSlope_const_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  have hc : (ENNReal.ofReal |c|)^2 = ENNReal.ofReal (c^2) := by
    rw [← ENNReal.ofReal_pow (abs_nonneg c), sq_abs]
  rw [hc]
  ac_rfl

end WeakHessian

open Set
open scoped NNReal


end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ExpNegQuadraticBound
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

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional

lemma heatSymbol_second_error {t s : ℝ} (ht : 0 ≤ t) (hs : s ∈ Icc (0:ℝ) 1) :
    |(heatSymbol t s-1)*s^2-t*(s^2-s)| ≤ t^2/2 := by
  rcases hs.1.eq_or_lt with hsz | hsz
  · simp only [← hsz, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, sub_self, abs_zero]
    positivity
  let r := t/s-t
  have hr : 0 ≤ r := by
    dsimp [r]
    have h : t ≤ t/s := (le_div_iff₀ hsz).mpr (by nlinarith [hs.2])
    linarith
  have he : heatSymbol t s = Real.exp (-r) := by
    rw [heatSymbol_of_pos ht hsz]
    congr 1
    dsimp [r]
    ring
  have hrs : r*s = t*(1-s) := by
    dsimp [r]
    field_simp
  have hlow := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-r)) (sq_nonneg s)
  have hupp := mul_le_mul_of_nonneg_right (exp_neg_quadratic_bound hr) (sq_nonneg s)
  have her : (heatSymbol t s-1)*s^2-t*(s^2-s) =
      (Real.exp (-r)-1+r)*s^2 := by
    rw [he]
    nlinarith [congrArg (fun x : ℝ => x*s) hrs]
  rw [her, abs_of_nonneg (by nlinarith : 0 ≤ (Real.exp (-r)-1+r)*s^2)]
  have hs1 : (1-s)^2 ≤ 1 := by nlinarith [hs.1,hs.2]
  have hsq := congrArg (fun x : ℝ => x^2) hrs
  have hmul := mul_le_mul_of_nonneg_left hs1 (sq_nonneg t)
  nlinarith

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatInverseSymbol
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

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolventHeat_second_error {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) :
    ‖(resolventHeat R t-1)*R^2-t • (R^2-R)‖ ≤ t^2/2 := by
  have hb : ‖cfc (fun s => (heatSymbol t s-1)*s^2-t*(s^2-s)) R‖ ≤ t^2/2 := by
    apply norm_cfc_le (by positivity)
    intro s hs
    exact heatSymbol_second_error ht (resolvent_spectrum_bounds hR hR1 hs)
  have hc1 : Continuous (fun s : ℝ => (heatSymbol t s-1)*s^2) :=
    ((heatSymbol_continuous t).sub continuous_const).mul (continuous_id.pow 2)
  have hc2 : Continuous (fun s : ℝ => s^2-s) := (continuous_id.pow 2).sub continuous_id
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  rw [cfc_sub _ _ R hc1.continuousOn (hc2.const_mul t).continuousOn,
    cfc_mul (fun s => heatSymbol t s-1) (fun s : ℝ => s^2) R
      ((heatSymbol_continuous t).sub continuous_const).continuousOn (continuous_id.pow 2).continuousOn,
    cfc_sub (heatSymbol t) (fun _ => 1) R (heatSymbol_continuous t).continuousOn continuous_const.continuousOn,
    cfc_const 1 R hR.isSelfAdjoint, map_one, cfc_pow_id R 2 hR.isSelfAdjoint,
    cfc_const_mul t (fun s : ℝ => s^2-s) R hc2.continuousOn,
    cfc_sub (fun s : ℝ => s^2) (fun s : ℝ => s) R (continuous_id.pow 2).continuousOn continuous_id.continuousOn,
    cfc_pow_id R 2 hR.isSelfAdjoint, hid] at hb
  exact hb

lemma resolventHeat_second_error_apply {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (v : H) :
    ‖resolventHeat R t (R (R v))-R (R v)-t • (R (R v)-R v)‖ ≤ (t^2/2)*‖v‖ := by
  calc
    _ = ‖(((resolventHeat R t-1)*R^2-t • (R^2-R) : H →L[ℂ] H)) v‖ := rfl
    _ ≤ ‖(resolventHeat R t-1)*R^2-t • (R^2-R)‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (resolventHeat_second_error hR hR1 ht) (norm_nonneg v)

lemma resolventHeat_slope_range2_error {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (v : H) :
    ‖t⁻¹ • (resolventHeat R t (R (R v))-R (R v))-(R (R v)-R v)‖ ≤ (t/2)*‖v‖ := by
  have he : t⁻¹ • (resolventHeat R t (R (R v))-R (R v))-(R (R v)-R v) =
      t⁻¹ • (resolventHeat R t (R (R v))-R (R v)-t • (R (R v)-R v)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    _ ≤ t⁻¹*((t^2/2)*‖v‖) := mul_le_mul_of_nonneg_left
      (resolventHeat_second_error_apply hR hR1 ht.le v) (inv_nonneg.mpr ht.le)
    _ = (t/2)*‖v‖ := by field_simp

lemma resolventHeat_slope_range_contractive {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (u v : H) :
    dist (t⁻¹ • (resolventHeat R t (R u)-R u))
      (t⁻¹ • (resolventHeat R t (R v)-R v)) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm]
  have he : t⁻¹ • (resolventHeat R t (R u)-R u) -
      t⁻¹ • (resolventHeat R t (R v)-R v) =
      t⁻¹ • (resolventHeat R t (R (u-v))-R (u-v)) := by
    simp only [map_sub, smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    _ ≤ t⁻¹*(t*‖u-v‖) := mul_le_mul_of_nonneg_left
      (resolventHeat_range_error_apply hR hR1 ht.le (u-v)) (inv_nonneg.mpr ht.le)
    _ = ‖u-v‖ := by rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]

lemma resolventHeat_slope_range_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hd : R.toLinearMap.range.topologicalClosure = ⊤) (v : H) :
    Tendsto (fun t : ℝ => t⁻¹ • (resolventHeat R t (R v)-R v))
      (𝓝[>] (0:ℝ)) (𝓝 (R v-v)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd' := Submodule.dense_iff_topologicalClosure_eq_top.mpr hd
  obtain ⟨u, hu, huR⟩ := Metric.dense_iff.mp hd' v (ε/8) (by positivity)
  obtain ⟨w,rfl⟩ := huR
  have hv : dist v (R w) < ε/8 := by simpa [dist_comm] using hu
  have htend : Tendsto (fun t : ℝ => (t/2)*‖w‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using ((((continuous_id.div_const 2).mul_const ‖w‖).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds : Tendsto (fun t : ℝ => (t/2)*‖w‖) (𝓝[>] (0:ℝ)) (𝓝 ((0/2)*‖w‖)))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), (t/2)*‖w‖ < ε/2 :=
    (tendsto_order.1 htend).2 _ (by positivity)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
  have hcon := resolventHeat_slope_range_contractive hR hR1 ht0 v (R w)
  have hn := resolventHeat_slope_range2_error hR hR1 ht0 w
  have hlim := resolvent_minus_id_bound hR hR1 (R w) v
  rw [dist_comm (R w) v] at hlim
  have htri := dist_triangle (t⁻¹ • (resolventHeat R t (R v)-R v))
    (t⁻¹ • (resolventHeat R t (R (R w))-R (R w))) (R v-v)
  have htri2 := dist_triangle (t⁻¹ • (resolventHeat R t (R (R w))-R (R w)))
    (R (R w)-R w) (R v-v)
  rw [dist_eq_norm (t⁻¹ • (resolventHeat R t (R (R w))-R (R w))) (R (R w)-R w)] at htri2
  linarith

lemma resolventHeat_deriv_range_zero {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hd : R.toLinearMap.range.topologicalClosure = ⊤) (v : H) :
    HasDerivWithinAt (fun t : ℝ => resolventHeat R t (R v))
      (R v-v) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici (0:ℝ) \ {0} = Ioi 0 := by ext t; simp
  rw [hset]
  change Tendsto (fun t => slope (fun s : ℝ => resolventHeat R s (R v)) 0 t)
    (𝓝[>] (0:ℝ)) (𝓝 (R v-v))
  simpa only [slope_def_module, sub_zero, resolventHeat_zero hR, one_apply_eq_self]
    using resolventHeat_slope_range_zero hR hR1 hd v

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_ActionDistPrimitiveValues
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

lemma action_dist_primitive_values {a : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    {s t u v : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) (hqt : ENNReal.ofReal |v - u| ≤ ∫⁻ r in Icc s t, a r) :
    dist u v ≤ dist (∫ r in (0 : ℝ)..s, (a r).toReal)
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
    dist u v = |v - u| := by rw [dist_comm, Real.dist_eq]
    _ ≤ (∫⁻ r in Icc s t, a r).toReal := by
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using ENNReal.toReal_mono hstfin hqt
    _ = (∫ r in (0 : ℝ)..t, (a r).toReal) - ∫ r in (0 : ℝ)..s, (a r).toReal :=
      hreal.trans (intervalIntegral.integral_interval_sub_left hi_t hi_s).symm
    _ ≤ _ := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _

lemma eq_of_dense_action_bounds {q : ℝ → ℝ} {a : ℝ → ℝ≥0∞}
    (hq : AbsolutelyContinuousOnInterval q 0 1)
    (ha : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)))
    (hfin : (∫⁻ t in Icc (0 : ℝ) 1, a t) < ∞)
    (d : ℕ → Icc (0 : ℝ) 1) (hd : DenseRange d)
    {t b : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hbound : ∀ i, ENNReal.ofReal |b - q (d i)| ≤ ∫⁻ r in uIcc (d i : ℝ) t, a r) :
    q t = b := by
  let A : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, (a r).toReal
  have hA : AbsolutelyContinuousOnInterval A 0 1 :=
    (action_intervalIntegrable ha hfin).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hcA : Continuous (fun s : Icc (0 : ℝ) 1 => A s) := by
    apply hA.continuousOn.comp_continuous continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hcq : Continuous (fun s : Icc (0 : ℝ) 1 => q s) := by
    apply hq.continuousOn.comp_continuous continuous_subtype_val
    intro s
    simpa only [uIcc_of_le zero_le_one] using s.property
  have hi : ∀ i, dist (q (d i)) b ≤ dist (A (d i)) (A t) := by
    intro i
    rcases le_total (d i : ℝ) t with h|h
    · exact action_dist_primitive_values ha hfin (d i).property ht h
        (by simpa only [uIcc_of_le h] using hbound i)
    · simpa only [dist_comm] using
        action_dist_primitive_values ha hfin ht (d i).property h
          (by simpa only [uIcc_of_ge h, abs_sub_comm] using hbound i)
  have hall := hd.induction_on (p := fun s : Icc (0 : ℝ) 1 =>
      dist (q s) b ≤ dist (A s) (A t)) (⟨t,ht⟩ : Icc (0 : ℝ) 1)
    (isClosed_le (hcq.dist continuous_const) (hcA.dist continuous_const)) hi
  exact dist_le_zero.mp (by simpa only [dist_self] using hall)

end WeakHessianCalculus

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_MeasurableVariableIntervalAction
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
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma measurable_variable_interval_action {a : Curve X × ℝ → ℝ≥0∞} (ha : Measurable a) (s : ℝ) :
    Measurable (fun p : Curve X × ℝ => ∫⁻ r in uIcc s p.2, a (p.1,r)) := by
  let H : (Curve X × ℝ) × ℝ → ℝ≥0∞ := fun p =>
    if p.2 ∈ uIcc s p.1.2 then a (p.1.1,p.2) else 0
  have hset : MeasurableSet {p : (Curve X × ℝ) × ℝ | p.2 ∈ uIcc s p.1.2} := by
    apply MeasurableSet.inter
    · exact measurableSet_le (measurable_const.min measurable_fst.snd) measurable_snd
    · exact measurableSet_le measurable_snd (measurable_const.max measurable_fst.snd)
  have hH : Measurable H := Measurable.ite hset
    (ha.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have hEq : (fun p : Curve X × ℝ => ∫⁻ r, H (p,r)) =
      (fun p : Curve X × ℝ => ∫⁻ r in uIcc s p.2, a (p.1,r)) := by
    funext p
    exact lintegral_indicator (s := uIcc s p.2) measurableSet_uIcc (fun r => a (p.1,r))
  rw [← hEq]
  exact hH.lintegral_prod_right

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_MulBounded
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
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma LocallyL2.mul_bounded {f g : X → ℝ} (hf : LocallyL2 m f)
    (hg : AEStronglyMeasurable g m) {B : ℝ} (hb : ∀ᵐ x ∂m, |g x| ≤ B) :
    LocallyL2 m (fun x => f x * g x) := by
  intro o R hR
  apply ((hf o R hR).const_mul B).mono ((hf.aestronglyMeasurable.mul hg).restrict)
  filter_upwards [ae_restrict_of_ae hb] with x hx
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  calc
    |f x| * |g x| ≤ |f x| * |B| :=
      mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)
    _ = |B| * |f x| := mul_comm _ _

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_AeProdMetricSpeed
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

omit [BorelSpace X] in

lemma IsTestPlan.ae_prod_metricSpeed_lt_top {π : Measure (Curve X)} (hπ : IsTestPlan m π) :
    ∀ᵐ z ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1)), metricSpeed z.1 z.2 < ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  have hfin : (∫⁻ z : Curve X × ℝ, metricSpeed z.1 z.2 ^ 2
      ∂π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) < ∞ := by
    rw [lintegral_prod _ (measurable_metricSpeed.pow_const 2).aemeasurable]
    exact hπ.2.2.2
  filter_upwards [ae_lt_top (measurable_metricSpeed.pow_const 2) hfin.ne] with z hz
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hz

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_AddConst
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
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

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma IsLocalWeakUpperGradient.add_const {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (c : ℝ) :
    IsLocalWeakUpperGradient m (fun x => f x+c) D := by
  refine ⟨hD.1,hD.2.1,fun π hπ hb => ?_⟩
  simpa only [add_sub_add_right_eq_sub] using hD.2.2 π hπ hb

omit [BorelSpace X] in
lemma IsMinimalLocalWeakUpperGradient.add_const {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) (c : ℝ) :
    IsMinimalLocalWeakUpperGradient m (fun x => f x+c) D := by
  refine ⟨hD.1.add_const c,fun E hE => hD.2 E ?_⟩
  simpa only [add_neg_cancel_right] using hE.add_const (-c)

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_AeIntegralPositiveLipschitz
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma ae_eq_zero_of_integral_positive_lipschitz_sq {H : X → ℝ}
    (hH : Integrable H m)
    (hzero : ∀ (η : X → ℝ) (L : ℝ≥0), LipschitzWith L η →
      (∀ x, 1 ≤ η x) → ∀ A : ℝ, 0 ≤ A → (∀ x, |η x| ≤ A) →
      (∫ x, H x * (η x)^2 ∂m) = 0) : H =ᵐ[m] 0 := by
  apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact hH.locallyIntegrable
  intro φ hφc ⟨L,hφL⟩
  obtain ⟨M,hM⟩ := hφc.exists_bound_of_continuous hφL.continuous
  let C := |M|+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hφ (x : X) : |φ x| ≤ |M| := by
    have hx : |φ x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x
    exact hx.trans (le_abs_self M)
  have hp : LipschitzWith L (fun x => C+φ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_left] using hφL.dist_le_mul x y
  have hm : LipschitzWith L (fun x => C-φ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_left] using hφL.dist_le_mul x y
  have hp1 (x : X) : 1 ≤ C+φ x := by
    dsimp only [C]
    linarith [(abs_le.mp (hφ x)).1]
  have hm1 (x : X) : 1 ≤ C-φ x := by
    dsimp only [C]
    linarith [(abs_le.mp (hφ x)).2]
  have hpb (x : X) : |C+φ x| ≤ C+|M| := by
    rw [abs_of_nonneg (by linarith [hp1 x])]
    linarith [(abs_le.mp (hφ x)).2]
  have hmb (x : X) : |C-φ x| ≤ C+|M| := by
    rw [abs_of_nonneg (by linarith [hm1 x])]
    linarith [(abs_le.mp (hφ x)).1]
  have Ap : 0 ≤ C+|M| := by positivity
  have hzp := hzero _ L hp hp1 _ Ap hpb
  have hzm := hzero _ L hm hm1 _ Ap hmb
  have hip : Integrable (fun x => H x*(C+φ x)^2) m :=
    hH.mul_bdd (hp.continuous.pow 2).aestronglyMeasurable (c := (C+|M|)^2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Ap).mpr (hpb x))
  have him : Integrable (fun x => H x*(C-φ x)^2) m :=
    hH.mul_bdd (hm.continuous.pow 2).aestronglyMeasurable (c := (C+|M|)^2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) Ap).mpr (hmb x))
  have he : (∫ x, H x*(C+φ x)^2 ∂m) - (∫ x, H x*(C-φ x)^2 ∂m) =
      (4*C) * (∫ x, H x*φ x ∂m) := by
    rw [← integral_sub hip him, ← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hzp,hzm,sub_self] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (by norm_num) hC.ne')

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ExpMulLp
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

noncomputable def expMulLp {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  boundedMulLp (Real.continuous_exp.comp_aestronglyMeasurable hV)
    (hB.mono (fun x hx => by simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx))

lemma expMulLp_ae {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (u : Lp ℝ 2 m) :
    expMulLp hV hB u =ᵐ[m] (fun x => u x*Real.exp (V x)) := boundedMulLp_ae _ _ u

lemma expMulLp_inner {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (u v : Lp ℝ 2 m) :
    ⟪expMulLp hV hB u,expMulLp hV hB v⟫_ℝ = ∫ x, v x*u x*Real.exp (2*V x) ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [expMulLp_ae hV hB u,expMulLp_ae hV hB v] with x hx hy
  simp only [RCLike.inner_apply,conj_trivial,hx,hy,← sq_exp_eq]
  ring

lemma expMulLp_norm_sq {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (u : Lp ℝ 2 m) :
    ‖expMulLp hV hB u‖^2 = ∫ x, (u x)^2*Real.exp (2*V x) ∂m := by
  rw [← real_inner_self_eq_norm_sq,expMulLp_inner]
  simp only [pow_two]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_MinNatTendsto
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma expMulLp_norm_le_weighted {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    (u : Lp ℝ 2 m) (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (n : ℕ) :
    ‖expMulLp ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [expMulLp_ae ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u,hU.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (min_le_left _ _)) (abs_nonneg _)

lemma memLp_mul_exp_of_trunc {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    (u : Lp ℝ 2 m) {B : ℝ}
    (hB : ∀ n : ℕ, ‖expMulLp ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
      (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u‖^2 ≤ B) :
    MemLp (fun x => u x*Real.exp (V x)) 2 m ∧
      (∫ x, (u x*Real.exp (V x))^2 ∂m) ≤ B := by
  let fs : ℕ → X → ℝ := fun n x => u x*Real.exp (min (V x) (n:ℝ))
  have hfs (n : ℕ) : MemLp (fs n) 2 m := by
    exact MemLp.ae_eq (expMulLp_ae _ _ _) (Lp.memLp (expMulLp ((hV.aemeasurable.min aemeasurable_const).aestronglyMeasurable)
      (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) u))
  apply integral_sq_fatou ((Lp.aestronglyMeasurable u).mul
    (Real.continuous_exp.comp_aestronglyMeasurable hV)) hfs
  · exact ae_of_all _ fun x => tendsto_const_nhds.mul
      ((Real.continuous_exp.tendsto _).comp (min_nat_tendsto (V x)))
  · intro n
    have H := hB n
    rw [expMulLp_norm_sq] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp only [fs,mul_pow,sq_exp_eq]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_RadialCutoffLp
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_cutoff_le_weighted {V f η : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hη : AEStronglyMeasurable η m) (hη1 : ∀ᵐ x ∂m, |η x| ≤ 1) :
    ‖∫ x, f x*η x ∂m‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*‖hV.toLp (fun x => Real.exp (-V x))‖ := by
  have hW : MemLp (fun x => Real.exp (-V x)*η x) 2 m := memLp_mul_bounded hV hη hη1
  let U := hf.toLp (fun x => f x*Real.exp (V x))
  let W := hW.toLp (fun x => Real.exp (-V x)*η x)
  let D := hV.toLp (fun x => Real.exp (-V x))
  have he : (∫ x, f x*η x ∂m) = ⟪U,W⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hW.coeFn_toLp] with x hu hw
    dsimp only [U,W]
    rw [hu,hw]
    simp only [RCLike.inner_apply,conj_trivial]
    calc f x*η x = f x*(Real.exp (V x)*Real.exp (-V x))*η x := by
           rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
         _ = _ := by ring
  have hnorm : ‖W‖ ≤ ‖D‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hW.coeFn_toLp,hV.coeFn_toLp,hη1] with x hx hy hηx
    dsimp only [W,D]
    rw [hx,hy]
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hηx
  rw [he]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_radialCutoff_tendsto (o : X) {f : X → ℝ} (hf : Integrable f m) :
    Tendsto (fun n => ∫ x, f x*radialCutoff o n x ∂m) atTop (𝓝 (∫ x,f x ∂m)) := by
  have H := tendsto_integral_of_dominated_convergence (fun x => |f x|)
    (fun n => hf.aestronglyMeasurable.mul (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
    (by simpa only [Real.norm_eq_abs] using hf.norm)
    (fun n => ae_of_all _ fun x => by
      change |f x*radialCutoff o n x| ≤ |f x|
      rw [abs_mul,abs_of_nonneg (radialCutoff_nonneg o n x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_le_one o n x))
    (ae_of_all _ fun x => tendsto_const_nhds.mul (radialCutoff_tendsto o x))
  simpa only [Pi.mul_apply,mul_one] using H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_FormGeneratorSymmetric
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
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

namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.scaled_resolvent_generator_error {u A : E}
    (hu : hQ.IsFormGenerator u A) {t : ℝ} (ht : 0 < t) :
    ‖(hQ.scale ht).resolvent u-u‖ ≤ t*‖A‖ := by
  have H : (hQ.scale ht).resolvent (u-t • A) = u := by
    rw [hQ.scaled_resolvent_iff ht, sub_sub_cancel, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    exact hu
  have he : (hQ.scale ht).resolvent u-u = t • (hQ.scale ht).resolvent A := by
    change (hQ.scale ht).resolventLinear (u-t • A) = u at H
    rw [map_sub, map_smul] at H
    change (hQ.scale ht).resolvent u - t • (hQ.scale ht).resolvent A = u at H
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp H).trans (add_comm _ _))
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  apply mul_le_mul_of_nonneg_left _ ht.le
  have H := (hQ.scale ht).resolvent_nonexpansive A 0
  simpa only [(hQ.scale ht).resolvent_zero, sub_zero] using H

lemma ClosedQuadraticEnergy.scaled_resolvent_tendsto
    (hd : hQ.domain.topologicalClosure = ⊤) {ι : Type*} {l : Filter ι}
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (hlim : Tendsto t l (𝓝 0)) (u : E) :
    Tendsto (fun i => (hQ.scale (ht i)).resolvent u) l (𝓝 u) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd' := Submodule.dense_iff_topologicalClosure_eq_top.mpr (hQ.resolvent_range_dense hd)
  obtain ⟨w,hw,hwR⟩ := Metric.dense_iff.mp hd' u (ε/4) (by positivity)
  obtain ⟨v,rfl⟩ := hwR
  have hv : dist (hQ.resolvent v) u < ε/4 := hw
  have hbound : Tendsto (fun i => t i*‖hQ.resolvent v-v‖) l (𝓝 0) := by
    simpa using hlim.mul_const ‖hQ.resolvent v-v‖
  filter_upwards [hbound.eventually_lt_const (by positivity : (0:ℝ) < ε/2)] with i hi
  have he := hQ.scaled_resolvent_generator_error (hQ.isFormGenerator_resolvent v) (ht i)
  have hc := (hQ.scale (ht i)).resolvent_nonexpansive u (hQ.resolvent v)
  have H := dist_triangle ((hQ.scale (ht i)).resolvent u)
    ((hQ.scale (ht i)).resolvent (hQ.resolvent v)) u
  have H' := dist_triangle ((hQ.scale (ht i)).resolvent (hQ.resolvent v)) (hQ.resolvent v) u
  simp only [dist_eq_norm] at H H' hv ⊢
  rw [norm_sub_rev u (hQ.resolvent v)] at hc
  nlinarith

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_DecayCutoffLp
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma memLp_decayCutoff {V : X → ℝ} (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (o : X) (n : ℕ) : MemLp (fun x => Real.exp (-V x)*(1-radialCutoff o n x)) 2 m := by
  apply memLp_mul_bounded hV (B := 1) (aestronglyMeasurable_const.sub
    (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change |1-radialCutoff o n x| ≤ (1:ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr (radialCutoff_le_one o n x))]
    linarith [radialCutoff_nonneg o n x]

noncomputable def decayCutoffLp {V : X → ℝ} (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (o : X) (n : ℕ) : Lp ℝ 2 m :=
  (memLp_decayCutoff hV o n).toLp (fun x => Real.exp (-V x)*(1-radialCutoff o n x))

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma decayCutoffLp_norm_tendsto {V : X → ℝ} (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (o : X) : Tendsto (fun n => ‖decayCutoffLp hV o n‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ‖decayCutoffLp hV o n‖^2) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence (F := fun n x => (Real.exp (-V x)*(1-radialCutoff o n x))^2) (f := fun _ => (0:ℝ)) (fun x => (Real.exp (-V x))^2)
      (fun n => (memLp_decayCutoff hV o n).aestronglyMeasurable.pow 2) hV.integrable_sq
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),mul_pow]
        apply mul_le_of_le_one_right (sq_nonneg _)
        have h0 := radialCutoff_nonneg o n x
        have h1 := radialCutoff_le_one o n x
        nlinarith [sq_nonneg (radialCutoff o n x)])
      (ae_of_all _ fun x => by
        have H := ((tendsto_const_nhds (x := Real.exp (-V x))).mul ((tendsto_const_nhds (x := (1:ℝ))).sub (radialCutoff_tendsto o x))).pow 2
        simpa only [sub_self,mul_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using H)
    simpa only [decayCutoffLp,norm_toLp_sq_eq_integral,integral_zero] using H
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using H

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_cutoff_error_le_weighted {V f : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m) (o : X) (n : ℕ) :
    ‖(∫ x,f x ∂m)-(∫ x,f x*radialCutoff o n x ∂m)‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*‖decayCutoffLp hV o n‖ := by
  have hfi := integrable_of_memLp_mul_exp hf hV
  have hη : Integrable (fun x => f x*radialCutoff o n x) m :=
    hfi.mul_bdd (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        change |radialCutoff o n x| ≤ (1:ℝ)
        rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
        exact radialCutoff_le_one o n x)
  have he : (∫ x,f x ∂m)-(∫ x,f x*radialCutoff o n x ∂m) =
      ∫ x,f x*(1-radialCutoff o n x) ∂m := by
    rw [← integral_sub hfi hη]
    congr 1; funext x; simp only [mul_sub,mul_one]
  rw [he]
  exact integral_mul_le_weighted hf (memLp_decayCutoff hV o n)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Curvature_DecayWeight
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
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
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma CurvatureDimension.exists_decay_weight {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) : ∃ a : ℝ, 0 < a ∧ MemLp (fun x => Real.exp (-a*dist x o)) 2 m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  refine ⟨|C|+1, by positivity, ?_⟩
  apply memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg (by positivity)
    (show C < 2*(|C|+1) by linarith [le_abs_self C,abs_nonneg C])
  exact cd_ball_volume_bound hN hcd hfull hfin o

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile75
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma densityMeasure_probability_integral (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) : IsProbabilityMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one hm) hun,hm,ENNReal.ofReal_one]

def integrableDensityProbability (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) : ProbabilityMeasure X :=
  ⟨densityMeasure m u,densityMeasure_probability_integral u hun hm⟩

end WeakHessian

end
end InlinedFile75

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_AveragedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

 def timeAverageLaw (π : Measure (Curve X)) (ν : Measure ℝ) (s : ℝ) : Measure X :=
  (ν.prod π).map (fun z : ℝ × Curve X => evalReal z.2 (s-z.1))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyCell
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
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

variable {m : Measure X} {K N : ℝ}

namespace EntropyCell

def uniformCap (c : EntropyCell m K N) : ℝ≥0∞ :=
  c.cap*ENNReal.ofReal (Real.exp (2*compressionRate K N*c.length))

end EntropyCell

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_SmoothDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

 def smoothDensity (κ : ℝ → ℝ) (u : Time → Lp ℝ 2 m) : ℝ → Lp ℝ 2 m :=
  convolution κ (fun t => u (clampTime t)) (ContinuousLinearMap.lsmul ℝ ℝ)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RadialRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile28
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X] in
lemma radial_mul_memLp {f : X → ℝ} (hf : MemLp f 2 m) (o : X) (n : ℕ) :
    MemLp (fun x => f x*radialCutoff o n x) 2 m :=
  memLp_mul_bounded hf (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)

end WeakHessian

end
end InlinedFile28

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_WeightedHeatPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile42
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma radial_tail_memLp {f : X → ℝ} (hf : MemLp f 2 m) (o : X) (n : ℕ) :
    MemLp (fun x => f x*(1-radialCutoff o n x)) 2 m := by
  convert hf.sub (radial_mul_memLp hf o n) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Pi.sub_apply]
  ring

end WeakHessian

end
end InlinedFile42

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CoreAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile110
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma laplacian_isLaplacian {f : X → ℝ} (hf : InLaplacianDomain m f) :
    IsLaplacian m f (laplacian m f) := by
  change ∃ L, IsLaplacian m f L at hf
  unfold laplacian
  simpa only [dite_eq_left hf] using Classical.choose_spec hf

end WeakHessian

end
end InlinedFile110

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GraphReuse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile173
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def OriginalTestGraphCore (m : Measure X) : Prop :=
  ∀ (u A : X → ℝ) (hu : IsLaplacian m u A),
    ∃ (gs : ℕ → X → ℝ) (htest : ∀ n, IsTestFunction m (gs n)),
      (∀ n, HasCompactSupport (gs n)) ∧
      Tendsto (fun n => (laplacian_isLaplacian (htest n).1).1.1.toLp (gs n)) atTop
        (𝓝 (hu.1.1.toLp u)) ∧
      Tendsto (fun n => (laplacian_isLaplacian (htest n).1).2.1.toLp (laplacian m (gs n)))
        atTop (𝓝 (hu.2.1.toLp A))

end WeakHessian

end
end InlinedFile173

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SquareTimePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile133
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma clipSquare_lipschitz (n : ℕ) :
    LipschitzWith (2*n) (fun r : ℝ => (realClip n r)^2) := by
  have H := lipschitz_mul_bounded (realClip_lipschitz n) (realClip_lipschitz n)
    (realClip_abs_le n) (realClip_abs_le n)
  convert! H using 1
  · ext; simp; ring
  · funext r; ring

def clipSquareLp (n : ℕ) (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (clipSquare_lipschitz n).compLp (by simp [realClip_zero]) u

end WeakHessian

end
end InlinedFile133

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PlanIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

 def planMoment (π : Measure (Curve X)) (f : X → ℝ) (t : Time) : ℝ := ∫ γ, f (γ t) ∂π
 def planGradientEnergy (m : Measure X) (π : Measure (Curve X)) (f : X → ℝ) (t : Time) : ℝ :=
  ∫ γ, (weakGradient m f (γ t))^2 ∂π
 def planKineticCost (π : Measure (Curve X)) : ℝ := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π

end WeakHessian

end
end

end OAI
end


