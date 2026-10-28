-- Prove2me | Definitions.Def_OAIQ52Wh005
-- name    : OAIQ52Wh005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:46:36.040635+00:00
-- url     : https://prove2.me/theorems/8fa8710c-87e9-436d-bae8-31b46847e8a9
-- title:
--   Definitions bundle OAIQ52Wh005 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 163 declarations of OpenAI's Lean: 6 definitions and 157 theorems. The definitions and types are `OAI.WeakHessian.cheegerHeat`, `OAI.WeakHessianFunctional.complexify`, `OAI.WeakHessianFunctional.complexifyReal`, `OAI.WeakHessianFunctional.realCfc`, `OAI.WeakHessianFunctional.realHeat`, `OAI.WeakHessianFunctional.realOperators`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_NormLpSqIntegral`, `WeakHessian_Calculus_NormSqLintegralEnorm`, `WeakHessian_Entropy_GradientParallelogramDefect`, `WeakHessian_Entropy_LocalGradientParallelogram`, `WeakHessian_Entropy_LocalGradientParallelogramCheeger`, `WeakHessian_Entropy_WeightedParallelogramIntegral`, `WeakHessian_HeatFlow_CheegerHeat`, `WeakHessian_HeatFlow_CheegerHeatContinuous`, `WeakHessian_HeatFlow_CheegerHeatDavies`, `WeakHessian_HeatFlow_HeatGeneratorOperator`, `WeakHessian_HeatFlow_RealHeat`, `WeakHessian_HeatFlow_RealHeatRangeError`, `WeakHessian_LocalBounds_ComplexifyReal`, `WeakHessian_LocalBounds_ConstMul`, `WeakHessian_LocalBounds_ExpMulLp`, `WeakHessian_LocalBounds_GammaAddConstLeft`, `WeakHessian_LocalBounds_GammaNatMulLeft`, `WeakHessian_LocalBounds_MulBounded`, `WeakHessian_LocalBounds_ReLp`, `WeakHessian_Measure_AeIntegralPositiveLipschitz`, `WeakHessian_Measure_InlinedFile0`, `WeakHessian_Measure_LocalSlopeNotMem`, `WeakHessian_Sobolev_AddConst`, `WeakHessian_Sobolev_AeAcRepresentativeMeasurable`, `WeakHessian_Sobolev_CheegerClosedQuadraticEnergy`, `WeakHessian_Sobolev_CompContDiff`, `WeakHessian_Sobolev_CompContDiff2`, `WeakHessian_Sobolev_GlobalCheegerEnergyMinimal`, `WeakHessian_Sobolev_GlobalCheegerEnergyReal`, `WeakHessian_Sobolev_GlobalCheegerEnergyWeak`, `WeakHessian_Sobolev_GradientPairSum`, `WeakHessian_Sobolev_Integral`, `WeakHessian_Sobolev_LocalSobolevLipschitz`, `WeakHessian_Sobolev_Minimal`, `WeakHessian_Sobolev_MulBounded`, `WeakHessian_Sobolev_Piecewise`, `WeakHessian_Sobolev_SobolevCheegerEnergyTop`, `WeakHessian_Sobolev_WeakGradientMul`, `WeakHessian_Transport_AeEvalAe`, `WeakHessian_Transport_AeProdMetricSpeed`, `WeakHessian_Transport_MeasurableVariableIntervalAction`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`; the bundles `OAIQ52Wh003` and `OAIQ52Wh004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ52Wh007`; the statements `OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated`, `OAI.WeakHessian.RCD.cheegerHeat_comparison_weighted`, `OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted`, `OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise`, `OAI.WeakHessian.RCD.weighted_heat_boundedLipschitzRepresentative`, `OAI.WeakHessian.RCD.weighted_heat_concentration`, `OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn`, `OAI.WeakHessian.RCD.weighted_heat_gamma_continuousOn`, `OAI.WeakHessian.RCD.weighted_heat_gamma_memLp` and `OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh003
import Definitions.Def_OAIQ52Wh004

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

lemma localSobolev_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : LocalSobolev m f ↔ LocalSobolev ν f := by
  simp only [LocalSobolev, locallyL2_iff_of_comparable hm hν,
    minimalLocalWeakUpperGradient_iff_of_comparable hm hν]

lemma weakGradient_le_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∀ᵐ x ∂m, weakGradient m f x ≤ (L : ℝ) := by
  by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact (weakGradient_isMinimal h).2 _ (lipschitz_isLocalWeakUpperGradient hfinite hf)
  · simp only [weakGradient, dite_eq_right h, Pi.zero_apply]
    exact ae_of_all m fun _ => L.coe_nonneg

lemma weakGradient_const_mul (c : ℝ) (f : X → ℝ) :
    weakGradient m (fun x => c * f x) =ᵐ[m] (fun x => |c| * weakGradient m f x) := by
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul, abs_zero] using (weakGradient_const (m := m) 0)
  by_cases hf : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact weakGradient_ae_eq_of_isMinimal ((weakGradient_isMinimal hf).const_mul hc)
  · have hcf : ¬ ∃ D, IsMinimalLocalWeakUpperGradient m (fun x => c * f x) D := by
      rintro ⟨D, hD⟩
      have hinv := hD.const_mul (inv_ne_zero hc)
      simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hinv
      exact hf ⟨_, hinv⟩
    simp only [weakGradient, dite_eq_right hcf, dite_eq_right hf, Pi.zero_apply, mul_zero]
    exact Filter.EventuallyEq.rfl

lemma gamma_self (f : X → ℝ) :
    gamma m f f =ᵐ[m] (fun x => (weakGradient m f x) ^ 2) := by
  have hsum : (fun x => f x + f x) = (fun x => 2 * f x) := by funext x; ring
  have hdiff : (fun x => f x - f x) = (fun _ => (0 : ℝ)) := by funext x; simp
  filter_upwards [weakGradient_const_mul (m := m) 2 f, weakGradient_const (m := m) 0]
    with x hx hz
  simp only [gamma, hsum, hdiff, hx, hz]
  norm_num
  ring

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

lemma weakGradient_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    weakGradient m f =ᵐ[m] weakGradient m g := by
  by_cases hf : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact (weakGradient_isMinimal hf).ae_eq
      ((weakGradient_isMinimal ((exists_isMinimal_congr_ae hfg).mp hf)).congr_ae
        hfg.symm Filter.EventuallyEq.rfl)
  · have hg := mt (exists_isMinimal_congr_ae hfg).mpr hf
    simp only [weakGradient, dite_eq_right hf, dite_eq_right hg]
    exact Filter.EventuallyEq.rfl

lemma sobolev_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[m] g) :
    Sobolev m f ↔ Sobolev m g := by
  constructor
  · intro h
    exact ⟨h.1.ae_eq hfg, (localSobolev_congr_ae hfg).mp h.2.1,
      h.2.2.ae_eq (weakGradient_congr_ae hfg)⟩
  · intro h
    exact ⟨h.1.ae_eq hfg.symm, (localSobolev_congr_ae hfg).mpr h.2.1,
      h.2.2.ae_eq (weakGradient_congr_ae hfg).symm⟩

lemma gamma_congr_ae {f f' g g' : X → ℝ} (hff : f =ᵐ[m] f')
    (hgg : g =ᵐ[m] g') : gamma m f g =ᵐ[m] gamma m f' g' := by
  filter_upwards [weakGradient_congr_ae (hff.add hgg),
    weakGradient_congr_ae (hff.sub hgg)] with x hp hm
  change weakGradient m (fun y => f y + g y) x =
    weakGradient m (fun y => f' y + g' y) x at hp
  change weakGradient m (fun y => f y - g y) x =
    weakGradient m (fun y => f' y - g' y) x at hm
  simp only [gamma, hp, hm]

end WeakHessian

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

lemma IsLocalWeakUpperGradient.ae_ae_subinterval_le {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : Measurable f) (hDm : Measurable D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) (s : Time) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ENNReal.ofReal |f (evalReal γ t) - f (γ s)| ≤
        ∫⁻ r in uIcc (s : ℝ) t,
          ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r := by
  let : IsProbabilityMeasure π := hπ.1
  have ham : Measurable (fun p : Curve X × ℝ =>
      ENNReal.ofReal (D (evalReal p.1 p.2)) * metricSpeed p.1 p.2) :=
    (hDm.comp continuous_evalReal.measurable).ennreal_ofReal.mul measurable_metricSpeed
  apply (Measure.ae_ae_comm (p := fun γ t =>
    ENNReal.ofReal |f (evalReal γ t) - f (γ s)| ≤
      ∫⁻ r in uIcc (s : ℝ) t,
        ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r) ?_).mpr
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    let t' : Time := ⟨t,ht⟩
    rcases lt_trichotomy (s : ℝ) t with h|h|h
    · filter_upwards [hD.ae_subinterval_le hf.aemeasurable hπ hb s t' h] with γ hγ
      simpa only [uIcc_of_le h.le, ← evalReal_coe γ t'] using hγ
    · have heq : t' = s := Subtype.ext h.symm
      have hev : ∀ γ : Curve X, evalReal γ t = γ s := fun γ => by
        exact (evalReal_coe γ t').trans (congrArg γ heq)
      exact ae_of_all _ fun γ => by rw [hev, sub_self, abs_zero, ENNReal.ofReal_zero]; exact bot_le
    · have hh := hD.ae_subinterval_le hf.aemeasurable hπ hb t' s h
      filter_upwards [hh] with γ hγ
      simpa only [uIcc_of_ge h.le, ← evalReal_coe γ t', abs_sub_comm] using hγ
  · exact measurableSet_le
      ((hf.comp continuous_evalReal.measurable).sub
        (hf.comp ((continuous_eval_const s).measurable.comp measurable_fst))).abs.ennreal_ofReal
      (measurable_variable_interval_action ham s)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_AeAcRepresentativeMeasurable
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

lemma IsLocalWeakUpperGradient.ae_exists_ac_representative_measurable {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : Measurable f) (hDm : Measurable D)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ∃ q : ℝ → ℝ,
      AbsolutelyContinuousOnInterval q 0 1 ∧ q 0 = f (γ timeZero) ∧ q 1 = f (γ timeOne) ∧
      (q =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun t => f (evalReal γ t)) ∧
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv q t| ≤ ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  let : Nonempty Time := ⟨timeZero⟩
  let d : ℕ → Time := fun n => match n with
    | 0 => timeZero
    | 1 => timeOne
    | n + 2 => TopologicalSpace.denseSeq Time n
  have hd : DenseRange d := by
    apply DenseRange.of_comp (g := fun n => n + 2)
    exact TopologicalSpace.denseRange_denseSeq Time
  have hall : ∀ᵐ γ ∂π, ∀ i : ℕ, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ENNReal.ofReal |f (evalReal γ t) - f (γ (d i))| ≤
        ∫⁻ r in uIcc (d i : ℝ) t,
          ENNReal.ofReal (D (evalReal γ r)) * metricSpeed γ r :=
    ae_all_iff.mpr fun i => hD.ae_ae_subinterval_le hf hDm hπ hb (d i)
  filter_upwards [hD.ae_action_data hπ hb,
    hD.ae_dense_subinterval_le hf.aemeasurable hπ hb d, hall] with γ hDa hDb hp
  have hDb' : ∀ i j, (d i : ℝ) < d j →
      ENNReal.ofReal |f (evalReal γ (d j)) - f (evalReal γ (d i))| ≤
        ∫⁻ t in Icc (d i : ℝ) (d j : ℝ),
          ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
    simpa only [evalReal_coe] using hDb
  obtain ⟨q,hq,heq⟩ := WeakHessianCalculus.exists_ac_representative
    (q := fun t => f (evalReal γ t)) hDa.1 hDa.2 d hDb'
  have hqd : ∀ i, q (d i) = f (γ (d i)) := by simpa only [evalReal_coe] using heq
  refine ⟨q,hq,hqd 0,hqd 1,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr hp, ae_restrict_mem measurableSet_Icc] with t ht htm
    exact WeakHessianCalculus.eq_of_dense_action_bounds hq hDa.1 hDa.2 d hd htm
      (by simpa only [hqd] using ht)
  · exact WeakHessianCalculus.ae_deriv_le_of_dense_action hq hDa.1 hDa.2 d hd
      (by simpa only [hqd] using hDb)

lemma IsLocalWeakUpperGradient.ae_exists_ac_representative {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∀ᵐ γ ∂π, ∃ q : ℝ → ℝ,
      AbsolutelyContinuousOnInterval q 0 1 ∧ q 0 = f (γ timeZero) ∧ q 1 = f (γ timeOne) ∧
      (q =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun t => f (evalReal γ t)) ∧
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv q t| ≤ ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t := by
  have hDm := hD.1.aemeasurable
  have hD' := hD.congr_ae hf.ae_eq_mk hDm.ae_eq_mk
  filter_upwards [hD'.ae_exists_ac_representative_measurable hf.measurable_mk
      hDm.measurable_mk hπ hb, hπ.ae_eval_of_ae hf.ae_eq_mk timeZero,
      hπ.ae_eval_of_ae hf.ae_eq_mk timeOne, hπ.ae_ae_eval_of_ae hf.ae_eq_mk,
      hπ.ae_ae_eval_of_ae hDm.ae_eq_mk] with γ hγ h0 h1 heq hDeq
  obtain ⟨q,hq,hq0,hq1,hqa,hqd⟩ := hγ
  refine ⟨q,hq,hq0.trans h0.symm,hq1.trans h1.symm,hqa.trans (Filter.EventuallyEq.symm heq),?_⟩
  filter_upwards [hqd,hDeq] with t ht hDt
  rwa [← hDt] at ht

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

lemma IsLocalWeakUpperGradient.mul_bounded {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m g E)
    (hf : LocallyL2 m f) (hg : AEMeasurable g m)
    {A B : ℝ} (hgB : ∀ᵐ x ∂m, |g x| ≤ A) (hEB : ∀ᵐ x ∂m, |E x| ≤ B) :
    IsLocalWeakUpperGradient m (fun x => f x * g x)
      (fun x => |g x| * D x + |f x| * E x) := by
  have hcalD : LocallyL2 m (fun x => |g x| * D x) := by
    simpa only [mul_comm] using hD.1.mul_bounded hg.abs.aestronglyMeasurable
      (by simpa only [abs_abs] using hgB)
  have hfn : LocallyL2 m (fun x => |f x|) := fun o R hR => by
    simpa only [Real.norm_eq_abs] using (hf o R hR).norm
  have hcalE : LocallyL2 m (fun x => |f x| * E x) :=
    hfn.mul_bounded hE.1.aestronglyMeasurable hEB
  refine ⟨fun o R hR => (hcalD o R hR).add (hcalE o R hR), ?_, ?_⟩
  · filter_upwards [hD.2.1,hE.2.1] with x hDx hEx
    exact add_nonneg (mul_nonneg (abs_nonneg _) hDx) (mul_nonneg (abs_nonneg _) hEx)
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_exists_ac_representative hf.aemeasurable hπ hb,
        hE.ae_exists_ac_representative hg hπ hb,
        hπ.ae_ae_eval_of_ae hD.2.1, hπ.ae_ae_eval_of_ae hE.2.1] with γ hq hr hDn hEn
    obtain ⟨q,hq,hq0,hq1,hqeq,hqd⟩ := hq
    obtain ⟨r,hr,hr0,hr1,hreq,hrd⟩ := hr
    have hp : AbsolutelyContinuousOnInterval (fun t => q t * r t) 0 1 := hq.mul hr
    have hder : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv (fun t => q t * r t) t| ≤
          ENNReal.ofReal (|g (evalReal γ t)| * D (evalReal γ t) +
            |f (evalReal γ t)| * E (evalReal γ t)) * metricSpeed γ t := by
      filter_upwards [hqeq,hreq,hqd,hrd,hDn,hEn,
        ae_restrict_of_ae hq.ae_differentiableAt, ae_restrict_of_ae hr.ae_differentiableAt,
        ae_restrict_mem measurableSet_Icc] with t hqt hrt hd he hDn hEn hqa hra htm
      have htt : t ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using htm
      change ENNReal.ofReal |deriv (q * r) t| ≤ _
      rw [deriv_mul (hqa htt) (hra htt)]
      calc
        ENNReal.ofReal |deriv q t * r t + q t * deriv r t| ≤
            ENNReal.ofReal (|r t| * |deriv q t| + |q t| * |deriv r t|) := by
          apply ENNReal.ofReal_le_ofReal
          simpa only [abs_mul, mul_comm (|deriv q t|)] using
            abs_add_le (deriv q t * r t) (q t * deriv r t)
        _ = ENNReal.ofReal |r t| * ENNReal.ofReal |deriv q t| +
            ENNReal.ofReal |q t| * ENNReal.ofReal |deriv r t| := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]
        _ ≤ ENNReal.ofReal |r t| * (ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t) +
            ENNReal.ofReal |q t| * (ENNReal.ofReal (E (evalReal γ t)) * metricSpeed γ t) :=
          add_le_add (mul_le_mul' le_rfl hd) (mul_le_mul' le_rfl he)
        _ = _ := by
          rw [hqt,hrt, ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hDn)
            (mul_nonneg (abs_nonneg _) hEn), ENNReal.ofReal_mul (abs_nonneg _),
            ENNReal.ofReal_mul (abs_nonneg _), add_mul, mul_assoc, mul_assoc]
    calc
      ENNReal.ofReal |f (γ timeOne) * g (γ timeOne) - f (γ timeZero) * g (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv (fun t => q t * r t) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hp.integral_deriv_eq_sub,
          hq0,hq1,hr0,hr1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (fun t => q t * r t) t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono_ae (by simpa only [Real.enorm_eq_ofReal_abs] using hder)

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

lemma IsLocalWeakUpperGradient.of_dominated_ae_tendsto {f D B : X → ℝ} {Dn : ℕ → X → ℝ}
    (hn : ∀ n, IsLocalWeakUpperGradient m f (Dn n))
    (hD : LocallyL2 m D) (hB : LocallyL2 m B)
    (hbound : ∀ n, ∀ᵐ x ∂m, Dn n x ≤ B x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => Dn n x) atTop (𝓝 (D x))) :
    IsLocalWeakUpperGradient m f D := by
  refine ⟨hD, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr (fun n => (hn n).2.1), hlim] with x hx hl
    exact ge_of_tendsto hl (Eventually.of_forall hx)
  · intro π hπ hb
    let : IsProbabilityMeasure π := hπ.1
    let ν := π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
    let action : (X → ℝ) → Curve X × ℝ → ℝ≥0∞ := fun g z =>
      ENNReal.ofReal (g (evalReal z.1 z.2)) * metricSpeed z.1 z.2
    have hbfin : (∫⁻ z, action B z ∂ν) ≠ ∞ := by
      rw [lintegral_prod _ (hπ.aemeasurable_action hB)]
      exact (hπ.lintegral_action_lt_top hb hB).ne
    have hnmeas : ∀ n, AEMeasurable (action (Dn n)) ν := fun n => hπ.aemeasurable_action (hn n).1
    have habound : ∀ n, action (Dn n) ≤ᵐ[ν] action B := by
      intro n
      filter_upwards [hπ.ae_prod_eval_of_ae (hbound n)] with z hz
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hz) _
    have halim : ∀ᵐ z ∂ν, Tendsto (fun n => action (Dn n) z) atTop (𝓝 (action D z)) := by
      filter_upwards [hπ.ae_prod_eval_of_ae hlim, hπ.ae_prod_metricSpeed_lt_top] with z hz hsz
      exact (ENNReal.continuous_mul_const hsz.ne).continuousAt.tendsto.comp
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz)
    have hi := tendsto_lintegral_of_dominated_convergence' (action B) hnmeas habound hbfin halim
    rw [← lintegral_prod _ (hπ.aemeasurable_action hD)]
    apply ge_of_tendsto hi
    exact Eventually.of_forall fun n => by
      dsimp only [action, ν]
      rw [lintegral_prod _ (hπ.aemeasurable_action (hn n).1)]
      exact (hn n).2.2 π hπ hb

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_Minimal
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
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.exists_minimal {f D₀ : X → ℝ}
    (hD₀ : IsLocalWeakUpperGradient m f D₀) (hf : AEMeasurable f m)
    (hfinite : FiniteOnBoundedSets m) :
    ∃ D, IsMinimalLocalWeakUpperGradient m f D := by
  let B : X → ℝ := fun x => max 0 (D₀ x)
  have hBnon : ∀ x, 0 ≤ B x := fun _ => le_max_left _ _
  have heq : D₀ =ᵐ[m] B := by
    filter_upwards [hD₀.2.1] with x hx
    exact (max_eq_right hx).symm
  have hB : IsLocalWeakUpperGradient m f B :=
    hD₀.congr_ae Filter.EventuallyEq.rfl heq
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  obtain ⟨μ, hμ, hmμ, hμm⟩ := exists_isFiniteMeasure_absolutelyContinuous m
  let : IsFiniteMeasure μ := hμ
  obtain ⟨ν, hμν, hνμ, hBi⟩ := WeakHessianCalculus.exists_equivalent_integrable_measure μ
    (hB.1.aemeasurable.mono_ac hμm)
  have hmν : m ≪ ν := hmμ.trans hμν
  have hνm : ν ≪ m := hνμ.trans hμm
  let S : Set (X → ℝ) := {D | IsLocalWeakUpperGradient m f D ∧ ∀ x, 0 ≤ D x ∧ D x ≤ B x}
  have hS : S.Nonempty := ⟨B,hB, fun x => ⟨hBnon x, le_rfl⟩⟩
  have hSm : ∀ D ∈ S, AEMeasurable D ν :=
    fun _ hD => hD.1.1.aemeasurable.mono_ac hνm
  have hSmin : ∀ D ∈ S, ∀ E ∈ S, (fun x => Min.min (D x) (E x)) ∈ S := by
    intro D hD E hE
    exact ⟨hD.1.min_measurable hE.1 hf, fun x => ⟨le_min (hD.2 x).1 (hE.2 x).1,
      (min_le_left _ _).trans (hD.2 x).2⟩⟩
  have hSclosed : ∀ u : ℕ → X → ℝ, (∀ n, u n ∈ S) → ∀ D : X → ℝ,
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (D x))) → D ∈ S := by
    intro u hu D hlim
    have hDb : ∀ x, 0 ≤ D x ∧ D x ≤ B x := fun x =>
      ⟨ge_of_tendsto (hlim x) (Eventually.of_forall fun n => ((hu n).2 x).1),
        le_of_tendsto (hlim x) (Eventually.of_forall fun n => ((hu n).2 x).2)⟩
    have hDm : AEStronglyMeasurable D m :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (hu n).1.1.aemeasurable.aestronglyMeasurable) (ae_of_all _ hlim)
    have hDL : LocallyL2 m D := by
      intro o R hR
      apply (hB.1 o R hR).mono' hDm.restrict
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hDb x).1,
          abs_of_nonneg (hBnon x)] using (hDb x).2
    exact ⟨IsLocalWeakUpperGradient.of_dominated_ae_tendsto (fun n => (hu n).1) hDL hB.1
      (fun n => ae_of_all _ fun x => ((hu n).2 x).2) (ae_of_all _ hlim), hDb⟩
  obtain ⟨D,hD,hDmin⟩ := WeakHessianCalculus.exists_ae_minimum_dominated ν S B hBi
    hS hSm (fun _ h => h.2) hSmin hSclosed
  refine ⟨D,hD.1,?_⟩
  intro E hE
  let E' : X → ℝ := fun x => max 0 (Min.min (D x) (E x))
  have hEq : (fun x => Min.min (D x) (E x)) =ᵐ[m] E' := by
    filter_upwards [hE.2.1] with x hx
    exact (max_eq_right (le_min (hD.2 x).1 hx)).symm
  have hE' : E' ∈ S := by
    refine ⟨(hD.1.min_measurable hE hf).congr_ae Filter.EventuallyEq.rfl hEq, fun x => ?_⟩
    exact ⟨le_max_left _ _, max_le (hBnon x) ((min_le_left _ _).trans (hD.2 x).2)⟩
  filter_upwards [hmν.ae_le (hDmin E' hE'), hEq] with x hx heq
  exact hx.trans (heq ▸ min_le_right (D x) (E x))

lemma localSobolev_iff_exists_upperGradient (hfinite : FiniteOnBoundedSets m) {f : X → ℝ} :
    LocalSobolev m f ↔ LocallyL2 m f ∧ ∃ D, IsLocalWeakUpperGradient m f D := by
  constructor
  · rintro ⟨hf,D,hD⟩
    exact ⟨hf,D,hD.1⟩
  · rintro ⟨hf,D,hD⟩
    exact ⟨hf,hD.exists_minimal hf.aemeasurable hfinite⟩


lemma LocalSobolev.add (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    LocalSobolev m (fun x => f x + g x) := by
  apply (localSobolev_iff_exists_upperGradient hfinite).mpr
  exact ⟨hf.1.add hg.1, _, (weakGradient_isMinimal hf.2).1.add (weakGradient_isMinimal hg.2).1 hf.1⟩

lemma weakGradient_add_le (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, weakGradient m (fun x => f x + g x) x ≤
      weakGradient m f x + weakGradient m g x :=
  (weakGradient_isMinimal (hf.add hfinite hg).2).2 _
    ((weakGradient_isMinimal hf.2).1.add (weakGradient_isMinimal hg.2).1 hf.1)

lemma Sobolev.of_upperGradient (hfinite : FiniteOnBoundedSets m) {f D : X → ℝ}
    (hf : MemLp f 2 m) (hD : IsLocalWeakUpperGradient m f D) (hD₂ : MemLp D 2 m) :
    Sobolev m f := by
  have hmin := hD.exists_minimal hf.aestronglyMeasurable.aemeasurable hfinite
  refine ⟨hf, ⟨fun o R _ => hf.restrict (Metric.ball o R), hmin⟩, ?_⟩
  have hw := weakGradient_isMinimal hmin
  apply hD₂.mono hw.1.1.aestronglyMeasurable
  filter_upwards [hw.2 _ hD,hw.1.2.1,hD.2.1] with x hx hwx hDx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hwx, abs_of_nonneg hDx] using hx

lemma Sobolev.add (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : Sobolev m f) (hg : Sobolev m g) : Sobolev m (fun x => f x + g x) :=
  Sobolev.of_upperGradient hfinite (hf.1.add hg.1)
    ((weakGradient_isMinimal hf.2.1.2).1.add (weakGradient_isMinimal hg.2.1.2).1 hf.2.1.1)
    (hf.2.2.add hg.2.2)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalSobolev.const_mul {f : X → ℝ} (hf : LocalSobolev m f) (c : ℝ) :
    LocalSobolev m (fun x => c * f x) :=
by
  refine ⟨hf.1.const_mul c, ?_⟩
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul] using ⟨_, isMinimalLocalWeakUpperGradient_const (m := m) 0⟩
  · exact ⟨_, (weakGradient_isMinimal hf.2).const_mul hc⟩

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma Sobolev.const_mul {f : X → ℝ} (hf : Sobolev m f) (c : ℝ) :
    Sobolev m (fun x => c * f x) :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c,
    (hf.2.2.const_mul |c|).ae_eq (weakGradient_const_mul c f).symm⟩

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma Sobolev.neg {f : X → ℝ} (hf : Sobolev m f) : Sobolev m (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

lemma Sobolev.sub (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : Sobolev m f) (hg : Sobolev m g) : Sobolev m (fun x => f x - g x) :=
  hf.add hfinite hg.neg

lemma Sobolev.mul_bounded (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : Sobolev m f) (hg : LocalSobolev m g)
    {A B : ℝ} (hgB : ∀ᵐ x ∂m, |g x| ≤ A)
    (hEB : ∀ᵐ x ∂m, |weakGradient m g x| ≤ B) :
    Sobolev m (fun x => f x * g x) := by
  apply Sobolev.of_upperGradient hfinite (memLp_mul_bounded hf.1 hg.1.aestronglyMeasurable hgB)
    ((weakGradient_isMinimal hf.2.1.2).1.mul_bounded (weakGradient_isMinimal hg.2).1
      hf.2.1.1 hg.1.aemeasurable hgB hEB)
  have hD : MemLp (fun x => |g x| * weakGradient m f x) 2 m := by
    simpa only [mul_comm, Real.norm_eq_abs] using memLp_mul_bounded hf.2.2 hg.1.aestronglyMeasurable.norm
      (by simpa only [Real.norm_eq_abs,abs_abs] using hgB)
  have hE : MemLp (fun x => |f x| * weakGradient m g x) 2 m :=
    memLp_mul_bounded (by simpa only [Real.norm_eq_abs] using hf.1.norm)
      (weakGradient_isMinimal hg.2).1.1.aestronglyMeasurable hEB
  exact hD.add hE

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_WeakGradientMul
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
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_mul_le (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : Sobolev m f) (hη : LocalSobolev m η) {A B : ℝ}
    (hηB : ∀ᵐ x ∂m, |η x| ≤ A) (hDB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (fun y => f y*η y) x ≤
      |η x| *weakGradient m f x + |f x| *weakGradient m η x :=
  (weakGradient_isMinimal (hf.mul_bounded hfinite hη hηB hDB).2.1.2).2 _
    ((weakGradient_isMinimal hf.2.1.2).1.mul_bounded (weakGradient_isMinimal hη.2).1
      hf.2.1.1 hη.1.aemeasurable hηB hDB)

lemma weakGradient_mul_error (hfinite : FiniteOnBoundedSets m) {f η ξ : X → ℝ}
    (hf : Sobolev m f) (hη : LocalSobolev m η) (hξ : LocalSobolev m ξ)
    (hθη : ∀ x, η x * ξ x = 1) (hη0 : ∀ᵐ x ∂m, 0 ≤ η x) (hξ0 : ∀ᵐ x ∂m, 0 ≤ ξ x)
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hηA : ∀ᵐ x ∂m, |η x| ≤ A) (hDη : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (hξC : ∀ᵐ x ∂m, |ξ x| ≤ C) (hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ D) :
    ∀ᵐ x ∂m, |weakGradient m (fun y => f y*η y) x - η x*weakGradient m f x| ≤
      (B + A^2*D)*|f x| := by
  have hfu := hf.mul_bounded hfinite hη hηA hDη
  have hid : (fun y => (f y * η y)*ξ y) = f := by
    funext y
    rw [mul_assoc, hθη, mul_one]
  have hu := weakGradient_mul_le hfinite hf hη hηA hDη
  have hl := weakGradient_mul_le hfinite hfu hξ hξC hDξ
  rw [hid] at hl
  filter_upwards [hu,hl,hη0,hξ0,hηA,hDη,hDξ] with x hu hl he0 hx0 heA hdη hdξ
  rw [abs_of_nonneg he0] at hu heA
  rw [abs_of_nonneg hx0,abs_mul,abs_of_nonneg he0] at hl
  have hum : weakGradient m (fun y => f y*η y) x - η x*weakGradient m f x ≤ |f x| *B := by
    have H := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdη) (abs_nonneg (f x))
    linarith
  have hlm := mul_le_mul_of_nonneg_left hl he0
  have hmul : η x * (ξ x * weakGradient m (fun y => f y*η y) x +
      |f x| * η x * weakGradient m ξ x) =
      weakGradient m (fun y => f y*η y) x + |f x| * (η x)^2 * weakGradient m ξ x := by
    calc
      _ = (η x*ξ x)*weakGradient m (fun y => f y*η y) x +
        |f x| *(η x)^2*weakGradient m ξ x := by ring
      _ = _ := by rw [hθη,one_mul]
  rw [hmul] at hlm
  have hsq : (η x)^2 ≤ A^2 := sq_le_sq₀ he0 hA |>.mpr heA
  have hbξ : |f x| *(η x)^2*weakGradient m ξ x ≤ |f x| *A^2*D := by
    calc
      _ ≤ |f x| *(η x)^2*D := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hdξ) (by positivity)
      _ ≤ |f x| *A^2*D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (abs_nonneg _)) hD
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hB (abs_nonneg (f x))]
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg A) hD) (abs_nonneg (f x))]

end WeakHessian

open Filter
open scoped Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NormLpSqIntegral
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
open Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma tendsto_gradient_mul_error (hfinite : FiniteOnBoundedSets m)
    {fs : ℕ → X → ℝ} (hs : ∀ n, Sobolev m (fs n)) {η ξ : X → ℝ}
    (hη : LocalSobolev m η) (hξ : LocalSobolev m ξ)
    (hei : ∀ x, η x * ξ x = 1) (hη0 : ∀ᵐ x ∂m, 0 ≤ η x) (hξ0 : ∀ᵐ x ∂m, 0 ≤ ξ x)
    {A B C D R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hηA : ∀ᵐ x ∂m, |η x| ≤ A) (hDη : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (hξC : ∀ᵐ x ∂m, |ξ x| ≤ C) (hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ D)
    (hR : ∀ n, ‖(hs n).2.2.toLp (weakGradient m (fs n))‖ ≤ R)
    (ht : Tendsto (fun n => (hs n).1.toLp (fs n)) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ x, (weakGradient m (fun y => fs n y*η y) x)^2 ∂m) -
      ∫ x, (weakGradient m (fs n) x * η x)^2 ∂m) atTop (𝓝 0) := by
  let hu (n : ℕ) := hs n |>.mul_bounded hfinite hη hηA hDη
  let hv (n : ℕ) := memLp_mul_bounded (hs n).2.2 hη.1.aestronglyMeasurable hηA
  let a (n : ℕ) := (hu n).2.2.toLp (weakGradient m (fun y => fs n y*η y))
  let b (n : ℕ) := (hv n).toLp (fun x => weakGradient m (fs n) x * η x)
  have he (n : ℕ) : ‖a n-b n‖ ≤ (B+A^2*D)*‖(hs n).1.toLp (fs n)‖ := by
    apply norm_toLp_le_mul_of_ae ((hu n).2.2.sub (hv n)) (hs n).1
    have H := weakGradient_mul_error hfinite (hs n) hη hξ hei hη0 hξ0 hA hB hD hηA hDη hξC hDξ
    simpa only [Pi.sub_apply, mul_comm (η _) (weakGradient m (fs n) _)] using H
  have hb (n : ℕ) : ‖b n‖ ≤ A*R := by
    apply le_trans (norm_toLp_le_mul_of_ae (hv n) (hs n).2.2 ?_) (mul_le_mul_of_nonneg_left (hR n) hA)
    filter_upwards [hηA] with x hx
    simpa only [abs_mul, mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg (weakGradient m (fs n) x))
  have H := tendsto_norm_sq_sub_norm_sq he hb ht
  simpa only [a,b,norm_toLp_sq_eq_integral] using H
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

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

lemma exists_minimalGradient_energy_le_cheeger
    (hfinite : FiniteOnBoundedSets m) {f : X → ℝ} (hf : MemLp f 2 m)
    (hch : cheegerEnergy m f < ∞) :
    ∃ D : Lp ℝ 2 m, IsMinimalLocalWeakUpperGradient m f D ∧
      ENNReal.ofReal (‖D‖ ^ 2 / 2) ≤ cheegerEnergy m f := by
  obtain ⟨E,hE,henergy⟩ := exists_upperGradient_energy_le_cheeger hfinite hf hch
  obtain ⟨D,hD,hmin⟩ := exists_norm_minimal_upperGradient
    ⟨E, hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl⟩
  have hminimal := norm_minimal_is_minimal hD hmin
  refine ⟨D, ⟨hminimal.1.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, ?_⟩, ?_⟩
  · intro E hE
    exact hminimal.2 E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)
  · apply le_trans _ henergy
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg D)
        (hmin E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)) 2) (by norm_num)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ConstMul
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
variable {X : Type*} [MetricSpace X]
variable [MeasurableSpace X] {m : Measure X}
attribute [local instance] Classical.propDecidable

lemma cheegerEnergy_zero : cheegerEnergy m (fun _ : X => (0:ℝ)) = 0 := by
  apply le_antisymm _ bot_le
  change cheegerEnergy m (fun _ : X => (0:ℝ)) ≤ 0
  have hh := cheegerEnergy_le_liminf (MemLp.zero' (μ := m))
    (fs := fun _ _ => (0:ℝ)) (fun _ => ⟨⟨0, by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp⟩, MemLp.zero'⟩) (by simp)
  simpa only [localSlope_zero, zero_pow (by omega : (2:ℕ) ≠ 0),
    lintegral_zero, mul_zero, liminf_const] using hh

lemma cheegerEnergy_const_mul_le (c : ℝ) (f : X → ℝ) :
    cheegerEnergy m (fun x => c * f x) ≤ ENNReal.ofReal (c^2) * cheegerEnergy m f := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul, zero_pow (by omega : (2:ℕ) ≠ 0), ENNReal.ofReal_zero,
      cheegerEnergy_zero, le_refl]
  have hC0 : ENNReal.ofReal (c^2) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hc))
  by_cases he : cheegerEnergy m f = ∞
  · simp only [he, ENNReal.mul_top hC0, le_top]
  have hf : MemLp f 2 m := by
    by_contra H
    exact he (by simp only [cheegerEnergy, ite_eq_right H])
  let S : Set ℝ≥0∞ := {a | ∃ fs : ℕ → X → ℝ,
      (∀ n, GloballyLipschitz (fs n) ∧ MemLp (fs n) 2 m) ∧
      Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 m) atTop (𝓝 0) ∧
      a = liminf (fun n => (2:ℝ≥0∞)⁻¹ * ∫⁻ x, localSlope (fs n) x ^ 2 ∂m) atTop}
  have hE : cheegerEnergy m f = sInf S := by simp only [cheegerEnergy, ite_eq_left hf, S]
  have hS : S.Nonempty := by
    by_contra H
    rw [Set.not_nonempty_iff_eq_empty.mp H, sInf_empty] at hE
    exact he hE
  let : Nonempty S := hS.to_subtype
  rw [hE, sInf_eq_iInf', ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)]
  apply le_iInf
  intro a
  obtain ⟨fs, hfs, hconv, ha⟩ := a.property
  have hfC : MemLp (fun x => c * f x) 2 m := hf.const_mul c
  have hcconv : Tendsto (fun n => eLpNorm (fun x => c * fs n x - c * f x) 2 m)
      atTop (𝓝 0) := by
    simp_rw [← mul_sub]
    change Tendsto (fun n => eLpNorm (c • (fun x => fs n x - f x)) 2 m) atTop (𝓝 0)
    simp_rw [eLpNorm_const_smul]
    simpa only [mul_zero, Function.comp_def] using (ENNReal.continuous_const_mul (show ‖c‖ₑ ≠ ∞ by finiteness)).tendsto 0 |>.comp hconv
  have hmain := cheegerEnergy_le_liminf hfC
    (fun n => ⟨(hfs n).1.const_mul c, (hfs n).2.const_mul c⟩) hcconv
  refine hmain.trans_eq ?_
  simp_rw [slope_energy_const_mul]
  rw [ha]
  exact (Monotone.map_liminf_of_continuousAt
    (f := fun a : ℝ≥0∞ => ENNReal.ofReal (c^2) * a)
    (fun _ _ h => mul_le_mul_right h _) _
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt).symm

lemma cheegerEnergy_const_mul (c : ℝ) (f : X → ℝ) :
    cheegerEnergy m (fun x => c * f x) = ENNReal.ofReal (c^2) * cheegerEnergy m f := by
  apply le_antisymm (cheegerEnergy_const_mul_le c f)
  by_cases hc : c = 0
  · simp [hc]
  have H := cheegerEnergy_const_mul_le (m := m) c⁻¹ (fun x => c * f x)
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at H
  have H' := mul_le_mul_right H (ENNReal.ofReal (c^2))
  have hcancel : ENNReal.ofReal (c^2) * ENNReal.ofReal (c⁻¹^2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg c), ← mul_pow, mul_inv_cancel₀ hc, one_pow,
      ENNReal.ofReal_one]
  simpa only [← mul_assoc, hcancel, one_mul] using H'

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CheegerClosedQuadraticEnergy
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheeger_closedQuadraticEnergy (h : QuadraticCheegerEnergy m) :
    ClosedQuadraticEnergy (fun f : Lp ℝ 2 m => cheegerEnergy m (f : X → ℝ)) := by
  refine ⟨lowerSemicontinuous_cheegerEnergy, ?_, ?_, ?_⟩
  · rw [cheegerEnergy_congr_ae (Lp.coeFn_zero ℝ 2 m)]
    exact cheegerEnergy_zero
  · intro c f
    rw [cheegerEnergy_congr_ae (Lp.coeFn_smul c f)]
    exact cheegerEnergy_const_mul c (f : X → ℝ)
  · intro f g hf hg
    rw [cheegerEnergy_congr_ae (Lp.coeFn_add f g), cheegerEnergy_congr_ae (Lp.coeFn_sub f g)]
    exact h (f : X → ℝ) (g : X → ℝ) hf hg

end WeakHessian

end
end InlinedFile0

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

lemma cheeger_domain_dense [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    [IsLocallyFiniteMeasure m] (h : QuadraticCheegerEnergy m) :
    (cheeger_closedQuadraticEnergy h).domain.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro H hH
  change H = 0
  have hAE : (H : X → ℝ) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((Lp.memLp H).locallyIntegrable (by norm_num))
    intro φ hc hφ
    obtain ⟨L,hL⟩ := hφ
    have hm : MemLp φ 2 m := hL.continuous.memLp_of_hasCompactSupport hc
    have hd : hm.toLp φ ∈ (cheeger_closedQuadraticEnergy h).domain := by
      change cheegerEnergy m (hm.toLp φ : X → ℝ) < ∞
      rw [cheegerEnergy_congr_ae hm.coeFn_toLp]
      exact cheegerEnergy_lipschitz_compact_lt_top hL hc
    have hz := Submodule.inner_left_of_mem_orthogonal hd hH
    rw [L2.inner_def] at hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  apply Lp.ext
  exact hAE.trans (Lp.coeFn_zero ℝ 2 m).symm

end WeakHessian

open Set Filter
open scoped Topology ENNReal NNReal

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
lemma weakGradient_add_const_of_exists {f : X → ℝ}
    (hf : ∃ D, IsMinimalLocalWeakUpperGradient m f D) (c : ℝ) :
    weakGradient m (fun x => f x+c) =ᵐ[m] weakGradient m f :=
  weakGradient_ae_eq_of_isMinimal ((weakGradient_isMinimal hf).add_const c)

omit [BorelSpace X] in
lemma LocalSobolev.add_const (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) (c : ℝ) :
    LocalSobolev m (fun x => f x+c) := by
  refine ⟨fun o R hR => ?_,⟨_,(weakGradient_isMinimal hf.2).add_const c⟩⟩
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite _ Metric.isBounded_ball⟩
  exact (hf.1 o R hR).add (memLp_const c)

lemma Sobolev.normalContraction [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (hfinite : FiniteOnBoundedSets m) {f : X → ℝ} (hf : Sobolev m f)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) :
    Sobolev m (η ∘ f) :=
  Sobolev.of_upperGradient hfinite (hη.comp_memLp hη0 hf.1)
    (IsLocalWeakUpperGradient.normalContraction (weakGradient_isMinimal hf.2.1.2).1 hη)
    hf.2.2

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_Piecewise
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

lemma IsLocalWeakUpperGradient.piecewise_on_eq {f g D E : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hE : IsLocalWeakUpperGradient m g E)
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) {s : Set X} (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂m, x ∈ s → f x = g x) :
    IsLocalWeakUpperGradient m f (s.piecewise E D) := by
  refine ⟨?_,?_,?_⟩
  · intro o R hR
    exact MemLp.piecewise hs ((hE.1 o R hR).mono_measure Measure.restrict_le_self)
      ((hD.1 o R hR).mono_measure Measure.restrict_le_self)
  · filter_upwards [hD.2.1,hE.2.1] with x hDx hEx
    by_cases hx : x ∈ s <;> simp only [Set.piecewise, hx, ↓reduceIte] <;> assumption
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_exists_ac_representative hf hπ hb,
      hE.ae_exists_ac_representative hg hπ hb, hπ.ae_ae_eval_of_ae heq] with γ hγ hr hfg
    obtain ⟨q,hq,hq0,hq1,hqeq,hqd⟩ := hγ
    obtain ⟨r,hr,_hr0,_hr1,hreq,hrd⟩ := hr
    have hder : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv q t| ≤
          ENNReal.ofReal ((s.piecewise E D) (evalReal γ t)) * metricSpeed γ t := by
      filter_upwards [hqeq,hreq,hqd,hrd,hfg,
        ae_restrict_of_ae (ae_deriv_eq_on_eq q r),
        ae_restrict_of_ae hq.ae_differentiableAt, ae_restrict_of_ae hr.ae_differentiableAt,
        ae_restrict_mem measurableSet_Icc] with t hqt hrt hd he hfg hqr hqa hra htm
      have htt : t ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using htm
      by_cases hx : evalReal γ t ∈ s
      · have heqr := hqr (hqa htt) (hra htt) (hqt.trans ((hfg hx).trans hrt.symm))
        simpa only [Set.piecewise, hx, ↓reduceIte, heqr] using he
      · simpa only [Set.piecewise, hx, ↓reduceIte] using hd
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv q t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hq.integral_deriv_eq_sub, hq0,hq1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv q t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono_ae (by simpa only [Real.enorm_eq_ofReal_abs] using hder)

lemma minimalGradients_locality {f g D E : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D)
    (hE : IsMinimalLocalWeakUpperGradient m g E)
    (hf : AEMeasurable f m) (hg : AEMeasurable g m) {s : Set X} (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂m, x ∈ s → f x = g x) :
    ∀ᵐ x ∂m, x ∈ s → D x = E x := by
  have hfg := hD.2 _ (hD.1.piecewise_on_eq hE.1 hf hg hs heq)
  have hef : ∀ᵐ x ∂m, x ∈ s → g x = f x := by
    filter_upwards [heq] with x hx hsx
    exact (hx hsx).symm
  have hgf := hE.2 _ (hE.1.piecewise_on_eq hD.1 hg hf hs hef)
  filter_upwards [hfg,hgf] with x h₁ h₂ hx
  rw [Set.piecewise_eq_of_mem s E D hx] at h₁
  rw [Set.piecewise_eq_of_mem s D E hx] at h₂
  exact le_antisymm h₁ h₂

lemma weakGradient_locality {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) {s : Set X} (hs : MeasurableSet s)
    (heq : ∀ᵐ x ∂m, x ∈ s → f x = g x) :
    ∀ᵐ x ∂m, x ∈ s → weakGradient m f x = weakGradient m g x :=
  minimalGradients_locality (weakGradient_isMinimal hf.2) (weakGradient_isMinimal hg.2)
    hf.1.aemeasurable hg.1.aemeasurable hs heq

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GradientPairSum
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
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_triangularFold_of_measurable (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) (hfm : Measurable f) {δ : ℝ} (hδ : 0 < δ) :
    weakGradient m (triangularFold δ ∘ f) =ᵐ[m] weakGradient m f := by
  have hF := hf.normalContraction hfinite (triangularFold_lipschitz δ) (triangularFold_zero δ)
  have hFm := (triangularFold_lipschitz δ).continuous.measurable.comp hfm
  have hp (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = f x - δ*(k:ℝ) →
      weakGradient m (triangularFold δ ∘ f) x = weakGradient m f x := by
    have hv := hf.2.1.add_const hfinite (-δ*(k:ℝ))
    have hh := weakGradient_locality hF.2.1 hv
      (measurableSet_eq_fun hFm (hfm.add_const (-δ*(k:ℝ)))) (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,weakGradient_add_const_of_exists hf.2.1.2 (-δ*(k:ℝ))] with x hx he ht
    exact (hx (by simpa only [Function.comp_apply, sub_eq_add_neg, neg_mul] using ht)).trans he
  have hm (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = -(f x - δ*(k:ℝ)) →
      weakGradient m (triangularFold δ ∘ f) x = weakGradient m f x := by
    have hv := (hf.2.1.const_mul (-1)).add_const hfinite (δ*(k:ℝ))
    have hh := weakGradient_locality hF.2.1 hv
      (measurableSet_eq_fun hFm ((hfm.const_mul (-1)).add_const (δ*(k:ℝ))))
      (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,weakGradient_add_const_of_exists (hf.2.1.const_mul (-1)).2 (δ*(k:ℝ)),
      weakGradient_const_mul (m := m) (-1) f] with x hx he hn ht
    have H := hx (by simp only [Function.comp_apply]; linarith [ht])
    simpa only [he, hn, abs_neg, abs_one, one_mul] using H
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hm] with x hp hm
  obtain ⟨k,h|h⟩ := triangularFold_piecewise hδ (f x)
  · exact hp k h
  · exact hm k h

lemma weakGradient_triangularFold (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {δ : ℝ} (hδ : 0 < δ) :
    weakGradient m (triangularFold δ ∘ f) =ᵐ[m] weakGradient m f := by
  let f' := hf.1.aestronglyMeasurable.mk f
  have he : f =ᵐ[m] f' := hf.1.aestronglyMeasurable.ae_eq_mk
  have hf' : Sobolev m f' := (sobolev_congr_ae he).mp hf
  have H := weakGradient_triangularFold_of_measurable hfinite hf'
    hf.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable hδ
  exact (weakGradient_congr_ae (he.fun_comp (triangularFold δ))).trans
    (H.trans (weakGradient_congr_ae he).symm)

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gradientPairSum_symm (f g : X → ℝ) :
    gradientPairSum m f g =ᵐ[m] gradientPairSum m g f := by
  filter_upwards [weakGradient_const_mul (m := m) (-1) (fun x => f x-g x)] with x hx
  have hplus : (fun x => f x+g x) = (fun x => g x+f x) := by funext x; ring
  have hminus : (fun x => -1*(f x-g x)) = (fun x => g x-f x) := by funext x; ring
  simp only [gradientPairSum, hplus, hminus, abs_neg, abs_one, one_mul] at hx ⊢
  rw [hx]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gradientPairSum_neg_left (f g : X → ℝ) :
    gradientPairSum m (fun x => -f x) g =ᵐ[m] gradientPairSum m f g := by
  have hp : (fun x => -1*(f x-g x)) = (fun x => -f x+g x) := by funext x; ring
  have hm : (fun x => -1*(f x+g x)) = (fun x => -f x-g x) := by funext x; ring
  filter_upwards [weakGradient_const_mul (m := m) (-1) (fun x => f x-g x),
      weakGradient_const_mul (m := m) (-1) (fun x => f x+g x)] with x h1 h2
  simp only [hp, hm, abs_neg, abs_one, one_mul] at h1 h2
  unfold gradientPairSum
  rw [h1, h2]
  exact add_comm _ _

lemma gradientPairSum_add_const_left (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    gradientPairSum m (fun x => f x+c) g =ᵐ[m] gradientPairSum m f g := by
  have hp : (fun x => (f x + g x)+c) = (fun x => (f x+c)+g x) := by funext x; ring
  have hm : (fun x => (f x - g x)+c) = (fun x => (f x+c)-g x) := by funext x; ring
  have hn : LocalSobolev m (fun x => -g x) := by simpa using hg.const_mul (-1)
  filter_upwards [weakGradient_add_const_of_exists (hf.add hfinite hg).2 c,
      weakGradient_add_const_of_exists (hf.add hfinite hn).2 c] with x h1 h2
  simp only [← sub_eq_add_neg] at h2
  rw [hp] at h1
  rw [hm] at h2
  simp only [gradientPairSum, h1, h2]

lemma gradientPairSum_locality_left (hfinite : FiniteOnBoundedSets m)
    {f u g : X → ℝ} (hf : LocalSobolev m f) (hu : LocalSobolev m u)
    (hg : LocalSobolev m g) {s : Set X} (hs : MeasurableSet s)
    (he : ∀ᵐ x ∂m, x ∈ s → f x = u x) :
    ∀ᵐ x ∂m, x ∈ s → gradientPairSum m f g x = gradientPairSum m u g x := by
  have hn : LocalSobolev m (fun x => -g x) := by simpa using hg.const_mul (-1)
  have hp := weakGradient_locality (hf.add hfinite hg) (hu.add hfinite hg) hs
    (he.mono fun x hx hm => by rw [hx hm])
  have hm := weakGradient_locality (hf.add hfinite hn) (hu.add hfinite hn) hs
    (he.mono fun x hx hm => by rw [hx hm])
  simp only [← sub_eq_add_neg] at hm
  filter_upwards [hp,hm] with x hp hm hx
  simp only [gradientPairSum, hp hx, hm hx]

lemma gradientPairSum_fold_left_of_measurable (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) (hfm : Measurable f)
    {δ : ℝ} (hδ : 0 < δ) :
    gradientPairSum m (triangularFold δ ∘ f) g =ᵐ[m] gradientPairSum m f g := by
  have hF := hf.normalContraction hfinite (triangularFold_lipschitz δ) (triangularFold_zero δ)
  have hFm := (triangularFold_lipschitz δ).continuous.measurable.comp hfm
  have hp (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = f x - δ*(k:ℝ) →
      gradientPairSum m (triangularFold δ ∘ f) g x = gradientPairSum m f g x := by
    have hv := hf.2.1.add_const hfinite (-δ*(k:ℝ))
    have hh := gradientPairSum_locality_left hfinite hF.2.1 hv hg.2.1
      (measurableSet_eq_fun hFm (hfm.add_const (-δ*(k:ℝ)))) (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,gradientPairSum_add_const_left hfinite hf.2.1 hg.2.1 (-δ*(k:ℝ))]
      with x hx he ht
    exact (hx (by simpa only [Function.comp_apply, sub_eq_add_neg, neg_mul] using ht)).trans he
  have hm (k : ℤ) : ∀ᵐ x ∂m, triangularFold δ (f x) = -(f x - δ*(k:ℝ)) →
      gradientPairSum m (triangularFold δ ∘ f) g x = gradientPairSum m f g x := by
    have hn : LocalSobolev m (fun x => -f x) := by simpa using hf.2.1.const_mul (-1)
    have hv := hn.add_const hfinite (δ*(k:ℝ))
    have hh := gradientPairSum_locality_left hfinite hF.2.1 hv hg.2.1
      (measurableSet_eq_fun hFm (hfm.neg.add_const (δ*(k:ℝ)))) (Eventually.of_forall fun _ h => h)
    filter_upwards [hh,gradientPairSum_add_const_left hfinite hn hg.2.1 (δ*(k:ℝ)),
      gradientPairSum_neg_left (m := m) f g] with x hx he hn ht
    exact (hx (by
      change triangularFold δ (f x) = -f x + δ*(k : ℝ)
      linarith [ht])).trans (he.trans hn)
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hm] with x hp hm
  obtain ⟨k,h|h⟩ := triangularFold_piecewise hδ (f x)
  · exact hp k h
  · exact hm k h

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gradientPairSum_congr_ae {f f' g g' : X → ℝ} (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') :
    gradientPairSum m f g =ᵐ[m] gradientPairSum m f' g' := by
  filter_upwards [weakGradient_congr_ae (hf.add hg),weakGradient_congr_ae (hf.sub hg)]
    with x h1 h2
  change weakGradient m (fun y => f y+g y) x = weakGradient m (fun y => f' y+g' y) x at h1
  change weakGradient m (fun y => f y-g y) x = weakGradient m (fun y => f' y-g' y) x at h2
  unfold gradientPairSum
  rw [h1,h2]

lemma gradientPairSum_fold_left (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {δ : ℝ} (hδ : 0 < δ) :
    gradientPairSum m (triangularFold δ ∘ f) g =ᵐ[m] gradientPairSum m f g := by
  let f' := hf.1.aestronglyMeasurable.mk f
  have he : f =ᵐ[m] f' := hf.1.aestronglyMeasurable.ae_eq_mk
  have H := gradientPairSum_fold_left_of_measurable hfinite ((sobolev_congr_ae he).mp hf) hg
    hf.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable hδ
  exact (gradientPairSum_congr_ae (he.fun_comp (triangularFold δ)) EventuallyEq.rfl).trans
    (H.trans (gradientPairSum_congr_ae he EventuallyEq.rfl).symm)

lemma gradientPairSum_fold (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {δ : ℝ} (hδ : 0 < δ) :
    gradientPairSum m (triangularFold δ ∘ f) (triangularFold δ ∘ g) =ᵐ[m]
      gradientPairSum m f g := by
  have hG := hg.normalContraction hfinite (triangularFold_lipschitz δ) (triangularFold_zero δ)
  exact (gradientPairSum_fold_left hfinite hf hG hδ).trans
    ((gradientPairSum_symm f (triangularFold δ ∘ g)).trans
    ((gradientPairSum_fold_left hfinite hg hf hδ).trans (gradientPairSum_symm g f)))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_WeightedParallelogramIntegral
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
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weighted_parallelogram_of_integral (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {η ξ : X → ℝ}
    (hη : LocalSobolev m η) (hξ : LocalSobolev m ξ)
    (hei : ∀ x, η x * ξ x = 1) (hη0 : ∀ᵐ x ∂m, 0 ≤ η x) (hξ0 : ∀ᵐ x ∂m, 0 ≤ ξ x)
    {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hηA : ∀ᵐ x ∂m, |η x| ≤ A) (hDη : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (hξC : ∀ᵐ x ∂m, |ξ x| ≤ C) (hDξ : ∀ᵐ x ∂m, |weakGradient m ξ x| ≤ D) :
    (∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
      (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m) =
    2*(∫ x, (weakGradient m f x*η x)^2 ∂m) + 2*(∫ x, (weakGradient m g x*η x)^2 ∂m) := by
  let fs (n : ℕ) := triangularFold (1/((n:ℝ)+1)) ∘ f
  let gs (n : ℕ) := triangularFold (1/((n:ℝ)+1)) ∘ g
  have hfs (n : ℕ) : Sobolev m (fs n) :=
    hf.normalContraction hfinite (triangularFold_lipschitz _) (triangularFold_zero _)
  have hgs (n : ℕ) : Sobolev m (gs n) :=
    hg.normalContraction hfinite (triangularFold_lipschitz _) (triangularFold_zero _)
  have hef (n : ℕ) : weakGradient m (fs n) =ᵐ[m] weakGradient m f :=
    weakGradient_triangularFold hfinite hf (by positivity)
  have heg (n : ℕ) : weakGradient m (gs n) =ᵐ[m] weakGradient m g :=
    weakGradient_triangularFold hfinite hg (by positivity)
  have hft : Tendsto (fun n => (hfs n).1.toLp (fs n)) atTop (𝓝 0) := triangularFold_tendsto_toLp hf.1
  have hgt : Tendsto (fun n => (hgs n).1.toLp (gs n)) atTop (𝓝 0) := triangularFold_tendsto_toLp hg.1
  have hplus (n : ℕ) := (hfs n).add hfinite (hgs n)
  have hminus (n : ℕ) := (hfs n).sub hfinite (hgs n)
  have hpt : Tendsto (fun n => (hplus n).1.toLp (fun x => fs n x+gs n x)) atTop (𝓝 0) := by
    have he (n : ℕ) : (hplus n).1.toLp (fun x => fs n x+gs n x) =
        (hfs n).1.toLp (fs n) + (hgs n).1.toLp (gs n) := MemLp.toLp_add (hfs n).1 (hgs n).1
    simpa only [he,zero_add] using hft.add hgt
  have hmt : Tendsto (fun n => (hminus n).1.toLp (fun x => fs n x-gs n x)) atTop (𝓝 0) := by
    have he (n : ℕ) : (hminus n).1.toLp (fun x => fs n x-gs n x) =
        (hfs n).1.toLp (fs n) - (hgs n).1.toLp (gs n) := MemLp.toLp_sub (hfs n).1 (hgs n).1
    simpa only [he,sub_zero] using hft.sub hgt
  have hrf (n : ℕ) : ‖(hfs n).2.2.toLp (weakGradient m (fs n))‖ ≤
      ‖hf.2.2.toLp (weakGradient m f)‖ := by
    have H : (hfs n).2.2.toLp (weakGradient m (fs n)) = hf.2.2.toLp (weakGradient m f) :=
      Lp.ext ((hfs n).2.2.coeFn_toLp.trans ((hef n).trans hf.2.2.coeFn_toLp.symm))
    rw [H]
  have hrg (n : ℕ) : ‖(hgs n).2.2.toLp (weakGradient m (gs n))‖ ≤
      ‖hg.2.2.toLp (weakGradient m g)‖ := by
    have H : (hgs n).2.2.toLp (weakGradient m (gs n)) = hg.2.2.toLp (weakGradient m g) :=
      Lp.ext ((hgs n).2.2.coeFn_toLp.trans ((heg n).trans hg.2.2.coeFn_toLp.symm))
    rw [H]
  let R := ‖(hf.2.2.add hg.2.2).toLp (fun x => weakGradient m f x+weakGradient m g x)‖
  have hbound {u : X → ℝ} (hu : Sobolev m u)
      (he : ∀ᵐ x ∂m, weakGradient m u x ≤ weakGradient m f x+weakGradient m g x) :
      ‖hu.2.2.toLp (weakGradient m u)‖ ≤ R := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu.2.2.coeFn_toLp,(hf.2.2.add hg.2.2).coeFn_toLp,
      (weakGradient_isMinimal hu.2.1.2).1.2.1, he] with x h1 h2 h0 hx
    change ‖(hu.2.2.toLp (weakGradient m u)) x‖ ≤
      ‖((hf.2.2.add hg.2.2).toLp (weakGradient m f + weakGradient m g)) x‖
    simpa only [h1,h2,Real.norm_eq_abs,abs_of_nonneg h0,Pi.add_apply] using hx.trans (le_abs_self _)
  have hrp (n : ℕ) : ‖(hplus n).2.2.toLp (weakGradient m (fun x => fs n x+gs n x))‖ ≤ R := by
    apply hbound (hplus n)
    filter_upwards [weakGradient_add_le hfinite (hfs n).2.1 (hgs n).2.1,hef n,heg n] with x hx hf' hg'
    simpa only [hf',hg'] using hx
  have hrm (n : ℕ) : ‖(hminus n).2.2.toLp (weakGradient m (fun x => fs n x-gs n x))‖ ≤ R := by
    apply hbound (hminus n)
    filter_upwards [weakGradient_add_le hfinite (hfs n).2.1 ((hgs n).neg).2.1,hef n,heg n,
      weakGradient_const_mul (m := m) (-1) (gs n)] with x hx hf' hg' hn
    simp only [neg_one_mul,abs_neg,abs_one,one_mul] at hn
    simpa only [← sub_eq_add_neg,hn,hf',hg'] using hx
  let e (u : X → ℝ) := (∫ x, (weakGradient m (fun y => u y*η y) x)^2 ∂m) -
    ∫ x, (weakGradient m u x*η x)^2 ∂m
  have ht (us : ℕ → X → ℝ) (hs : ∀ n, Sobolev m (us n)) {R : ℝ}
      (hR : ∀ n, ‖(hs n).2.2.toLp (weakGradient m (us n))‖ ≤ R)
      (hT : Tendsto (fun n => (hs n).1.toLp (us n)) atTop (𝓝 0)) :
      Tendsto (fun n => e (us n)) atTop (𝓝 0) :=
    tendsto_gradient_mul_error hfinite hs hη hξ hei hη0 hξ0 hA hB hD hηA hDη hξC hDξ hR hT
  have hT := ((ht _ hplus hrp hpt).add (ht _ hminus hrm hmt)).sub
    (((ht _ hfs hrf hft).const_mul 2).add ((ht _ hgs hrg hgt).const_mul 2))
  have hpair (n : ℕ) :
      (∫ x, (weakGradient m (fun y => fs n y+gs n y) x*η x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => fs n y-gs n y) x*η x)^2 ∂m) =
      (∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m) := by
    rw [← integral_add (memLp_mul_bounded (hplus n).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq
        (memLp_mul_bounded (hminus n).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq,
      ← integral_add (memLp_mul_bounded (hf.add hfinite hg).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq
        (memLp_mul_bounded (hf.sub hfinite hg).2.2 hη.1.aestronglyMeasurable hηA).integrable_sq]
    apply integral_congr_ae
    filter_upwards [gradientPairSum_fold (m := m) hfinite hf hg (δ := 1/((n:ℝ)+1)) (by positivity)] with x hx
    change weakGradient m (fun y => fs n y+gs n y) x^2 +
      weakGradient m (fun y => fs n y-gs n y) x^2 =
      weakGradient m (fun y => f y+g y) x^2 + weakGradient m (fun y => f y-g y) x^2 at hx
    calc
      _ = (weakGradient m (fun y => fs n y+gs n y) x^2 +
        weakGradient m (fun y => fs n y-gs n y) x^2)*(η x)^2 := by ring
      _ = _ := congrArg (fun a : ℝ => a*(η x)^2) hx
      _ = _ := by ring
  have hefs (n : ℕ) : (∫ x, (weakGradient m (fs n) x*η x)^2 ∂m) =
      ∫ x, (weakGradient m f x*η x)^2 ∂m :=
    integral_congr_ae ((hef n).mono fun x hx => congrArg (fun a : ℝ => (a*η x)^2) hx)
  have hegs (n : ℕ) : (∫ x, (weakGradient m (gs n) x*η x)^2 ∂m) =
      ∫ x, (weakGradient m g x*η x)^2 ∂m :=
    integral_congr_ae ((heg n).mono fun x hx => congrArg (fun a : ℝ => (a*η x)^2) hx)
  let v := 2*(∫ x, (weakGradient m f x*η x)^2 ∂m) + 2*(∫ x, (weakGradient m g x*η x)^2 ∂m) -
      ((∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m))
  have heq (n : ℕ) : e (fun x => fs n x+gs n x) + e (fun x => fs n x-gs n x) -
      (2*e (fs n)+2*e (gs n)) = v := by
    have H := hpar (fun x => fs n x*η x) (fun x => gs n x*η x)
      ((hfs n).mul_bounded hfinite hη hηA hDη) ((hgs n).mul_bounded hfinite hη hηA hDη)
    have hp : (fun y => (fs n y+gs n y)*η y) = (fun y => fs n y*η y+gs n y*η y) := by funext y; ring
    have hm : (fun y => (fs n y-gs n y)*η y) = (fun y => fs n y*η y-gs n y*η y) := by funext y; ring
    dsimp only [e,v]
    rw [hp,hm,hefs,hegs]
    linarith [hpair n]
  simp only [zero_add,mul_zero,sub_zero,heq] at hT
  have hv : v = 0 := tendsto_nhds_unique tendsto_const_nhds hT
  dsimp only [v] at hv
  linarith
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CompContDiff
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

lemma IsLocalWeakUpperGradient.comp_contDiff {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {B : ℝ}
    (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    IsLocalWeakUpperGradient m (φ ∘ f) (fun x => |deriv φ (f x)| * D x) := by
  have hm : AEMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf).abs
  refine ⟨?_,?_,?_⟩
  · simpa only [mul_comm] using hD.1.mul_bounded hm.aestronglyMeasurable
      (by simpa only [abs_abs] using hB)
  · filter_upwards [hD.2.1] with x hx
    exact mul_nonneg (abs_nonneg _) hx
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_exists_ac_representative hf hπ hb] with γ hγ
    obtain ⟨q,hq,hq0,hq1,heq,hder⟩ := hγ
    have hp := ac_comp_contDiff hq hφ
    have hder' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv (φ ∘ q) t| ≤
          ENNReal.ofReal (|deriv φ (f (evalReal γ t))| * D (evalReal γ t)) *
            metricSpeed γ t := by
      filter_upwards [heq,hder, ae_restrict_of_ae hq.ae_differentiableAt,
        ae_restrict_mem measurableSet_Icc] with t ht hd hqd htm
      have htt : t ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using htm
      rw [deriv_comp t (hφ.differentiable (by simp) (q t)) (hqd htt), abs_mul,
        ENNReal.ofReal_mul (abs_nonneg _), ht,
        ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
      exact mul_le_mul' le_rfl hd
    calc
      ENNReal.ofReal |(φ ∘ f) (γ timeOne) - (φ ∘ f) (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv (φ ∘ q) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hp.integral_deriv_eq_sub]
        simp only [Function.comp_apply, hq0, hq1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (φ ∘ q) t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono_ae (by simpa only [Real.enorm_eq_ofReal_abs] using hder')

lemma IsLocalWeakUpperGradient.exp {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, f x ≤ B) :
    IsLocalWeakUpperGradient m (fun x => Real.exp (f x))
      (fun x => Real.exp (f x) * D x) := by
  have hb : ∀ᵐ x ∂m, |deriv Real.exp (f x)| ≤ Real.exp B := by
    filter_upwards [hB] with x hx
    simp only [Real.deriv_exp, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx
  simpa only [Function.comp_def, Real.deriv_exp, abs_of_pos (Real.exp_pos _)] using
    hD.comp_contDiff hf Real.contDiff_exp hb

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LocalSobolevLipschitz
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
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma localSobolev_of_lipschitz (hfinite : FiniteOnBoundedSets m) {f : X → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) : LocalSobolev m f := by
  refine ⟨?_, (lipschitz_isLocalWeakUpperGradient hfinite hf).exists_minimal
    hf.continuous.aemeasurable hfinite⟩
  intro o R _hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      hfinite (Metric.ball o R) Metric.isBounded_ball⟩
  apply MemLp.of_bound hf.continuous.aestronglyMeasurable.restrict (|f o| + L * R)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs]
  calc
    |f x| ≤ |f o| + |f x - f o| := by
      simpa only [sub_add_cancel] using (abs_add_le (f x - f o) (f o)).trans_eq (add_comm _ _)
    _ ≤ |f o| + L * dist x o := by gcongr; exact hf.dist_le_mul x o
    _ ≤ |f o| + L * R := by gcongr; exact hx.le

lemma weakGradient_zero_off_support {f : X → ℝ} (hf : LocalSobolev m f)
    :
    ∀ᵐ x ∂m, x ∉ tsupport f → weakGradient m f x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0 : ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero, _, isMinimalLocalWeakUpperGradient_const 0⟩
  have heq : ∀ᵐ x ∂m, x ∈ (tsupport f)ᶜ → f x = 0 :=
    ae_of_all _ fun _ hx => image_eq_zero_of_notMem_tsupport hx
  filter_upwards [weakGradient_locality hf hz (isClosed_tsupport f).measurableSet.compl heq,
    weakGradient_const (m := m) 0] with x h₁ h₂ hx
  exact (h₁ hx).trans h₂

lemma sobolev_of_lipschitz_compactSupport (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    Sobolev m f := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  have hfl := localSobolev_of_lipschitz hfinite hf
  refine ⟨hf.continuous.memLp_of_hasCompactSupport hc, hfl, ?_⟩
  let : IsFiniteMeasure (m.restrict (tsupport f)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hc.measure_lt_top (μ := m)⟩
  have hI : MemLp ((tsupport f).indicator (fun _ : X => (L : ℝ))) 2 m :=
    (memLp_indicator_iff_restrict (isClosed_tsupport f).measurableSet).mpr (memLp_const (L : ℝ))
  apply hI.mono (weakGradient_isMinimal hfl.2).1.1.aestronglyMeasurable
  filter_upwards [weakGradient_zero_off_support hfl,
    weakGradient_le_lipschitz hfinite hf, weakGradient_nonneg (m := m) f] with x hz hL hn
  by_cases hx : x ∈ tsupport f
  · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hn,
      abs_of_nonneg L.coe_nonneg] using hL
  · simp only [Set.indicator_of_notMem hx, hz hx, norm_zero, le_rfl]

lemma Sobolev.mul_exp (hfinite : FiniteOnBoundedSets m) {f V : X → ℝ}
    (hf : Sobolev m f) {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hVB : ∀ᵐ x ∂m, V x ≤ B) : Sobolev m (fun x => f x * Real.exp (V x)) := by
  have hVl := localSobolev_of_lipschitz hfinite hV
  have hD := (weakGradient_isMinimal hVl.2).1.exp hV.continuous.aemeasurable hVB
  have hexpB : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B := by
    filter_upwards [hVB] with x hx
    simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  have hel : LocalSobolev m (fun x => Real.exp (V x)) :=
    ⟨locallyL2_of_bounded hfinite (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hexpB),
      hD.exists_minimal (Real.continuous_exp.comp hV.continuous).aemeasurable hfinite⟩
  apply hf.mul_bounded hfinite hel hexpB
  filter_upwards [(weakGradient_isMinimal hel.2).2 _ hD,
    weakGradient_le_lipschitz hfinite hV, hVB,
    weakGradient_nonneg (m := m) (fun x => Real.exp (V x))] with x hx hL hB hn
  rw [abs_of_nonneg hn]
  exact hx.trans ((mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hB) L.coe_nonneg))

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_GradientParallelogramDefect
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gradientParallelogramDefect_integrable (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    Integrable (gradientParallelogramDefect m f g) m :=
  (((hf.add hfinite hg).2.2.integrable_sq.add (hf.sub hfinite hg).2.2.integrable_sq).sub
    (hf.2.2.integrable_sq.const_mul 2)).sub (hg.2.2.integrable_sq.const_mul 2)

lemma integral_gradientParallelogramDefect_mul_sq (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g)
    {η : X → ℝ} (hη : AEStronglyMeasurable η m) {A : ℝ}
    (hA : ∀ᵐ x ∂m, |η x| ≤ A) :
    (∫ x, gradientParallelogramDefect m f g x * (η x)^2 ∂m) =
    ((∫ x, (weakGradient m (fun y => f y+g y) x*η x)^2 ∂m) +
      (∫ x, (weakGradient m (fun y => f y-g y) x*η x)^2 ∂m)) -
    2*(∫ x, (weakGradient m f x*η x)^2 ∂m) - 2*(∫ x, (weakGradient m g x*η x)^2 ∂m) := by
  have hp := (memLp_mul_bounded (hf.add hfinite hg).2.2 hη hA).integrable_sq
  have hm := (memLp_mul_bounded (hf.sub hfinite hg).2.2 hη hA).integrable_sq
  have hf' := (memLp_mul_bounded hf.2.2 hη hA).integrable_sq
  have hg' := (memLp_mul_bounded hg.2.2 hη hA).integrable_sq
  calc
    _ = ∫ x, ((weakGradient m (fun y => f y+g y) x*η x)^2 +
        (weakGradient m (fun y => f y-g y) x*η x)^2) -
        2*(weakGradient m f x*η x)^2 - 2*(weakGradient m g x*η x)^2 ∂m := by
      congr 1
      funext x
      dsimp [gradientParallelogramDefect]
      ring
    _ = _ := by
      have E := integral_sub ((hp.add hm).sub (hf'.const_mul 2)) (hg'.const_mul 2)
      have E₂ := integral_sub (hp.add hm) (hf'.const_mul 2)
      have E₃ := integral_add hp hm
      dsimp only [Pi.add_apply, Pi.sub_apply] at E E₂ E₃
      rw [E, E₂, E₃, integral_const_mul, integral_const_mul]

lemma weighted_parallelogram_defect_zero (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) {η : X → ℝ} {L : ℝ≥0}
    (hη : LipschitzWith L η) (h1 : ∀ x, 1 ≤ η x) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ x, |η x| ≤ A) :
    (∫ x, gradientParallelogramDefect m f g x * (η x)^2 ∂m) = 0 := by
  have hξ := lipschitz_inv_of_one_le hη h1
  have h0 (x : X) : 0 < η x := lt_of_lt_of_le zero_lt_one (h1 x)
  have H := weighted_parallelogram_of_integral hfinite hpar hf hg
    (localSobolev_of_lipschitz hfinite hη) (localSobolev_of_lipschitz hfinite hξ)
    (fun x => mul_inv_cancel₀ (h0 x).ne')
    (ae_of_all _ fun x => (h0 x).le) (ae_of_all _ fun x => inv_nonneg.mpr (h0 x).le)
    hA L.coe_nonneg L.coe_nonneg (ae_of_all _ hbound)
    (by filter_upwards [weakGradient_le_lipschitz hfinite hη, weakGradient_nonneg (m := m) η] with x hL hn
        rwa [abs_of_nonneg hn])
    (C := 1) (ae_of_all _ fun x => by
      rw [abs_of_nonneg (inv_nonneg.mpr (h0 x).le)]
      exact (inv_le_one₀ (h0 x)).mpr (h1 x))
    (by filter_upwards [weakGradient_le_lipschitz hfinite hξ,
          weakGradient_nonneg (m := m) (fun x => (η x)⁻¹)] with x hL hn
        rwa [abs_of_nonneg hn])
  rw [integral_gradientParallelogramDefect_mul_sq hfinite hf hg hη.continuous.aestronglyMeasurable
    (ae_of_all _ hbound)]
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_LocalGradientParallelogram
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocalSobolev.neg {f : X → ℝ} (hf : LocalSobolev m f) :
    LocalSobolev m (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

lemma LocalSobolev.sub (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) : LocalSobolev m (fun x => f x-g x) :=
  hf.add hfinite hg.neg

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma weakGradient_neg (f : X → ℝ) : weakGradient m (fun x => -f x) =ᵐ[m] weakGradient m f := by
  simpa only [neg_one_mul,abs_neg,abs_one,one_mul] using weakGradient_const_mul (m := m) (-1) f

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gamma_comm (f g : X → ℝ) : gamma m f g =ᵐ[m] gamma m g f := by
  have ep : (fun x => f x+g x) = (fun x => g x+f x) := by funext x; ring
  have em : (fun x => g x-f x) = (fun x => -(f x-g x)) := by funext x; ring
  filter_upwards [weakGradient_neg (m := m) (fun x => f x-g x)] with x hx
  simp only [gamma,ep,em,hx]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma gamma_zero_left (g : X → ℝ) : gamma m (fun _ => (0:ℝ)) g =ᵐ[m] 0 := by
  filter_upwards [weakGradient_neg (m := m) g] with x hx
  simp only [gamma,zero_add,zero_sub,hx,sub_self,zero_div,Pi.zero_apply]

lemma gamma_add_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m (fun x => f x+g x) h =ᵐ[m] (fun x => gamma m f h x+gamma m g h x) := by
  filter_upwards [hpar _ _ (hf.add hfinite hh) hg, hpar _ _ (hf.sub hfinite hh) hg,
    hpar _ _ (hg.add hfinite hh) hf,hpar _ _ (hg.sub hfinite hh) hf,
    weakGradient_neg (m := m) (fun x => f x-g x-h x),
    weakGradient_neg (m := m) (fun x => f x-g x+h x)] with x h₁ h₂ h₃ h₄ hn₁ hn₂
  exact polar_add_of_four_parallelograms (fun u : X → ℝ => (weakGradient m u x)^2)
    f g h h₁ h₂ h₃ h₄ (congrArg (fun a : ℝ => a^2) hn₁) (congrArg (fun a : ℝ => a^2) hn₂)

lemma gamma_add_right (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m f (fun x => g x+h x) =ᵐ[m] (fun x => gamma m f g x+gamma m f h x) := by
  filter_upwards [gamma_add_left hfinite hpar hg hh hf,gamma_comm (m := m) f (fun x => g x+h x),
    gamma_comm (m := m) g f,gamma_comm (m := m) h f] with x hx h1 h2 h3
  rw [h1,hx,h2,h3]

lemma gamma_neg_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    gamma m (fun x => -f x) g =ᵐ[m] (fun x => -gamma m f g x) := by
  filter_upwards [gamma_add_left hfinite hpar hf hf.neg hg,gamma_zero_left (m := m) g] with x hx h0
  simp only [add_neg_cancel] at hx
  change gamma m (fun _ => (0:ℝ)) g x = 0 at h0
  linarith

lemma gamma_sub_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g h : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (hh : LocalSobolev m h) :
    gamma m (fun x => f x-g x) h =ᵐ[m] (fun x => gamma m f h x-gamma m g h x) := by
  filter_upwards [gamma_add_left hfinite hpar hf hg.neg hh,gamma_neg_left hfinite hpar hg hh] with x hx hn
  simpa only [hn,← sub_eq_add_neg] using hx

lemma weakGradient_dist_le (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, |weakGradient m f x-weakGradient m g x| ≤ weakGradient m (fun y => f y-g y) x := by
  have e : (fun x => g x-f x) = (fun x => -(f x-g x)) := by funext x; ring
  filter_upwards [weakGradient_add_le hfinite (hf.sub hfinite hg) hg,
    weakGradient_add_le hfinite (hg.sub hfinite hf) hf,
    weakGradient_neg (m := m) (fun x => f x-g x)] with x h₁ h₂ hn
  simp only [sub_add_cancel] at h₁ h₂
  rw [e,hn] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma weakGradient_const_mul_add_tendsto (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {cs : ℕ → ℝ} {c : ℝ} (hc : Tendsto cs atTop (𝓝 c)) :
    ∀ᵐ x ∂m, Tendsto (fun n => weakGradient m (fun y => cs n*f y+g y) x) atTop
      (𝓝 (weakGradient m (fun y => c*f y+g y) x)) := by
  have hdist (n : ℕ) : ∀ᵐ x ∂m,
      dist (weakGradient m (fun y => cs n*f y+g y) x) (weakGradient m (fun y => c*f y+g y) x) ≤
      |cs n-c| * weakGradient m f x := by
    have he : (fun y => (cs n*f y+g y)-(c*f y+g y)) = (fun y => (cs n-c)*f y) := by funext y; ring
    filter_upwards [weakGradient_dist_le hfinite ((hf.const_mul (cs n)).add hfinite hg)
      ((hf.const_mul c).add hfinite hg),weakGradient_const_mul (m := m) (cs n-c) f] with x hx hmul
    simpa only [he,hmul,Real.dist_eq] using hx
  filter_upwards [ae_all_iff.mpr hdist] with x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have H : Tendsto (fun n => |cs n-c| * weakGradient m f x) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_mul] using ((hc.sub (tendsto_const_nhds (x := c))).abs.mul_const (weakGradient m f x))
  exact squeeze_zero (fun n => dist_nonneg) hx H

lemma gamma_const_mul_tendsto (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {cs : ℕ → ℝ} {c : ℝ} (hc : Tendsto cs atTop (𝓝 c)) :
    ∀ᵐ x ∂m, Tendsto (fun n => gamma m (fun y => cs n*f y) g x) atTop
      (𝓝 (gamma m (fun y => c*f y) g x)) := by
  filter_upwards [weakGradient_const_mul_add_tendsto hfinite hf hg hc,
    weakGradient_const_mul_add_tendsto hfinite hf hg.neg hc] with x hp hm
  simpa only [gamma, ← sub_eq_add_neg] using ((hp.pow 2).sub (hm.pow 2)).div_const 4
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GammaNatMulLeft
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_nat_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (n : ℕ) :
    gamma m (fun x => (n:ℝ)*f x) g =ᵐ[m] (fun x => (n:ℝ)*gamma m f g x) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul,Pi.zero_def] using gamma_zero_left (m := m) g
  | succ n ih =>
    have e : (fun x => ((n+1:ℕ):ℝ)*f x) = (fun x => (n:ℝ)*f x+f x) := by
      funext x; push_cast; ring
    filter_upwards [gamma_add_left hfinite hpar (hf.const_mul n) hf hg,ih] with x ha hi
    rw [e,ha,hi]
    push_cast
    ring

lemma gamma_int_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (n : ℤ) :
    gamma m (fun x => (n:ℝ)*f x) g =ᵐ[m] (fun x => (n:ℝ)*gamma m f g x) := by
  obtain ⟨n,rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [Int.cast_natCast] using gamma_nat_mul_left hfinite hpar hf hg n
  · filter_upwards [gamma_nat_mul_left hfinite hpar hf hg n,
      gamma_neg_left hfinite hpar (hf.const_mul n) hg] with x hn hneg
    simpa only [Int.cast_neg,Int.cast_natCast,neg_mul,hn] using hneg

lemma gamma_rat_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (q : ℚ) :
    gamma m (fun x => (q:ℝ)*f x) g =ᵐ[m] (fun x => (q:ℝ)*gamma m f g x) := by
  have hd : (q.den:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have eq : (q.den:ℝ)*(q:ℝ) = (q.num:ℝ) := by
    rw [Rat.cast_def, mul_div_cancel₀ _ hd]
  have e : (fun x => (q.den:ℝ)*((q:ℝ)*f x)) = (fun x => (q.num:ℝ)*f x) := by
    funext x; rw [← mul_assoc,eq]
  filter_upwards [gamma_nat_mul_left hfinite hpar (hf.const_mul q) hg q.den,
    gamma_int_mul_left hfinite hpar hf hg q.num] with x hden hnum
  rw [e,hnum] at hden
  apply mul_left_cancel₀ hd
  rw [← mul_assoc,eq,hden]

lemma gamma_const_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    gamma m (fun x => c*f x) g =ᵐ[m] (fun x => c*gamma m f g x) := by
  obtain ⟨qs,_,_,hqs⟩ := Real.exists_seq_rat_strictMono_tendsto c
  filter_upwards [gamma_const_mul_tendsto hfinite hf hg hqs,
    ae_all_iff.mpr (fun n => gamma_rat_mul_left hfinite hpar hf hg (qs n))] with x ht he
  apply tendsto_nhds_unique ht
  exact (hqs.mul_const (gamma m f g x)).congr (fun n => (he n).symm)

lemma gamma_const_mul_right (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    gamma m f (fun x => c*g x) =ᵐ[m] (fun x => c*gamma m f g x) := by
  filter_upwards [gamma_const_mul_left hfinite hpar hg hf c,
    gamma_comm (m := m) f (fun x => c*g x),gamma_comm (m := m) g f] with x hc h1 h2
  rw [h1,hc,h2]

lemma weakGradient_linear_combination_sq (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+c*g y) x)^2 =
      (weakGradient m f x)^2 + 2*c*gamma m f g x + c^2*(weakGradient m g x)^2 := by
  have hc := hg.const_mul c
  have hs := hf.add hfinite hc
  filter_upwards [gamma_self (m := m) (fun y => f y+c*g y),
    gamma_add_left hfinite hpar hf hc hs,
    gamma_add_right hfinite hpar hf hf hc,
    gamma_add_right hfinite hpar hc hf hc,
    gamma_const_mul_left hfinite hpar hg hf c,
    gamma_const_mul_left hfinite hpar hg hc c,
    gamma_const_mul_right hfinite hpar hf hg c,
    gamma_const_mul_right hfinite hpar hg hg c,
    gamma_self (m := m) f,gamma_self (m := m) g,gamma_comm (m := m) g f]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [← h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
  ring


lemma gamma_sq_le (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, (gamma m f g x)^2 ≤ (weakGradient m f x)^2 * (weakGradient m g x)^2 := by
  filter_upwards [ae_all_iff.mpr (fun q : ℚ =>
    weakGradient_linear_combination_sq hfinite hpar hf hg (q:ℝ))] with x hx
  have hn (c : ℝ) : 0 ≤ (weakGradient m g x)^2*(c*c) + (2*gamma m f g x)*c +
      (weakGradient m f x)^2 := by
    obtain ⟨qs,_,_,ht⟩ := Real.exists_seq_rat_strictMono_tendsto c
    have hq (n : ℕ) : 0 ≤ (weakGradient m g x)^2*((qs n:ℝ)*(qs n:ℝ)) +
        (2*gamma m f g x)*(qs n:ℝ) + (weakGradient m f x)^2 := by
      have H := sq_nonneg (weakGradient m (fun y => f y+(qs n:ℝ)*g y) x)
      rw [hx (qs n)] at H
      nlinarith
    have ht' : Tendsto (fun n => (weakGradient m g x)^2*((qs n:ℝ)*(qs n:ℝ)) +
        (2*gamma m f g x)*(qs n:ℝ) + (weakGradient m f x)^2) atTop
      (𝓝 ((weakGradient m g x)^2*(c*c) + (2*gamma m f g x)*c + (weakGradient m f x)^2)) :=
      (((ht.mul ht).const_mul _).add (ht.const_mul _)).add_const _
    exact ge_of_tendsto ht' (Eventually.of_forall hq)
  have H := discrim_le_zero hn
  dsimp only [discrim] at H
  nlinarith

lemma abs_gamma_le (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, |gamma m f g x| ≤ weakGradient m f x * weakGradient m g x := by
  filter_upwards [gamma_sq_le hfinite hpar hf hg,weakGradient_nonneg (m := m) f,
    weakGradient_nonneg (m := m) g] with x h hn hm
  have hp : 0 ≤ weakGradient m f x*weakGradient m g x := mul_nonneg hn hm
  have he : (gamma m f g x)^2 ≤ (weakGradient m f x*weakGradient m g x)^2 := by
    nlinarith only [h]
  exact (sq_le_sq₀ (abs_nonneg _) hp).mp (by simpa only [sq_abs] using he)

lemma integrable_gamma (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) : Integrable (gamma m f g) m := by
  exact (((hf.add hfinite hg).2.2.integrable_sq).sub
    ((hf.sub hfinite hg).2.2.integrable_sq)).div_const 4
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

lemma weakGradient_pointwise_parallelogram (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+g y) x)^2 +
      (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2 := by
  have H := ae_eq_zero_of_integral_positive_lipschitz_sq
    (gradientParallelogramDefect_integrable hfinite hf hg)
    (fun η _L hL h1 _A hA hb => weighted_parallelogram_defect_zero hfinite hpar hf hg hL h1 hA hb)
  filter_upwards [H] with x hx
  change gradientParallelogramDefect m f g x = 0 at hx
  dsimp only [gradientParallelogramDefect] at hx
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_MulBounded
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

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma LocalSobolev.mul_bounded (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : LocalSobolev m f) (hη : LocalSobolev m η) {A B : ℝ}
    (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    LocalSobolev m (fun x => f x*η x) := by
  apply (localSobolev_iff_exists_upperGradient hfinite).mpr
  exact ⟨hf.1.mul_bounded hη.1.aestronglyMeasurable hA, _,
    (weakGradient_isMinimal hf.2).1.mul_bounded (weakGradient_isMinimal hη.2).1
      hf.1 hη.1.aemeasurable hA hB⟩

lemma LocalSobolev.sobolev_of_zero_outside_ball {f : X → ℝ} (hf : LocalSobolev m f)
    {o : X} {R : ℝ} (hR : 0 < R) (hz : ∀ᵐ x ∂m, x ∉ Metric.ball o R → f x = 0) :
    Sobolev m f := by
  refine ⟨hf.1.memLp_of_zero_outside_ball hR hz,hf,?_⟩
  apply (weakGradient_isMinimal hf.2).1.1.memLp_of_zero_outside_ball hR
  have hc : LocalSobolev m (fun _ : X => (0 : ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero, _, isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [weakGradient_locality hf hc measurableSet_ball.compl hz,
    weakGradient_const (m := m) 0] with x hx h0 hmem
  exact (hx hmem).trans h0

lemma LocalSobolev.sobolev_of_compactSupport [Nonempty X] {f : X → ℝ}
    (hf : LocalSobolev m f) (hc : HasCompactSupport f) : Sobolev m f := by
  let o : X := Classical.arbitrary X
  obtain ⟨R,hR,hsub⟩ := hc.isBounded.subset_ball_lt 0 o
  apply hf.sobolev_of_zero_outside_ball hR
  exact ae_of_all _ fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))

lemma LocalSobolev.mul_lipschitz_compactSupport [Nonempty X]
    (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : LocalSobolev m f) {L : ℝ≥0} (hη : LipschitzWith L η) (hc : HasCompactSupport η) :
    Sobolev m (fun x => f x*η x) := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hη.continuous
  apply LocalSobolev.sobolev_of_compactSupport ?_
    (hc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right)
  apply hf.mul_bounded hfinite (localSobolev_of_lipschitz hfinite hη)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hA x)
  filter_upwards [weakGradient_nonneg (m := m) η, weakGradient_le_lipschitz hfinite hη] with x hn hL
  rwa [abs_of_nonneg hn]

lemma weakGradient_local_pointwise_parallelogram [ProperSpace X] [Nonempty X]
    (hfinite : FiniteOnBoundedSets m)
    (hpar : ∀ u v : X → ℝ, Sobolev m u → Sobolev m v →
      (∫ x, (weakGradient m (fun y => u y+v y) x)^2 ∂m) +
        (∫ x, (weakGradient m (fun y => u y-v y) x)^2 ∂m) =
      2*(∫ x, (weakGradient m u x)^2 ∂m) + 2*(∫ x, (weakGradient m v x)^2 ∂m))
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+g y) x)^2 +
      (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2 := by
  let o : X := Classical.arbitrary X
  have hloc (n : ℕ) : ∀ᵐ x ∂m, x ∈ Metric.closedBall o n →
      (weakGradient m (fun y => f y+g y) x)^2 +
        (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2 := by
    let η : X → ℝ := fun x => thickenedIndicator zero_lt_one (Metric.closedBall o (n:ℝ)) x
    have hη : LipschitzWith (1 : ℝ≥0) η := by
      simpa only [Real.toNNReal_one,inv_one] using
        (WeakHessianCalculus.lipschitz_thickenedIndicator (s := Metric.closedBall o (n:ℝ)) zero_lt_one)
    have hηc : HasCompactSupport η :=
      WeakHessianCalculus.compact_thickenedIndicator (isCompact_closedBall o (n:ℝ)) zero_lt_one
    have hη1 {x : X} (hx : x ∈ Metric.closedBall o (n:ℝ)) : η x = 1 := by
      simp only [η,thickenedIndicator_one zero_lt_one _ hx,NNReal.coe_one]
    have hfs := hf.mul_lipschitz_compactSupport hfinite hη hηc
    have hgs := hg.mul_lipschitz_compactSupport hfinite hη hηc
    have hplus : LocalSobolev m (fun x => f x+g x) := hf.add hfinite hg
    have hminus : LocalSobolev m (fun x => f x-g x) := by
      simpa only [neg_one_mul, sub_eq_add_neg] using hf.add hfinite (hg.const_mul (-1))
    have hl {u v : X → ℝ} (hu : LocalSobolev m u) (hv : LocalSobolev m v)
        (he : ∀ x ∈ Metric.closedBall o (n:ℝ), u x = v x) :
        ∀ᵐ x ∂m, x ∈ Metric.closedBall o (n:ℝ) → weakGradient m u x = weakGradient m v x :=
      weakGradient_locality hu hv measurableSet_closedBall (ae_of_all _ he)
    filter_upwards [weakGradient_pointwise_parallelogram hfinite hpar hfs hgs,
      hl hfs.2.1 hf (fun x hx => by simp only [hη1 hx,mul_one]),
      hl hgs.2.1 hg (fun x hx => by simp only [hη1 hx,mul_one]),
      hl (hfs.add hfinite hgs).2.1 hplus (fun x hx => by simp only [hη1 hx,mul_one]),
      hl (hfs.sub hfinite hgs).2.1 hminus (fun x hx => by simp only [hη1 hx,mul_one])]
      with x hp hfx hgx hpx hmx hx
    simpa only [hfx hx,hgx hx,hpx hx,hmx hx] using hp
  filter_upwards [ae_all_iff.mpr hloc] with x hx
  obtain ⟨n,hn⟩ := exists_nat_ge (dist x o)
  exact hx n hn
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GammaAddConstLeft
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_add_const_left (hfinite : FiniteOnBoundedSets m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (a : ℝ) :
    gamma m (fun x => f x+a) g =ᵐ[m] gamma m f g := by
  have ep : (fun x => f x+a+g x) = (fun x => (f x+g x)+a) := by funext x; ring
  have em : (fun x => f x+a-g x) = (fun x => (f x-g x)+a) := by funext x; ring
  filter_upwards [weakGradient_add_const_of_exists (hf.add hfinite hg).2 a,
    weakGradient_add_const_of_exists (hf.sub hfinite hg).2 a] with x hp hm
  simp only [gamma,ep,em,hp,hm]

lemma weakGradient_mul_le_local (hfinite : FiniteOnBoundedSets m) {f η : X → ℝ}
    (hf : LocalSobolev m f) (hη : LocalSobolev m η) {A B : ℝ}
    (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (fun y => f y*η y) x ≤
      |η x| *weakGradient m f x + |f x| *weakGradient m η x :=
  (weakGradient_isMinimal (hf.mul_bounded hfinite hη hA hB).2).2 _
    ((weakGradient_isMinimal hf.2).1.mul_bounded (weakGradient_isMinimal hη.2).1
      hf.1 hη.1.aemeasurable hA hB)

lemma gamma_product_residual (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f η g : X → ℝ} (hf : LocalSobolev m f) (hη : LocalSobolev m η) (hg : LocalSobolev m g)
    {A B : ℝ} (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B)
    (a b : ℝ) :
    ∀ᵐ x ∂m, |gamma m (fun y => f y*η y) g x - b*gamma m f g x - a*gamma m η g x| ≤
      (|η x-b| *weakGradient m f x + |f x-a| *weakGradient m η x)*weakGradient m g x := by
  let u : X → ℝ := fun x => f x-a
  let v : X → ℝ := fun x => η x-b
  have hu : LocalSobolev m u := hf.add_const hfinite (-a)
  have hv : LocalSobolev m v := hη.add_const hfinite (-b)
  have hvA : ∀ᵐ x ∂m, |v x| ≤ A+|b| := by
    filter_upwards [hA] with x hx
    exact (abs_sub (η x) b).trans (add_le_add hx le_rfl)
  have hDf : weakGradient m u =ᵐ[m] weakGradient m f := weakGradient_add_const_of_exists hf.2 (-a)
  have hDη : weakGradient m v =ᵐ[m] weakGradient m η := weakGradient_add_const_of_exists hη.2 (-b)
  have hvB : ∀ᵐ x ∂m, |weakGradient m v x| ≤ B := by
    filter_upwards [hB,hDη] with x hx he; simpa only [he] using hx
  have hp := hf.mul_bounded hfinite hη hA hB
  have hres := hu.mul_bounded hfinite hv hvA hvB
  have hs₁ := hp.sub hfinite (hf.const_mul b)
  have hs₂ := hs₁.sub hfinite (hη.const_mul a)
  have e : (fun x => u x*v x) = (fun x => (f x*η x-b*f x-a*η x)+a*b) := by
    funext x; dsimp only [u,v]; ring
  filter_upwards [abs_gamma_le hfinite hpar hres hg,
    weakGradient_mul_le_local hfinite hu hv hvA hvB,hDf,hDη,
    gamma_add_const_left hfinite hs₂ hg (a*b),
    gamma_sub_left hfinite hpar hs₁ (hη.const_mul a) hg,
    gamma_sub_left hfinite hpar hp (hf.const_mul b) hg,
    gamma_const_mul_left hfinite hpar hf hg b,
    gamma_const_mul_left hfinite hpar hη hg a,
    weakGradient_nonneg (m := m) g] with x hab hd hdf hdη he hs2 hs1 hb ha hng
  rw [e,he,hs2,hs1,hb,ha] at hab
  rw [hdf,hdη,e] at hd
  exact hab.trans (mul_le_mul_of_nonneg_right hd hng)

lemma gamma_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f η g : X → ℝ} (hf : LocalSobolev m f) (hη : LocalSobolev m η) (hg : LocalSobolev m g)
    {A B : ℝ} (hA : ∀ᵐ x ∂m, |η x| ≤ A) (hB : ∀ᵐ x ∂m, |weakGradient m η x| ≤ B) :
    gamma m (fun y => f y*η y) g =ᵐ[m]
      (fun x => f x*gamma m η g x + η x*gamma m f g x) := by
  filter_upwards [ae_all_iff.mpr (fun a : ℚ => ae_all_iff.mpr
    (fun b : ℚ => gamma_product_residual hfinite hpar hf hη hg hA hB (a:ℝ) (b:ℝ)))] with x hx
  obtain ⟨qa,_,_,has⟩ := Real.exists_seq_rat_strictMono_tendsto (f x)
  obtain ⟨qb,_,_,hbs⟩ := Real.exists_seq_rat_strictMono_tendsto (η x)
  have H : |gamma m (fun y => f y*η y) g x - η x*gamma m f g x - f x*gamma m η g x| ≤ (0:ℝ) := by
    have hl := (((tendsto_const_nhds (x := gamma m (fun y => f y*η y) g x)).sub (hbs.mul_const (gamma m f g x))).sub
      (has.mul_const (gamma m η g x))).abs
    have hr := ((((tendsto_const_nhds (x := η x)).sub hbs).abs.mul_const (weakGradient m f x)).add
      (((tendsto_const_nhds (x := f x)).sub has).abs.mul_const (weakGradient m η x))).mul_const (weakGradient m g x)
    have hr0 : Tendsto (fun n => (|η x-(qb n:ℝ)| *weakGradient m f x +
        |f x-(qa n:ℝ)| *weakGradient m η x)*weakGradient m g x) atTop (𝓝 (0:ℝ)) := by
      simpa only [sub_self,abs_zero,zero_mul,zero_add] using hr
    exact le_of_tendsto_of_tendsto hl hr0 (Eventually.of_forall fun n => hx (qa n) (qb n))
  have he : gamma m (fun y => f y*η y) g x - η x*gamma m f g x - f x*gamma m η g x = 0 :=
    abs_nonpos_iff.mp H
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CompContDiff2
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma LocalSobolev.comp_contDiff (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hfφ : LocallyL2 m (φ ∘ f)) {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    LocalSobolev m (φ ∘ f) := by
  apply (localSobolev_iff_exists_upperGradient hfinite).mpr
  exact ⟨hfφ,_,(weakGradient_isMinimal hf.2).1.comp_contDiff hf.1.aemeasurable hφ hB⟩

lemma weakGradient_comp_contDiff_le (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : LocalSobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hfφ : LocallyL2 m (φ ∘ f)) {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    ∀ᵐ x ∂m, weakGradient m (φ ∘ f) x ≤ |deriv φ (f x)| *weakGradient m f x :=
  (weakGradient_isMinimal (hf.comp_contDiff hfinite hφ hfφ hB).2).2 _
    ((weakGradient_isMinimal hf.2).1.comp_contDiff hf.1.aemeasurable hφ hB)

lemma gamma_chain_residual (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hfφ : LocallyL2 m (φ ∘ f))
    {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) (c : ℝ) :
    ∀ᵐ x ∂m, |gamma m (φ ∘ f) g x-c*gamma m f g x| ≤
      |deriv φ (f x)-c| *weakGradient m f x*weakGradient m g x := by
  let ψ : ℝ → ℝ := fun s => φ s-c*s
  have hψ : ContDiff ℝ 1 ψ := hφ.sub (contDiff_const.mul contDiff_id)
  have hdψ (s : ℝ) : deriv ψ s = deriv φ s-c := by
    simpa only [Pi.sub_def,id_eq,ψ,one_mul,mul_one] using
      ((hφ.differentiable (by simp) s).hasDerivAt.sub ((hasDerivAt_id s).const_mul c)).deriv
  have hbψ : ∀ᵐ x ∂m, |deriv ψ (f x)| ≤ B+|c| := by
    filter_upwards [hB] with x hx
    rw [hdψ]
    exact (abs_sub _ _).trans (add_le_add hx le_rfl)
  have hφs := hf.comp_contDiff hfinite hφ hfφ hB
  have hψL : LocallyL2 m (ψ ∘ f) := fun o R hR => (hfφ o R hR).sub ((hf.1 o R hR).const_mul c)
  have hψs := hf.comp_contDiff hfinite hψ hψL hbψ
  filter_upwards [abs_gamma_le hfinite hpar hψs hg,
    weakGradient_comp_contDiff_le hfinite hf hψ hψL hbψ,
    gamma_sub_left hfinite hpar hφs (hf.const_mul c) hg,
    gamma_const_mul_left hfinite hpar hf hg c,
    weakGradient_nonneg (m := m) g] with x hc hd hs hm hng
  change |gamma m (fun y => φ (f y)-c*f y) g x| ≤ _ at hc
  dsimp only [Function.comp_apply] at hs
  rw [hs,hm] at hc
  rw [hdψ] at hd
  exact hc.trans (mul_le_mul_of_nonneg_right hd hng)

lemma gamma_comp_contDiff (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hfφ : LocallyL2 m (φ ∘ f))
    {B : ℝ} (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    gamma m (φ ∘ f) g =ᵐ[m] (fun x => deriv φ (f x)*gamma m f g x) := by
  filter_upwards [ae_all_iff.mpr (fun q : ℚ =>
    gamma_chain_residual hfinite hpar hf hg hφ hfφ hB q)] with x hx
  obtain ⟨qs,_,_,ht⟩ := Real.exists_seq_rat_strictMono_tendsto (deriv φ (f x))
  have hl := ((tendsto_const_nhds (x := gamma m (φ ∘ f) g x)).sub
    (ht.mul_const (gamma m f g x))).abs
  have hr := (((tendsto_const_nhds (x := deriv φ (f x))).sub ht).abs.mul_const
    (weakGradient m f x)).mul_const (weakGradient m g x)
  have hr0 : Tendsto (fun n => |deriv φ (f x)-(qs n:ℝ)| *weakGradient m f x*weakGradient m g x)
      atTop (𝓝 (0:ℝ)) := by simpa only [sub_self,abs_zero,zero_mul] using hr
  have he : |gamma m (φ ∘ f) g x - deriv φ (f x)*gamma m f g x| ≤ 0 :=
    le_of_tendsto_of_tendsto hl hr0 (Eventually.of_forall fun n => hx (qs n))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)


lemma LocalSobolev.exp_bounded (hfinite : FiniteOnBoundedSets m) {V : X → ℝ}
    (hV : LocalSobolev m V) {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) :
    LocalSobolev m (fun x => Real.exp (V x)) := by
  apply hV.comp_contDiff hfinite Real.contDiff_exp
  · apply locallyL2_of_bounded hfinite (Real.continuous_exp.comp_aestronglyMeasurable hV.1.aestronglyMeasurable)
    filter_upwards [hB] with x hx
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  · filter_upwards [hB] with x hx
    simpa only [Real.deriv_exp,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx

lemma gamma_exp_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V f : X → ℝ} (hV : LocalSobolev m V) (hf : LocalSobolev m f)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) :
    gamma m (fun x => Real.exp (V x)) f =ᵐ[m]
      (fun x => Real.exp (V x)*gamma m V f x) := by
  have hb : ∀ᵐ x ∂m, |deriv Real.exp (V x)| ≤ Real.exp B := by
    filter_upwards [hB] with x hx
    simpa only [Real.deriv_exp,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  simpa only [Function.comp_def,Real.deriv_exp] using
    gamma_comp_contDiff hfinite hpar hV hf Real.contDiff_exp (hV.exp_bounded hfinite hB).1 hb

lemma weakGradient_exp_bound (hfinite : FiniteOnBoundedSets m) {V : X → ℝ}
    (hV : LocalSobolev m V) {B L : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B)
    (hL : ∀ᵐ x ∂m, weakGradient m V x ≤ L) :
    ∀ᵐ x ∂m, |weakGradient m (fun y => Real.exp (V y)) x| ≤ Real.exp B*L := by
  have hd := (weakGradient_isMinimal hV.2).1.exp hV.1.aemeasurable hB
  filter_upwards [(weakGradient_isMinimal (hV.exp_bounded hfinite hB).2).2 _ hd,
    hB,hL,weakGradient_nonneg (m := m) V,
    weakGradient_nonneg (m := m) (fun y => Real.exp (V y))] with x h hx hl hn he
  rw [abs_of_nonneg he]
  exact h.trans (mul_le_mul (Real.exp_le_exp.mpr hx) hl hn (Real.exp_pos B).le)

lemma gamma_mul_exp_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f V g : X → ℝ} (hf : LocalSobolev m f) (hV : LocalSobolev m V) (hg : LocalSobolev m g)
    {B L : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (hL : ∀ᵐ x ∂m, weakGradient m V x ≤ L) :
    gamma m (fun y => f y*Real.exp (V y)) g =ᵐ[m]
      (fun x => Real.exp (V x)*(gamma m f g x+f x*gamma m V g x)) := by
  have hb : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B := by
    filter_upwards [hB] with x hx
    simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  filter_upwards [gamma_mul_left hfinite hpar hf (hV.exp_bounded hfinite hB) hg hb
    (weakGradient_exp_bound hfinite hV hB hL),gamma_exp_left hfinite hpar hV hg hB] with x hm he
  rw [hm,he]
  ring

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GlobalCheegerEnergyWeak
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
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma CurvatureDimension.global_cheegerEnergy_le_weak {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f W : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (W : X → ℝ)) :
    cheegerEnergy m (f : X → ℝ) ≤ ENNReal.ofReal (‖W‖^2/2) := by
  by_cases hm : m = 0
  · have hae : (f : X → ℝ) =ᵐ[m] (fun _ => (0:ℝ)) := by
      subst m
      change ∀ᶠ x in MeasureTheory.ae (0 : Measure X), (f : X → ℝ) x = 0
      rw [MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    rw [cheegerEnergy_congr_ae hae,cheegerEnergy_zero]
    exact bot_le
  obtain ⟨ν,hνp,hνm,hmν,⟨C,hC⟩,hlocal⟩ := exists_probability_reference m o hm hfinite
  let : IsProbabilityMeasure ν := hνp
  let L : ℕ → ℝ≥0 := fun n => ((n:ℝ≥0)+1)⁻¹
  have hφB (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let u : ℕ → Lp ℝ 2 m := fun n => boundedMulLp
    (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all m (hφB n)) f
  have hu : Tendsto u atTop (𝓝 f) := boundedMulLp_tendsto
    (fun n => (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
    (fun n => ae_of_all m (hφB n)) (ae_of_all m (radialCutoff_tendsto o)) f
  have hL : Tendsto (fun n => (L n:ℝ)) atTop (𝓝 0) := by
    simpa only [L,NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,one_div]
      using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb : Tendsto (fun n => ENNReal.ofReal ((‖W‖+(L n:ℝ)*‖f‖)^2/2)) atTop
      (𝓝 (ENNReal.ofReal (‖W‖^2/2))) := by
    have H := (((tendsto_const_nhds (x := ‖W‖)).add (hL.mul_const ‖f‖)).pow 2).div_const 2
    simpa only [zero_mul,add_zero] using ENNReal.tendsto_ofReal H
  change (f, ENNReal.ofReal (‖W‖^2/2)) ∈
    {p : Lp ℝ 2 m × ℝ≥0∞ | cheegerEnergy m (p.1 : X → ℝ) ≤ p.2}
  apply lowerSemicontinuous_cheegerEnergy.isClosed_epigraph.mem_of_tendsto (hu.prodMk_nhds hb)
  apply Eventually.of_forall
  intro n
  obtain ⟨c,hc⟩ := hlocal (tsupport (radialCutoff o n)) (radialCutoff_compact o n).isBounded
  exact hcd.cutoff_cheegerEnergy_le hC hmν hf (radialCutoff_lipschitz o n)
    (radialCutoff_compact o n) (radialCutoff_nonneg o n) (radialCutoff_le_one o n)
    ENNReal.coe_ne_top hc
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GlobalCheegerEnergyMinimal
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
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma CurvatureDimension.global_cheegerEnergy_eq_minimal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D) :
    cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
  have hle := hcd.global_cheegerEnergy_le_weak hfinite o hD.1
  have hch : cheegerEnergy m (f : X → ℝ) < ∞ := lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  obtain ⟨E,hE,henergy⟩ := exists_minimalGradient_energy_le_cheeger
    hfinite (Lp.memLp f) hch
  have heq : E = D := Lp.ext (hE.ae_eq hD)
  rw [heq] at henergy
  exact le_antisymm hle henergy

lemma CurvatureDimension.global_sobolev_iff_cheeger_lt_top {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Sobolev m f ↔ cheegerEnergy m f < ∞ := by
  constructor
  · intro hs
    have hD := (weakGradient_isMinimal hs.2.1.2).1
    have hw := hD.congr_ae hf.coeFn_toLp.symm hs.2.2.coeFn_toLp.symm
    have he := hcd.global_cheegerEnergy_le_weak hfinite o hw
    rw [cheegerEnergy_congr_ae hf.coeFn_toLp] at he
    exact lt_of_le_of_lt he ENNReal.ofReal_lt_top
  · intro hch
    obtain ⟨D,hD,_⟩ := exists_minimalGradient_energy_le_cheeger
      hfinite hf hch
    exact ⟨hf, ⟨fun _ _ _ => hf.restrict _, ⟨D,hD⟩⟩,
      (Lp.memLp D).ae_eq (weakGradient_ae_eq_of_isMinimal hD).symm⟩

lemma CurvatureDimension.global_cheegerEnergy_eq_weakGradient {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal (‖hf.2.2.toLp (weakGradient m f)‖^2/2) := by
  let D := hf.2.2.toLp (weakGradient m f)
  have hD : IsMinimalLocalWeakUpperGradient m (hf.1.toLp f) D := by
    have hm := weakGradient_isMinimal hf.2.1.2
    refine ⟨hm.1.congr_ae hf.1.coeFn_toLp.symm hf.2.2.coeFn_toLp.symm, ?_⟩
    intro E hE
    filter_upwards [hm.2 E (hE.congr_ae hf.1.coeFn_toLp Filter.EventuallyEq.rfl),
      hf.2.2.coeFn_toLp] with x hx hd
    exact hd.trans_le hx
  have he := hcd.global_cheegerEnergy_eq_minimal hfinite o hD
  rwa [cheegerEnergy_congr_ae hf.1.coeFn_toLp] at he

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_SobolevCheegerEnergyTop
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

lemma integral_parallelogram_of_cheeger (hfinite : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂m) +
      (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂m) =
    2*(∫ x, (weakGradient m f x)^2 ∂m) + 2*(∫ x, (weakGradient m g x)^2 ∂m) := by
  have H := h f g (by rw [hID f hf]; exact ENNReal.ofReal_lt_top)
    (by rw [hID g hg]; exact ENNReal.ofReal_lt_top)
  rw [hID _ (hf.add hfinite hg),hID _ (hf.sub hfinite hg),hID f hf,hID g hg] at H
  have Hr := congrArg ENNReal.toReal H
  have hp : 0 ≤ (∫ x, (weakGradient m (fun y => f y+g y) x)^2 ∂m)/2 := by positivity
  have hm : 0 ≤ (∫ x, (weakGradient m (fun y => f y-g y) x)^2 ∂m)/2 := by positivity
  have hf0 : 0 ≤ (∫ x, (weakGradient m f x)^2 ∂m)/2 := by positivity
  have hg0 : 0 ≤ (∫ x, (weakGradient m g x)^2 ∂m)/2 := by positivity
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hm,
    ENNReal.toReal_ofReal hf0, ENNReal.toReal_ofReal hg0] at Hr
  linarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_LocalGradientParallelogramCheeger
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma localGradientParallelogram_of_cheeger [CompleteSpace X] [ProperSpace X] [Nonempty X]
    [TopologicalSpace.SeparableSpace X] {m : Measure X}
    (hfinite : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2)) :
    LocalGradientParallelogram m := by
  intro f g hf hg
  exact weakGradient_local_pointwise_parallelogram hfinite
    (fun _ _ hu hv => integral_parallelogram_of_cheeger hfinite h hID hu hv) hf hg

lemma CurvatureDimension.global_localGradientParallelogram [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
     {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) :
    LocalGradientParallelogram m := by
  let : Nonempty X := ⟨o⟩
  apply localGradientParallelogram_of_cheeger hfinite h
  intro f hf
  rw [hcd.global_cheegerEnergy_eq_weakGradient hfinite o hf,norm_toLp_sq_eq_integral]

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

@[simp] lemma im_ofRealLp (f : Lp ℝ 2 m) : imLp m (ofRealLp m f) = 0 := by
  apply Lp.ext
  filter_upwards [imLp_ae m (ofRealLp m f), ofRealLp_ae m f, Lp.coeFn_zero ℝ 2 m] with x hr hf hz
  rw [hr,hf,hz]
  rfl

lemma reLp_smul_complex (c : ℂ) (f : Lp ℂ 2 m) :
    reLp m (c • f) = c.re • reLp m f - c.im • imLp m f := by
  apply Lp.ext
  filter_upwards [reLp_ae m (c • f), reLp_ae m f, imLp_ae m f,
    Lp.coeFn_smul c f, Lp.coeFn_sub (c.re • reLp m f) (c.im • imLp m f),
    Lp.coeFn_smul c.re (reLp m f), Lp.coeFn_smul c.im (imLp m f)] with x h1 h2 h3 h4 h5 h6 h7
  simp only [h1,h4,h5, Pi.sub_apply, h6,h7, Pi.smul_apply, h2,h3, smul_eq_mul, Complex.mul_re]

lemma imLp_smul_complex (c : ℂ) (f : Lp ℂ 2 m) :
    imLp m (c • f) = c.re • imLp m f + c.im • reLp m f := by
  apply Lp.ext
  filter_upwards [imLp_ae m (c • f), reLp_ae m f, imLp_ae m f,
    Lp.coeFn_smul c f, Lp.coeFn_add (c.re • imLp m f) (c.im • reLp m f),
    Lp.coeFn_smul c.re (imLp m f), Lp.coeFn_smul c.im (reLp m f)] with x h1 h2 h3 h4 h5 h6 h7
  simp only [h1,h4,h5, Pi.add_apply, h6,h7, Pi.smul_apply, h2,h3, smul_eq_mul, Complex.mul_im]

lemma ofRealLp_re_add_im (f : Lp ℂ 2 m) :
    ofRealLp m (reLp m f) + Complex.I • ofRealLp m (imLp m f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ofRealLp m (reLp m f)) (Complex.I • ofRealLp m (imLp m f)),
    Lp.coeFn_smul Complex.I (ofRealLp m (imLp m f)), ofRealLp_ae m (reLp m f),
    ofRealLp_ae m (imLp m f), reLp_ae m f, imLp_ae m f] with x ha hs hr hi hf hg
  simp only [ha, Pi.add_apply, hs, Pi.smul_apply, hr,hi,hf,hg, smul_eq_mul]
  simpa only [mul_comm] using Complex.re_add_im (f x)

lemma ofRealLp_inner (f g : Lp ℝ 2 m) :
    ⟪ofRealLp m f, ofRealLp m g⟫_ℂ = (⟪f,g⟫_ℝ : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ofRealLp_ae m f, ofRealLp_ae m g] with x hf hg
  simp [hf,hg, RCLike.inner_apply]

lemma complexLp_inner (f g : Lp ℂ 2 m) :
    ⟪f,g⟫_ℂ = (⟪reLp m f,reLp m g⟫_ℝ : ℂ) + (⟪imLp m f,imLp m g⟫_ℝ : ℂ) +
      ((⟪reLp m f,imLp m g⟫_ℝ : ℂ) - (⟪imLp m f,reLp m g⟫_ℝ : ℂ))*Complex.I := by
  conv_lhs => rw [← ofRealLp_re_add_im m f, ← ofRealLp_re_add_im m g]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    ofRealLp_inner, Complex.conj_I]
  ring_nf
  simp

def complexifyReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Lp ℂ 2 m →L[ℝ] Lp ℂ 2 m :=
  (ofRealLp m).comp (R.comp (reLp m)) +
    Complex.I • (ofRealLp m).comp (R.comp (imLp m))

lemma complexifyReal_apply (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    complexifyReal m R f = ofRealLp m (R (reLp m f)) +
      Complex.I • ofRealLp m (R (imLp m f)) := rfl

lemma complexLp_ext {f g : Lp ℂ 2 m}
    (hr : reLp m f = reLp m g) (hi : imLp m f = imLp m g) : f = g := by
  rw [← ofRealLp_re_add_im m f, hr, hi, ofRealLp_re_add_im]

@[simp] lemma re_complexifyReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    reLp m (complexifyReal m R f) = R (reLp m f) := by
  simp [complexifyReal_apply, reLp_smul_complex]

@[simp] lemma im_complexifyReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    imLp m (complexifyReal m R f) = R (imLp m f) := by
  simp [complexifyReal_apply, imLp_smul_complex]

lemma complexifyReal_smul (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (c : ℂ) (f : Lp ℂ 2 m) :
    complexifyReal m R (c • f) = c • complexifyReal m R f := by
  apply complexLp_ext m
  · simp [reLp_smul_complex]
  · simp [imLp_smul_complex]

def complexify (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m where
  toFun := complexifyReal m R
  map_add' := (complexifyReal m R).map_add
  map_smul' := complexifyReal_smul m R
  cont := (complexifyReal m R).continuous

@[simp] lemma re_complexify (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    reLp m (complexify m R f) = R (reLp m f) := re_complexifyReal m R f
@[simp] lemma im_complexify (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (f : Lp ℂ 2 m) :
    imLp m (complexify m R f) = R (imLp m f) := im_complexifyReal m R f

lemma complexify_symmetric {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.toLinearMap.IsSymmetric) : (complexify m R).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪complexify m R f,g⟫_ℂ = ⟪f,complexify m R g⟫_ℂ
  simp only [complexLp_inner, re_complexify, im_complexify]
  have hr (u v : Lp ℝ 2 m) : ⟪R u,v⟫_ℝ = ⟪u,R v⟫_ℝ := hR u v
  simp only [hr]

lemma complexify_injective {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : Function.Injective R) : Function.Injective (complexify m R) := by
  intro f g h
  apply complexLp_ext m
  · apply hR
    simpa using congrArg (reLp m) h
  · apply hR
    simpa using congrArg (imLp m) h

lemma complexify_positive {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.IsPositive) : (complexify m R).IsPositive := by
  refine ⟨complexify_symmetric m hR.isSymmetric, ?_⟩
  intro f
  change 0 ≤ (⟪complexify m R f,f⟫_ℂ).re
  rw [complexLp_inner]
  simp only [re_complexify, im_complexify, Complex.add_re, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_self, zero_mul, add_zero]
  exact add_nonneg (hR.re_inner_nonneg_left _) (hR.re_inner_nonneg_left _)

lemma complexify_sub (R S : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) :
    complexify m (R-S) = complexify m R-complexify m S := by
  ext1 f
  apply complexLp_ext m <;> simp

lemma complexify_one : complexify m (1 : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) = 1 := by
  ext1 f
  apply complexLp_ext m <;> simp

lemma complexify_range_dense {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hs : R.toLinearMap.IsSymmetric) (hi : Function.Injective R) :
    (complexify m R).toLinearMap.range.topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply complexify_injective m hi
  rw [map_zero]
  have hz : ∀ w, ⟪w,complexify m R u⟫_ℂ = 0 := by
    intro w
    exact ((complexify_symmetric m hs) w u).symm.trans
      ((Submodule.mem_orthogonal _ _).mp hu (complexify m R w) ⟨w,rfl⟩)
  exact inner_self_eq_zero.mp (hz (complexify m R u))

lemma ofRealLp_of_im_zero {f : Lp ℂ 2 m} (hf : imLp m f = 0) :
    ofRealLp m (reLp m f) = f := by
  simpa [hf] using ofRealLp_re_add_im m f

attribute [local instance] OAI.WeakHessianFunctional.instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions
def realOperators : StarSubalgebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) where
  carrier := {T | ∀ f : Lp ℝ 2 m, imLp m (T (ofRealLp m f)) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro T S hT hS f
    change imLp m (T (ofRealLp m f) + S (ofRealLp m f)) = 0
    simp [hT f,hS f]
  one_mem' := by simp
  mul_mem' := by
    intro T S hT hS f
    change imLp m (T (S (ofRealLp m f))) = 0
    rw [← ofRealLp_of_im_zero m (hS f)]
    exact hT _
  algebraMap_mem' := by
    intro r f
    change imLp m (r • ofRealLp m f) = 0
    simp
  star_mem' := by
    intro T hT f
    let v := imLp m ((star T) (ofRealLp m f))
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have he := congrArg Complex.im
      (ContinuousLinearMap.adjoint_inner_left T (ofRealLp m v) (ofRealLp m f))
    change (⟪(star T) (ofRealLp m f),ofRealLp m v⟫_ℂ).im =
      (⟪ofRealLp m f,T (ofRealLp m v)⟫_ℂ).im at he
    simp only [complexLp_inner, re_ofRealLp, im_ofRealLp, hT v, inner_zero_right,
      inner_zero_left, Complex.ofReal_zero, add_zero, zero_sub, sub_zero,
      Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.neg_im, Complex.neg_re, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, mul_one] at he
    change ⟪v,v⟫_ℝ = 0
    linarith

lemma realOperators_closed : IsClosed (realOperators m : Set (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m)) := by
  change IsClosed {T : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m | ∀ f : Lp ℝ 2 m,
    imLp m (T (ofRealLp m f)) = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro f
  exact isClosed_eq ((imLp m).continuous.comp (ContinuousLinearMap.apply ℂ _ (ofRealLp m f)).continuous)
    continuous_const

lemma complexify_mem_realOperators (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) :
    complexify m R ∈ realOperators m := by
  intro f
  simp

lemma cfc_preserves_real (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ)
    (f : Lp ℝ 2 m) : imLp m (cfc a (complexify m R) (ofRealLp m f)) = 0 := by
  have hle : StarAlgebra.elemental ℝ (complexify m R) ≤ realOperators m :=
    StarAlgebra.elemental.le_of_mem (realOperators_closed m) (complexify_mem_realOperators m R)
  exact hle (cfc_mem_elemental a (complexify m R)) f

def realCfc (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  (reLp m).comp (((cfc a (complexify m R)).restrictScalars ℝ).comp (ofRealLp m))

lemma ofReal_realCfc (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ)
    (f : Lp ℝ 2 m) : ofRealLp m (realCfc m R a f) = cfc a (complexify m R) (ofRealLp m f) :=
  ofRealLp_of_im_zero m (cfc_preserves_real m R a f)

end WeakHessianFunctional

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_RealHeat
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

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

lemma ofRealLp_norm (f : Lp ℝ 2 m) : ‖ofRealLp m f‖ = ‖f‖ := by
  have h := congrArg Complex.re (ofRealLp_inner m f f)
  have he := inner_self_eq_norm_sq (𝕜 := ℂ) (ofRealLp m f)
  change (⟪ofRealLp m f,ofRealLp m f⟫_ℂ).re = ‖ofRealLp m f‖^2 at he
  rw [he, Complex.ofReal_re, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (ofRealLp m f), norm_nonneg f]

lemma ofRealLp_injective : Function.Injective (ofRealLp m) := by
  intro u v huv
  simpa using congrArg (reLp m) huv

lemma complexify_le_one {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR1 : (1-R).IsPositive) :
    (1-complexify m R).IsPositive := by
  simpa only [complexify_sub, complexify_one] using complexify_positive m hR1

def realHeat (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  realCfc m R (heatSymbol t)

lemma ofReal_realHeat (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ) (u : Lp ℝ 2 m) :
    ofRealLp m (realHeat m R t u) = resolventHeat (complexify m R) t (ofRealLp m u) :=
  ofReal_realCfc m R (heatSymbol t) u

lemma realHeat_zero {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive) :
    realHeat m R 0 = 1 := by
  ext1 u
  apply ofRealLp_injective m
  rw [ofReal_realHeat, resolventHeat_zero (complexify_positive m hR)]
  rfl

lemma realHeat_add (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    realHeat m R (t+s) = realHeat m R t * realHeat m R s := by
  ext1 u
  apply ofRealLp_injective m
  change ofRealLp m (realHeat m R (t+s) u) = ofRealLp m (realHeat m R t (realHeat m R s u))
  simp only [ofReal_realHeat, resolventHeat_add _ ht hs]
  rfl

lemma realHeat_contractive {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (u v : Lp ℝ 2 m) :
    dist (realHeat m R t u) (realHeat m R t v) ≤ dist u v := by
  have H := resolventHeat_contractive (complexify_positive m hR) (complexify_le_one m hR1)
    ht (ofRealLp m u) (ofRealLp m v)
  simpa only [← ofReal_realHeat, dist_eq_norm, ← map_sub, ofRealLp_norm] using H

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ComplexifyReal
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

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

@[simp] lemma complexify_ofReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (u : Lp ℝ 2 m) :
    complexify m R (ofRealLp m u) = ofRealLp m (R u) := by
  apply complexLp_ext m <;> simp

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeat
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

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

def cheegerHeat (h : QuadraticCheegerEnergy m) (t : ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  realHeat m (cheeger_closedQuadraticEnergy h).resolventLinear t

lemma cheegerHeat_zero (h : QuadraticCheegerEnergy m) : cheegerHeat h 0 = 1 :=
  realHeat_zero m (cheeger_closedQuadraticEnergy h).resolvent_positive

lemma cheegerHeat_contractive (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    (u v : Lp ℝ 2 m) : dist (cheegerHeat h t u) (cheegerHeat h t v) ≤ dist u v :=
  realHeat_contractive m (cheeger_closedQuadraticEnergy h).resolvent_positive
    (cheeger_closedQuadraticEnergy h).resolvent_le_one ht u v

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatGeneratorOperator
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
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

lemma realHeat_resolvent {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (t : ℝ) (u : Lp ℝ 2 m) : realHeat m R t (R u) = R (realHeat m R t u) := by
  apply ofRealLp_injective m
  rw [ofReal_realHeat, ← complexify_ofReal m R, ← complexify_ofReal m R, ofReal_realHeat]
  exact resolventHeat_resolvent (complexify_positive m hR) t (ofRealLp m u)

lemma realHeat_deriv_range_zero {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hi : Function.Injective R) (v : Lp ℝ 2 m) :
    HasDerivWithinAt (fun t : ℝ => realHeat m R t (R v)) (R v-v) (Ici 0) 0 := by
  have H := resolventHeat_deriv_range_zero (complexify_positive m hR)
    (complexify_le_one m hR1) (complexify_range_dense m hR.isSymmetric hi) (ofRealLp m v)
  have Hr := (reLp m).hasFDerivAt.comp_hasDerivWithinAt 0 H
  simpa only [Function.comp_def, complexify_ofReal, ← ofReal_realHeat, map_sub,
    re_ofRealLp] using Hr

end WeakHessianFunctional
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.formGenerator_heat {u A : Lp ℝ 2 m}
    (hu : hQ.IsFormGenerator u A) (t : ℝ) :
    hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u)
      (realHeat m hQ.resolventLinear t A) := by
  rw [hQ.isFormGenerator_iff, ← map_sub]
  change hQ.resolventLinear (realHeat m hQ.resolventLinear t (u-A)) = _
  rw [← realHeat_resolvent m hQ.resolvent_positive]
  change realHeat m hQ.resolventLinear t (hQ.resolvent (u-A)) = _
  rw [(hQ.isFormGenerator_iff _ _).mp hu]

lemma ClosedQuadraticEnergy.heat_deriv_form_zero (hd : hQ.domain.topologicalClosure = ⊤)
    {u A : Lp ℝ 2 m} (hu : hQ.IsFormGenerator u A) :
    HasDerivWithinAt (fun t : ℝ => realHeat m hQ.resolventLinear t u) A (Ici 0) 0 := by
  have H := realHeat_deriv_range_zero m hQ.resolvent_positive hQ.resolvent_le_one
    (hQ.resolvent_injective hd) (u-A)
  change HasDerivWithinAt (fun t : ℝ => realHeat m hQ.resolventLinear t (hQ.resolvent (u-A)))
    (hQ.resolvent (u-A)-(u-A)) (Ici 0) 0 at H
  simpa only [(hQ.isFormGenerator_iff _ _).mp hu, sub_sub_cancel] using H

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_RealHeatRangeError
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
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

lemma realHeat_range_error_apply {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.IsPositive) (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (v : Lp ℝ 2 m) :
    ‖realHeat m R t (R v)-R v‖ ≤ t*‖v‖ := by
  have H := resolventHeat_range_error_apply (complexify_positive m hR)
    (complexify_le_one m hR1) ht (ofRealLp m v)
  simpa only [complexify_ofReal, ← ofReal_realHeat, ← map_sub, ofRealLp_norm] using H

lemma realHeat_range_lipschitz {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.IsPositive) (hR1 : (1-R).IsPositive) (v : Lp ℝ 2 m) :
    LipschitzOnWith ‖v‖₊ (fun t : ℝ => realHeat m R t (R v)) (Ici 0) := by
  have H (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      dist (realHeat m R t (R v)) (realHeat m R s (R v)) ≤ ‖v‖*|t-s| := by
    have heq : realHeat m R t (R v) = realHeat m R s (realHeat m R (t-s) (R v)) := by
      have he := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T (R v))
        (realHeat_add m R hs (sub_nonneg.mpr hst))
      simpa only [mul_apply_eq_comp, add_sub_cancel] using he
    rw [heq]
    apply (realHeat_contractive m hR hR1 hs _ _).trans
    have H := realHeat_range_error_apply m hR hR1 (sub_nonneg.mpr hst) v
    simpa only [dist_eq_norm, abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using H
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  change dist (realHeat m R t (R v)) (realHeat m R s (R v)) ≤ ‖v‖*|t-s|
  rcases le_total s t with hst | hts
  · exact H s t hs hst
  · have HH := H t s ht hts
    rwa [dist_comm (realHeat m R s (R v)), abs_sub_comm s t] at HH

variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_lipschitz_on_generator {u A : Lp ℝ 2 m}
    (hu : hQ.IsFormGenerator u A) :
    LipschitzOnWith ‖u-A‖₊ (fun t : ℝ => realHeat m hQ.resolventLinear t u) (Ici 0) := by
  have H := realHeat_range_lipschitz m hQ.resolvent_positive hQ.resolvent_le_one (u-A)
  change LipschitzOnWith _ (fun t => realHeat m hQ.resolventLinear t (hQ.resolvent (u-A))) _ at H
  simpa only [(hQ.isFormGenerator_iff _ _).mp hu] using H

lemma ClosedQuadraticEnergy.heat_deriv_form_right (hd : hQ.domain.topologicalClosure = ⊤)
    {u A : Lp ℝ 2 m} (hu : hQ.IsFormGenerator u A) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => realHeat m hQ.resolventLinear s u)
      (realHeat m hQ.resolventLinear t A) (Ici t) t := by
  have hg := hQ.heat_deriv_form_zero m hd (hQ.formGenerator_heat m hu t)
  have hc : HasDerivWithinAt (fun s : ℝ => s-t) 1 (Ici t) t :=
    (hasDerivWithinAt_id t (Ici t)).sub_const t
  have H := hg.scomp_of_eq (h := fun s : ℝ => s-t) t hc
    (show MapsTo (fun s : ℝ => s-t) (Ici t) (Ici 0) from
      by intro s hs; exact (show 0 ≤ s-t from sub_nonneg.mpr hs)) (by simp)
  simp only [one_smul, Function.comp_def] at H
  apply H.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have he := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (realHeat_add m hQ.resolventLinear (sub_nonneg.mpr hs) ht)
    simpa only [mul_apply_eq_comp, sub_add_cancel] using he
  · rw [sub_self, realHeat_zero m hQ.resolvent_positive]
    rfl

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatContinuous
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

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_continuousOn (hfinite : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    ContinuousOn (fun t : ℝ => cheegerHeat h t u) (Ici 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  have hd : Dense (Q.resolventLinear.toLinearMap.range : Set (Lp ℝ 2 m)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (Q.resolvent_range_dense (cheeger_domain_dense h))
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro U hU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨v,⟨w,rfl⟩,hw⟩ := hd.exists_dist_lt u hε
  refine ⟨fun t => cheegerHeat h t (Q.resolvent w), ?_, ?_⟩
  · exact (Q.heat_lipschitz_on_generator m (Q.isFormGenerator_resolvent w)).continuousOn
  · intro t ht
    apply hεU
    change dist u (Q.resolvent w) < ε at hw
    exact (cheegerHeat_contractive h ht u (Q.resolvent w)).trans_lt hw

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GlobalCheegerEnergyReal
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
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma CurvatureDimension.global_cheegerEnergy_toReal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (_ : QuadraticCheegerEnergy m)
    {f : X → ℝ} (hf : Sobolev m f) :
    (cheegerEnergy m f).toReal = (∫ x, (weakGradient m f x)^2 ∂m) / 2 := by
  rw [hcd.global_cheegerEnergy_eq_weakGradient hfinite o hf, ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.2.2.coeFn_toLp] with x hx
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]

lemma CurvatureDimension.global_integral_gamma_eq {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    (∫ x, gamma m f g x ∂m) =
      ((cheegerEnergy m (fun x => f x+g x)).toReal -
        (cheegerEnergy m (fun x => f x-g x)).toReal)/2 := by
  have hp := hf.add hfinite hg
  have hm := hf.sub hfinite hg
  simp only [gamma, integral_div, integral_sub hp.2.2.integrable_sq hm.2.2.integrable_sq,
    hcd.global_cheegerEnergy_toReal hfinite o h hp, hcd.global_cheegerEnergy_toReal hfinite o h hm]
  ring

lemma CurvatureDimension.global_integral_gamma_form {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (f g : (cheeger_closedQuadraticEnergy h).domain) :
    (∫ x, gamma m (f.val : X → ℝ) (g.val : X → ℝ) x ∂m) =
      2*(cheeger_closedQuadraticEnergy h).form f g := by
  have hf := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp f.val)).mpr f.property
  have hg := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp g.val)).mpr g.property
  rw [hcd.global_integral_gamma_eq hfinite o h hf hg]
  rw [ClosedQuadraticEnergy.form_apply]
  simp only [energyPolar, ClosedQuadraticEnergy.realEnergy, Submodule.coe_add,
    Submodule.coe_sub, cheegerEnergy_congr_ae (Lp.coeFn_add f.val g.val),
    cheegerEnergy_congr_ae (Lp.coeFn_sub f.val g.val)]
  change ((cheegerEnergy m (fun x => f.val x + g.val x)).toReal -
    (cheegerEnergy m (fun x => f.val x - g.val x)).toReal) / 2 =
    2 * (((cheegerEnergy m (fun x => f.val x + g.val x)).toReal -
      (cheegerEnergy m (fun x => f.val x - g.val x)).toReal) / 4)
  ring

lemma CurvatureDimension.global_isLaplacian_of_formGenerator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) :
    IsLaplacian m (u : X → ℝ) (A : X → ℝ) := by
  refine ⟨(hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp u)).mpr hu.1, Lp.memLp A, ?_⟩
  intro v hv
  let v' := hv.1.toLp v
  have hv' : cheegerEnergy m (v' : X → ℝ) < ∞ := by
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfinite o hv.1).mp hv
  have heq := hcd.global_integral_gamma_form hfinite o h ⟨u,hu.1⟩ ⟨v',hv'⟩
  have heq' := hu.2 ⟨v',hv'⟩
  calc
    (∫ x, gamma m (u : X → ℝ) v x ∂m) =
        ∫ x, gamma m (u : X → ℝ) (v' : X → ℝ) x ∂m :=
      integral_congr_ae (gamma_congr_ae Filter.EventuallyEq.rfl hv.1.coeFn_toLp.symm)
    _ = -⟪A,v'⟫_ℝ := heq.trans heq'
    _ = -(∫ x, A x * v x ∂m) := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hv.1.coeFn_toLp] with x hx
      change v' x * A x = A x * v x
      rw [show v' x = v x from hx]
      exact mul_comm _ _

end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

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
open MeasureTheory Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.davies_form (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) :
    (∫ x, A x * u x * Real.exp (2*V x) ∂m) ≤
      (L:ℝ)^2 * (∫ x, (u x)^2 * Real.exp (2*V x) ∂m) := by
  have hV2 : LipschitzWith (‖(2:ℝ)‖₊*L) (fun x => 2*V x) := (lipschitzWith_smul (2:ℝ)).comp hV
  have hB2 : ∀ᵐ x ∂m, 2*V x ≤ 2*B := hB.mono (fun x hx => by linarith)
  have hv := hu.1.mul_exp hfinite hV2 hB2
  have huV := hu.1.mul_exp hfinite hV hB
  have hi : Integrable (fun x => (u x)^2*Real.exp (2*V x)) m := by
    apply huV.1.integrable_sq.congr
    exact ae_of_all _ (fun x => by simp only [mul_pow,sq_exp_eq])
  have hlap := hu.2.2 (fun x => u x*Real.exp (2*V x)) hv
  have hg : gamma m u (fun x => u x*Real.exp (2*V x)) =ᵐ[m]
      (fun x => Real.exp (2*V x)*((weakGradient m u x)^2+2*u x*gamma m V u x)) := by
    filter_upwards [gamma_comm (m := m) u (fun x => u x*Real.exp (2*V x)),
      gamma_mul_exp_left hfinite hpar hu.1.2.1 (localSobolev_of_lipschitz hfinite hV2)
        hu.1.2.1 hB2 (weakGradient_le_lipschitz hfinite hV2),
      gamma_self (m := m) u,
      gamma_const_mul_left hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1 2]
      with x hc hm hs hc2
    rw [hc,hm,hs,hc2]
    ring
  have hb : ∀ᵐ x ∂m, -gamma m u (fun x => u x*Real.exp (2*V x)) x ≤
      (L:ℝ)^2*((u x)^2*Real.exp (2*V x)) := by
    filter_upwards [hg,abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1,
      weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u] with x hx hgam hLip hD
    have hgL : |gamma m V u x| ≤ (L:ℝ)*weakGradient m u x :=
      hgam.trans (mul_le_mul_of_nonneg_right hLip hD)
    have hm : |u x*gamma m V u x| ≤ |u x| *(L:ℝ)*weakGradient m u x := by
      rw [abs_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left hgL (abs_nonneg _)
    have hp : -((weakGradient m u x)^2+2*u x*gamma m V u x) ≤ (L:ℝ)^2*(u x)^2 := by
      have hlow := (abs_le.mp hm).1
      nlinarith [sq_nonneg (weakGradient m u x-(L:ℝ)*|u x|),sq_abs (u x)]
    rw [hx]
    have HH := mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*V x)).le
    nlinarith [HH]
  calc
    (∫ x, A x*u x*Real.exp (2*V x) ∂m) =
        -(∫ x, gamma m u (fun y => u y*Real.exp (2*V y)) x ∂m) := by
      have he : (∫ x, A x*u x*Real.exp (2*V x) ∂m) =
          ∫ x, A x*(u x*Real.exp (2*V x)) ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => mul_assoc _ _ _)
      rw [he]
      linarith
    _ ≤ (L:ℝ)^2*(∫ x, (u x)^2*Real.exp (2*V x) ∂m) := by
      rw [← integral_neg,← integral_const_mul]
      exact integral_mono_ae (integrable_gamma hfinite hu.1 hv).neg (hi.const_mul _) hb

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma CurvatureDimension.cheegerHeat_davies_generator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB (cheegerHeat h t u)‖^2 ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  let f : ℝ → ℝ := fun s => ‖T (cheegerHeat h s u)‖^2
  let f' : ℝ → ℝ := fun s => 2*⟪T (cheegerHeat h s u),T (cheegerHeat h s A)⟫_ℝ
  have hder (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt f (f' s) (Ici s) s := by
    have HS := (cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu hs
    change HasDerivWithinAt (fun r : ℝ => cheegerHeat h r u) (cheegerHeat h s A) (Ici s) s at HS
    exact (T.hasFDerivAt.comp_hasDerivWithinAt s HS).norm_sq
  have hbound (s : ℝ) (_hs : 0 ≤ s) : f' s ≤ 2*(L:ℝ)^2*f s := by
    have hG := hcd.global_isLaplacian_of_formGenerator hfinite o h (cheegerHeat h s u)
      (cheegerHeat h s A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu s)
    have HD := hG.davies_form hfinite (hcd.global_localGradientParallelogram hfinite o h) hV hB
    dsimp only [f',f,T]
    rw [expMulLp_inner,expMulLp_norm_sq]
    linarith
  have hcont : ContinuousOn f (Icc 0 t) := by
    have H := (cheeger_closedQuadraticEnergy h).heat_lipschitz_on_generator m hu
    change LipschitzOnWith _ (fun s : ℝ => cheegerHeat h s u) (Ici 0) at H
    exact (T.continuous.comp_continuousOn (H.continuousOn.mono Icc_subset_Ici_self)).norm.pow 2
  have H := le_gronwallBound_of_liminf_deriv_right_le (f' := f') (K := 2*(L:ℝ)^2) (ε := 0) hcont
    (fun s hs r hr => (hder s hs.1).liminf_right_slope_le hr)
    (show f 0 ≤ ‖T u‖^2 by simp [f,T,cheegerHeat_zero])
    (fun s hs => by simpa only [add_zero] using hbound s hs.1) t (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  simpa only [gronwallBound_ε0,sub_zero,f,T] using H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatDavies
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

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_davies {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB (cheegerHeat h t u)‖^2 ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hd : Dense (Q.resolventLinear.toLinearMap.range : Set (Lp ℝ 2 m)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (Q.resolvent_range_dense (cheeger_domain_dense h))
  apply hd.induction (P := fun v => ‖T (cheegerHeat h t v)‖^2 ≤ ‖T v‖^2*Real.exp (2*(L:ℝ)^2*t)) ?_ ?_ u
  · rintro v ⟨w,rfl⟩
    exact hcd.cheegerHeat_davies_generator hfinite o h (Q.isFormGenerator_resolvent w) hV hB ht
  · exact isClosed_le ((T.continuous.comp (cheegerHeat h t).continuous).norm.pow 2)
      ((T.continuous.norm.pow 2).mul_const _)

lemma CurvatureDimension.cheegerHeat_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun x => cheegerHeat h t u x*Real.exp (V x)) 2 m ∧
      (∫ x, (cheegerHeat h t u x*Real.exp (V x))^2 ∂m) ≤
        ‖hU.toLp (fun x => u x*Real.exp (V x))‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  apply memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
  intro n
  have H := hcd.cheegerHeat_davies hfinite o h u (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) ht
  exact H.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n) 2)
    (Real.exp_pos _).le)
lemma CurvatureDimension.cheegerHeat_weighted_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ‖(hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1.toLp
        (fun x => cheegerHeat h t u x*Real.exp (V x))‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq_eq_integral,mul_pow,sq_exp_eq]
  have H := (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).2
  simpa only [mul_assoc] using H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_Integral
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
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.integral_eq_zero (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A : X → ℝ}
    (hu : IsLaplacian m u A) (hA : Integrable A m)
    (hD : Integrable (weakGradient m u) m) : ∫ x, A x ∂m = 0 := by
  have hχ (n : ℕ) : Sobolev m (radialCutoff o n) :=
    sobolev_of_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n)
      (radialCutoff_compact o n)
  have hlim : Tendsto (fun n => ∫ x, A x*radialCutoff o n x ∂m) atTop
      (𝓝 (∫ x, A x ∂m)) := by
    have H := tendsto_integral_of_dominated_convergence (fun x => |A x|)
      (fun n => hA.aestronglyMeasurable.mul
        (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using hA.norm)
      (fun n => ae_of_all _ fun x => by
        change |A x*radialCutoff o n x| ≤ |A x|
        rw [abs_mul,abs_of_nonneg (radialCutoff_nonneg o n x)]
        exact mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_le_one o n x))
      (ae_of_all _ fun x => tendsto_const_nhds.mul (radialCutoff_tendsto o x))
    simpa only [Pi.mul_apply,mul_one] using H
  have hb (n : ℕ) : ‖∫ x, A x*radialCutoff o n x ∂m‖ ≤
      (((n:ℝ)+1)⁻¹)*(∫ x, weakGradient m u x ∂m) := by
    have he := congrArg Neg.neg (hu.2.2 (radialCutoff o n) (hχ n))
    simp only [neg_neg] at he
    rw [← he,norm_neg]
    have HI := norm_integral_le_of_norm_le (f := gamma m u (radialCutoff o n)) (hD.const_mul (((n:ℝ)+1)⁻¹)) (by
      filter_upwards [abs_gamma_le hfinite hpar hu.1.2.1 (hχ n).2.1,
        weakGradient_le_lipschitz hfinite (radialCutoff_lipschitz o n),
        weakGradient_nonneg (m := m) u] with x hg hc hnon
      change |gamma m u (radialCutoff o n) x| ≤ (((n:ℝ)+1)⁻¹)*weakGradient m u x
      have hcr : weakGradient m (radialCutoff o n) x ≤ (((n:ℝ)+1)⁻¹) := by
        simpa only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hc
      exact hg.trans ((mul_le_mul_of_nonneg_left hcr hnon).trans_eq (mul_comm _ _)))
    simpa only [integral_const_mul] using HI
  have hz : Tendsto (fun n => ∫ x, A x*radialCutoff o n x ∂m) atTop (𝓝 0) := by
    apply squeeze_zero_norm hb
    simpa only [one_div,zero_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (∫ x, weakGradient m u x ∂m)
  exact tendsto_nhds_unique hlim hz
end WeakHessian

end
end InlinedFile0

end OAI
end


