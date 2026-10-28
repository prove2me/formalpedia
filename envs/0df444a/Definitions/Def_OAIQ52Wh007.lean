-- Prove2me | Definitions.Def_OAIQ52Wh007
-- name    : OAIQ52Wh007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:51:57.056682+00:00
-- url     : https://prove2.me/theorems/12b555f9-2089-494e-ae0b-70e40188db3c
-- title:
--   Definitions bundle OAIQ52Wh007 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 72 declarations of OpenAI's Lean: 11 definitions and 61 theorems. The definitions and types are `OAI.WeakHessian.CurvatureDimension.driftPerturbation`, `OAI.WeakHessian.CurvatureDimension.formGammaLp`, `OAI.WeakHessian.CurvatureDimension.heatProbability`, `OAI.WeakHessian.HeatVariableDissipation`, `OAI.WeakHessian.compactGeneratorRange`, `OAI.WeakHessian.compactHopfDualBound`, `OAI.WeakHessian.driftResolvent`, `OAI.WeakHessian.heatBridgeEnergy`, `OAI.WeakHessian.heatBridgeError`, `OAI.WeakHessian.localizedHeatError`, `OAI.WeakHessian.radialCutoffLp`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_CompactHopfCurve`, `WeakHessian_Calculus_GammaLimits`, `WeakHessian_Curvature_DecayWeight`, `WeakHessian_Entropy_FisherDensity`, `WeakHessian_HeatFlow_CheegerHeat`, `WeakHessian_HeatFlow_CheegerHeatContinuous`, `WeakHessian_HeatFlow_CheegerHeatLaplacianIntegral`, `WeakHessian_HeatFlow_CheegerHeatMassNonneg`, `WeakHessian_HeatFlow_CheegerHeatMassWeighted`, `WeakHessian_HeatFlow_CheegerResolventDavies`, `WeakHessian_HeatFlow_CompactGeneratorRange`, `WeakHessian_HeatFlow_DriftResolvent`, `WeakHessian_HeatFlow_HeatBridge`, `WeakHessian_HeatFlow_HeatProbability`, `WeakHessian_HeatFlow_LaplacianResolventUnique`, `WeakHessian_HeatFlow_PlanHeatEntropy`, `WeakHessian_HeatFlow_RealHeat`, `WeakHessian_HeatFlow_ScaledResolventCfc`, `WeakHessian_LocalBounds_AbsGammaLipschitz`, `WeakHessian_LocalBounds_ComplexifyReal`, `WeakHessian_LocalBounds_CoreAlgebra`, `WeakHessian_LocalBounds_DriftPerturbation`, `WeakHessian_LocalBounds_EnergyIdentification`, `WeakHessian_LocalBounds_FormGamma`, `WeakHessian_LocalBounds_GammaNatMulLeft`, `WeakHessian_LocalBounds_IdentifiedConservation`, `WeakHessian_LocalBounds_LocalizedCertificate`, `WeakHessian_LocalBounds_Smul`, `WeakHessian_LocalBounds_TestLinear`, `WeakHessian_LocalBounds_TestScaling`, `WeakHessian_LocalBounds_VariableDuhamelClosure`, `WeakHessian_Measure_DecayCutoffLp`, `WeakHessian_Measure_InlinedFile0`, `WeakHessian_Measure_IntegrableFatouNonneg`, `WeakHessian_Measure_IntegralExponentialMeasure`, `WeakHessian_Measure_RadialCutoffLp`, `WeakHessian_Sobolev_CompContDiff2`, `WeakHessian_Sobolev_DaviesGradient`, `WeakHessian_Sobolev_LaplacianLocality`, `WeakHessian_Sobolev_SobolevCheegerEnergyTop`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`; the bundles `OAIQ52Wh005` and `OAIQ52Wh006` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.WeakHessian.RCD.compact_core_product_identity`, `OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds`, `OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound`, `OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient` and `OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error`; the proofs of `OAI.WeakHessian.RCD.bounded_entropy_subdifferential`, `OAI.WeakHessian.RCD.cheegerHeat_comparison_integrated`, `OAI.WeakHessian.RCD.cheegerHeat_comparison_weighted`, `OAI.WeakHessian.RCD.cheegerHeat_contraction_weighted`, `OAI.WeakHessian.RCD.cheegerHeat_reversePoincare_pointwise`, `OAI.WeakHessian.RCD.compact_core_localized_pairing`, `OAI.WeakHessian.RCD.compact_core_localized_sobolev`, `OAI.WeakHessian.RCD.compact_core_product_identity`, `OAI.WeakHessian.RCD.compact_core_weak_equation`, `OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential`, `OAI.WeakHessian.RCD.generator_entropy_subdifferential`, `OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian`, `OAI.WeakHessian.RCD.test_gradientSquare_sobolev`, `OAI.WeakHessian.RCD.weighted_heat_boundedLipschitzRepresentative`, `OAI.WeakHessian.RCD.weighted_heat_concentration`, `OAI.WeakHessian.RCD.weighted_heat_curvature_continuousOn`, `OAI.WeakHessian.RCD.weighted_heat_gamma_continuousOn`, `OAI.WeakHessian.RCD.weighted_heat_gamma_memLp`, `OAI.WeakHessian.WeakHessianUpperBound.heatBridge_bounds`, `OAI.WeakHessian.WeakHessianUpperBound.localized_heatError_tail_bound`, `OAI.WeakHessian.WeakHessianUpperBound.localized_heat_gradient`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_localized_plan_law`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality`, `OAI.WeakHessian.cheegerHeat_plan_entropy_dual_error` and `OAI.WeakHessian.every_geodesic`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh005
import Definitions.Def_OAIQ52Wh006

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

theorem sobolev_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : Sobolev m f ↔ Sobolev ν f := by
  have transfer : ∀ {μ₁ μ₂ : Measure X} {C₁ C₂ : ℝ≥0},
      μ₁ ≤ (C₁ : ℝ≥0∞) • μ₂ → μ₂ ≤ (C₂ : ℝ≥0∞) • μ₁ →
      Sobolev μ₁ f → Sobolev μ₂ f := by
    intro μ₁ μ₂ C₁ C₂ h₁ h₂ hf
    refine ⟨MemLp.of_measure_le_smul ENNReal.coe_ne_top h₂ hf.1,
      (localSobolev_iff_of_comparable h₁ h₂ f).mp hf.2.1, ?_⟩
    exact MemLp.ae_eq (weakGradient_eq_of_comparable h₂ h₁ f).symm
      (MemLp.of_measure_le_smul ENNReal.coe_ne_top h₂ hf.2.2)
  exact ⟨transfer hm hν, transfer hν hm⟩

theorem sobolev_exponentialMeasure_iff {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f : X → ℝ) :
    Sobolev m f ↔ Sobolev (exponentialMeasure m V) f := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact sobolev_iff_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f

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

lemma gamma_aestronglyMeasurable (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    AEStronglyMeasurable (gamma m f g) m := by
  exact ((((weakGradient_isMinimal (hf.add hfinite hg).2).1.1.aestronglyMeasurable).pow 2).sub
    (((weakGradient_isMinimal (hf.sub hfinite hg).2).1.1.aestronglyMeasurable).pow 2)).mul_const (4⁻¹ : ℝ)

end WeakHessian

end

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
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

noncomputable def radialCutoffLp (hfinite : FiniteOnBoundedSets m) (o : X) (n : ℕ) : Lp ℝ 2 m :=
  (sobolev_of_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n)
    (radialCutoff_compact o n)).1.toLp (radialCutoff o n)
lemma radialCutoffLp_ae (hfinite : FiniteOnBoundedSets m) (o : X) (n : ℕ) :
    radialCutoffLp hfinite o n =ᵐ[m] radialCutoff o n := MemLp.coeFn_toLp _
lemma integral_radialCutoff_eq_inner (hfinite : FiniteOnBoundedSets m) (o : X) (n : ℕ) (f : Lp ℝ 2 m) :
    (∫ x, f x*radialCutoff o n x ∂m) = ⟪radialCutoffLp hfinite o n,f⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialCutoffLp_ae hfinite o n] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AbsGammaLipschitz
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
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma abs_gamma_lipschitz_le (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ}
    (hu : LocalSobolev m u) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ∀ᵐ x ∂m, |gamma m u φ x| ≤ (L:ℝ)*weakGradient m u x := by
  filter_upwards [abs_gamma_le hfinite hpar hu (localSobolev_of_lipschitz hfinite hφ),
    weakGradient_le_lipschitz hfinite hφ,weakGradient_nonneg (m := m) u] with x h1 h2 h3
  exact h1.trans (by nlinarith)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherDensity
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
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_le_localSlope (hfinite : FiniteOnBoundedSets m)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    ∀ᵐ x ∂m, weakGradient m u x ≤ (localSlope u x).toReal :=
  (weakGradient_isMinimal (localSobolev_of_lipschitz hfinite hu).2).2 _
    (localSlope_isLocalWeakUpperGradient hfinite hu)

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactHopfCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma compactHopf_exists_L2_curve (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    (o : X) (hf : HasCompactSupport (f : X → ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (W : ℝ → Lp ℝ 2 m) (D : ℝ),
      (∀ t, 0 < t → W t =ᵐ[m] boundedHopfMap f t) ∧
      ContinuousOn W (Icc a b) ∧
      (∀ t, 0 < t → Sobolev m (W t : X → ℝ)) ∧
      (∀ t, 0 < t → MemLp (fun x => (weakGradient m (W t) x)^2) 2 m) ∧
      (∀ t ∈ Icc a b, (∫ x, (weakGradient m (W t) x)^2 ∂m) ≤ D) ∧
      (∀ r s, 0 < r → r ≤ s → ∀ᵐ x ∂m,
        W s x-W r x ≤ (-(s-r)*r/(2*s))*(weakGradient m (W r) x)^2) := by
  let W : ℝ → Lp ℝ 2 m := fun t => if ht : 0 < t then
    (boundedHopfMap_memLp_compact hfin f o hf ht).toLp (boundedHopfMap f t) else 0
  have he (t : ℝ) (ht : 0 < t) : W t =ᵐ[m] boundedHopfMap f t := by
    dsimp only [W]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hSob (t : ℝ) (ht : 0 < t) : Sobolev m (W t : X → ℝ) :=
    (sobolev_congr_ae (he t ht)).mpr (sobolev_of_lipschitz_compactSupport hfin
      (boundedHopfMap_lipschitz f ht).choose_spec (boundedHopfMap_compactSupport f o hf ht))
  have hg2 (t : ℝ) (ht : 0 < t) : MemLp (fun x => (weakGradient m (W t) x)^2) 2 m := by
    obtain ⟨L,hL⟩ := boundedHopfMap_lipschitz f ht
    have hbb : ∀ᵐ x ∂m, |weakGradient m (W t) x| ≤ (L:ℝ) := by
      filter_upwards [weakGradient_congr_ae (he t ht),weakGradient_le_lipschitz hfin hL,
        weakGradient_nonneg (m := m) (W t)] with x hx hb hn
      rw [abs_of_nonneg hn,hx]; exact hb
    simpa only [sq] using
      memLp_mul_bounded (hSob t ht).2.2 (hSob t ht).2.2.aestronglyMeasurable hbb
  obtain ⟨R,L,_,hRL⟩ := compactHopf_uniform_data hfin f o hf ha hab
  let Q := Metric.closedBall o R
  have hQ : MeasurableSet Q := measurableSet_closedBall
  have hQfin : m Q < ∞ := hfin _ Metric.isBounded_closedBall
  let hi := memLp_indicator_const (μ := m) 2 hQ (1:ℝ) (Or.inr hQfin.ne)
  let χ : Lp ℝ 2 m := hi.toLp (Q.indicator (fun _ => (1:ℝ)))
  have hχe : χ =ᵐ[m] Q.indicator (fun _ => (1:ℝ)) := hi.coeFn_toLp
  have hLip : LipschitzOnWith ⟨(2*‖f‖/a)*‖χ‖,by positivity⟩ W (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    rw [dist_eq_norm]
    calc
      ‖W t-W s‖ ≤ ‖((2*‖f‖/a)*dist t s) • χ‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [Lp.coeFn_sub (W t) (W s),Lp.coeFn_smul ((2*‖f‖/a)*dist t s) χ,
          he t (ha.trans_le ht.1),he s (ha.trans_le hs.1),hχe] with x hd hm het hes hc
        simp only [hd,hm,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,het,hes,hc]
        by_cases hx : x ∈ Q
        · rw [indicator_of_mem hx,mul_one]
          rw [Real.norm_eq_abs (r := (2*‖f‖/a)*dist t s),abs_of_nonneg (by positivity)]
          exact ((BoundedContinuousFunction.dist_coe_le_dist (f := boundedHopfMap f t)
            (g := boundedHopfMap f s) x).trans
            ((boundedHopfMap_time_lipschitz f ha).dist_le_mul _ ht.1 _ hs.1))
        · rw [indicator_of_notMem hx,mul_zero,norm_zero,
            image_eq_zero_of_notMem_tsupport (fun hh => hx ((hRL t ht).1 hh)),
            image_eq_zero_of_notMem_tsupport (fun hh => hx ((hRL s hs).1 hh)),sub_self,norm_zero]
      _ = ((2*‖f‖/a)*‖χ‖)*dist t s := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        ring
  let D := ∫ x, Q.indicator (fun _ => (L:ℝ)^2) x ∂m
  refine ⟨W,D,he,hLip.continuousOn,hSob,hg2,?_,?_⟩
  · intro t ht
    apply integral_mono_ae (hSob t (ha.trans_le ht.1)).2.2.integrable_sq
      ((integrableOn_const (C := (L:ℝ)^2) hQfin.ne).integrable_indicator hQ)
    have hQS := sobolev_of_lipschitz_compactSupport hfin (hRL t ht).2
      (boundedHopfMap_compactSupport f o hf (ha.trans_le ht.1))
    filter_upwards [weakGradient_congr_ae (he t (ha.trans_le ht.1)),
      weakGradient_le_lipschitz hfin (hRL t ht).2,
      weakGradient_nonneg (m := m) (boundedHopfMap f t),weakGradient_zero_off_support hQS.2.1]
      with x hx hB hn hz
    rw [hx]
    by_cases hmem : x ∈ Q
    · rw [indicator_of_mem hmem]
      exact (sq_le_sq₀ hn L.coe_nonneg).mpr hB
    · rw [indicator_of_notMem hmem,hz (fun hh => hmem ((hRL t ht).1 hh)),sq]
      norm_num
  · intro r s hr hrs
    obtain ⟨L,hL⟩ := boundedHopfMap_lipschitz f hr
    have hsl := weakGradient_le_localSlope hfin hL
    have hfunc : (boundedHopfMap f r : X → ℝ) = hopfLax f r := funext (boundedHopfMap_apply_pos f hr)
    filter_upwards [he s (hr.trans_le hrs),he r hr,weakGradient_congr_ae (he r hr),
      hsl,weakGradient_nonneg (m := m) (boundedHopfMap f r)] with x hes her hge hg hn
    rw [hes,her,hge,boundedHopfMap_apply_pos f (hr.trans_le hrs),boundedHopfMap_apply_pos f hr]
    have H := hopf_forward_increment f.continuous (fun x => (boundedContinuous_bounds f x).1)
      (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) hr hrs x
    apply H.trans
    have hcoeff : -(s-r)*r/(2*s) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith
    rw [hfunc] at hg hn ⊢
    exact mul_le_mul_of_nonpos_left ((sq_le_sq₀ hn ENNReal.toReal_nonneg).mpr hg) hcoeff

end WeakHessianTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_GammaLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile16
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

lemma memLp_gamma_lipschitz (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ} (hu : Sobolev m u)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) : MemLp (gamma m u φ) 2 m :=
  (hu.2.2.const_mul (L:ℝ)).mono'
    (gamma_aestronglyMeasurable hfin hu.2.1 (localSobolev_of_lipschitz hfin hφ))
    (by simpa only [Real.norm_eq_abs] using abs_gamma_lipschitz_le hfin hpar hu.2.1 hφ)

end WeakHessian

end
end InlinedFile16

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

lemma realHeat_symmetric (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ) :
    (realHeat m R t).toLinearMap.IsSymmetric := by
  intro u v
  have h := (resolventHeat_positive (complexify m R) t).isSymmetric (ofRealLp m u) (ofRealLp m v)
  change ⟪resolventHeat (complexify m R) t (ofRealLp m u),ofRealLp m v⟫_ℂ =
    ⟪ofRealLp m u,resolventHeat (complexify m R) t (ofRealLp m v)⟫_ℂ at h
  rw [← ofReal_realHeat, ← ofReal_realHeat, ofRealLp_inner, ofRealLp_inner] at h
  exact Complex.ofReal_injective h

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

attribute [local instance] OAI.WeakHessianFunctional.instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions_2
lemma ofReal_realCfc_pow (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ)
    (n : ℕ) (u : Lp ℝ 2 m) :
    ofRealLp m (((realCfc m R a)^n) u) = ((cfc a (complexify m R))^n) (ofRealLp m u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, ofReal_realCfc, ih]

lemma realCfc_eulerStep_eq {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    R (realCfc m R (eulerStep t) u-t⁻¹ • (realCfc m R (eulerStep t) u-u)) =
      realCfc m R (eulerStep t) u := by
  apply ofRealLp_injective m
  rw [← complexify_ofReal m R]
  simp only [map_sub, map_smul, ofReal_realCfc]
  have hinv (v : Lp ℂ 2 m) : (t⁻¹ : ℝ) • v = (t⁻¹ : ℂ) • v := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change Complex.ofReal (t⁻¹) • v = (t⁻¹ : ℂ) • v
    rw [Complex.ofReal_inv]
  simpa only [mul_apply_eq_comp, _root_.sub_apply, hinv, _root_.smul_apply,
    one_apply_eq_self, map_sub] using congrArg (fun T : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m => T (ofRealLp m u))
    (cfc_eulerStep_eq (complexify_positive m hR) (complexify_le_one m hR1) ht)

lemma realCfc_eulerApproximation_tendsto {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => ((realCfc m R (eulerStep (t/(2:ℝ)^n)))^(2^n:ℕ)) u)
      atTop (𝓝 (realHeat m R t u)) := by
  have H := cfc_eulerApproximation_tendsto (complexify_positive m hR) (complexify_le_one m hR1) ht
  have Ha := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 m) (ofRealLp m u)).continuous.continuousAt.tendsto.comp H
  have Hr := (reLp m).continuous.continuousAt.tendsto.comp Ha
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ← ofReal_realCfc_pow, ← ofReal_realHeat, re_ofRealLp] using Hr

end WeakHessianFunctional

end
end InlinedFile0

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

lemma ClosedQuadraticEnergy.scaled_resolvent_cfc {t : ℝ} (ht : 0 < t) :
    (hQ.scale ht).resolventLinear = realCfc m hQ.resolventLinear (eulerStep t) := by
  ext1 u
  change (hQ.scale ht).resolvent u = realCfc m hQ.resolventLinear (eulerStep t) u
  rw [hQ.scaled_resolvent_iff ht, hQ.isFormGenerator_iff]
  exact realCfc_eulerStep_eq m hQ.resolvent_positive hQ.resolvent_le_one ht u

lemma ClosedQuadraticEnergy.euler_tendsto_heat {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => (((hQ.scale (by positivity : 0 < t/(2:ℝ)^n)).resolventLinear)^(2^n:ℕ)) u)
      atTop (𝓝 (realHeat m hQ.resolventLinear t u)) := by
  have heq : ∀ n : ℕ,
      (hQ.scale (by positivity : 0 < t/(2:ℝ)^n)).resolventLinear =
        realCfc m hQ.resolventLinear (eulerStep (t/(2:ℝ)^n)) := by
    intro n
    exact hQ.scaled_resolvent_cfc m (by positivity)
  simp_rw [heq]
  exact realCfc_eulerApproximation_tendsto m hQ.resolvent_positive hQ.resolvent_le_one ht u

lemma ClosedQuadraticEnergy.heat_normal_fixed
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    (hηQ : ∀ f : Lp ℝ 2 m, Q (hη.compLp hη0 f) ≤ Q f) (u : Lp ℝ 2 m)
    (hu : hη.compLp hη0 u = u) {t : ℝ} (ht : 0 ≤ t) :
    hη.compLp hη0 (realHeat m hQ.resolventLinear t u) = realHeat m hQ.resolventLinear t u := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [realHeat_zero m hQ.resolvent_positive, one_apply_eq_self] using hu
  have hstep {s : ℝ} (hs : 0 < s) (v : Lp ℝ 2 m) (hv : hη.compLp hη0 v = v) :
      hη.compLp hη0 ((hQ.scale hs).resolventLinear v) = (hQ.scale hs).resolventLinear v :=
    (hQ.scale hs).resolvent_normal_fixed m hη hη0 (fun f => mul_le_mul_right (hηQ f) _) v hv
  have hpow {s : ℝ} (hs : 0 < s) (n : ℕ) :
      hη.compLp hη0 ((((hQ.scale hs).resolventLinear)^n) u) = (((hQ.scale hs).resolventLinear)^n) u := by
    induction n with
    | zero => exact hu
    | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using hstep hs ((((hQ.scale hs).resolventLinear)^n) u) ih
  have H := hQ.euler_tendsto_heat m ht u
  have Hη := (hη.continuous_compLp hη0).continuousAt.tendsto.comp H
  have Hη' := H.congr' (Filter.Eventually.of_forall (fun n =>
    (hpow (by positivity : 0 < t/(2:ℝ)^n) (2^n)).symm))
  exact tendsto_nhds_unique Hη Hη'

end WeakHessianFunctional

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

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

lemma cheegerHeat_symmetric (h : QuadraticCheegerEnergy m) (t : ℝ) :
    (cheegerHeat h t).toLinearMap.IsSymmetric := realHeat_symmetric m _ t


lemma cheegerHeat_normal_fixed (h : QuadraticCheegerEnergy m)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0) (u : Lp ℝ 2 m)
    (hu : hη.compLp hη0 u = u) {t : ℝ} (ht : 0 ≤ t) :
    hη.compLp hη0 (cheegerHeat h t u) = cheegerHeat h t u := by
  apply (cheeger_closedQuadraticEnergy h).heat_normal_fixed m hη hη0 _ u hu ht
  intro f
  rw [cheegerEnergy_congr_ae (hη.coeFn_compLp hη0 f)]
  exact cheegerEnergy_normalContraction hη hη0 f

lemma cheegerHeat_nonneg (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) :
    ∀ᵐ x ∂m, 0 ≤ (cheegerHeat h t) u x := by
  let η : ℝ → ℝ := fun r => max r 0
  have hη : LipschitzWith 1 η := lipschitzWith_posPart
  have hη0 : η 0 = 0 := max_self _
  have hufix : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u, hu] with x hx hu
    simpa only [Function.comp_apply, η, max_eq_left hu] using hx
  have hfix := cheegerHeat_normal_fixed h hη hη0 u hufix ht
  filter_upwards [hη.coeFn_compLp hη0 ((cheegerHeat h t) u)] with x hx
  rw [hfix] at hx
  change (cheegerHeat h t) u x =
    max ((cheegerHeat h t) u x) 0 at hx
  rw [hx]
  exact le_max_right _ _

lemma cheegerHeat_order (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t) (u v : Lp ℝ 2 m)
    (huv : ∀ᵐ x ∂m, u x ≤ v x) :
    ∀ᵐ x ∂m, (cheegerHeat h t) u x ≤
      (cheegerHeat h t) v x := by
  have hsub : ∀ᵐ x ∂m, 0 ≤ (v-u) x := by
    filter_upwards [huv, Lp.coeFn_sub v u] with x hx hs
    simpa only [hs, Pi.sub_apply, sub_nonneg] using hx
  have hnon := cheegerHeat_nonneg h ht (v-u) hsub
  have hlin : (cheegerHeat h t) (v-u) =
      (cheegerHeat h t) v-(cheegerHeat h t) u :=
    (cheegerHeat h t).map_sub v u
  rw [hlin] at hnon
  filter_upwards [hnon, Lp.coeFn_sub ((cheegerHeat h t) v)
    ((cheegerHeat h t) u)] with x hn hs
  simpa only [hs, Pi.sub_apply, sub_nonneg] using hn


lemma cheegerHeat_interval (h : QuadraticCheegerEnergy m) {t : ℝ} (ht : 0 ≤ t)
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, u x ∈ Icc a b) :
    ∀ᵐ x ∂m, cheegerHeat h t u x ∈ Icc a b := by
  let η : ℝ → ℝ := fun r => max a (min r b)
  have hη : LipschitzWith 1 η := (LipschitzWith.id.min_const b).const_max a
  have hη0 : η 0 = 0 := by simp only [η, min_eq_left hb, max_eq_right ha]
  have hfixu : hη.compLp hη0 u = u := by
    apply Lp.ext
    filter_upwards [hη.coeFn_compLp hη0 u, hu] with x hx hu
    simpa only [Function.comp_apply, η, min_eq_left hu.2, max_eq_right hu.1] using hx
  have hfix := cheegerHeat_normal_fixed h hη hη0 u hfixu ht
  filter_upwards [hη.coeFn_compLp hη0 (cheegerHeat h t u)] with x hx
  rw [hfix] at hx
  change cheegerHeat h t u x = max a (min (cheegerHeat h t u x) b) at hx
  rw [hx]
  exact ⟨le_max_left _ _, max_le (ha.trans hb) (min_le_right _ _)⟩

end WeakHessian

end

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

lemma cheegerHeat_integral_generator (hfinite : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, cheegerHeat h s A) = cheegerHeat h t u-u := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  have hc := cheegerHeat_continuousOn hfinite h A
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    ((cheegerHeat_continuousOn hfinite h u).mono Icc_subset_Ici_self)
    (fun s hs => ((cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu hs.1.le).mono Ioi_subset_Ici_self)
    ((hc.mono (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable)
  change (∫ s in 0..t, cheegerHeat h s A) = cheegerHeat h t u-cheegerHeat h 0 u at H
  simpa only [cheegerHeat_zero, one_apply_eq_self] using H
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

lemma memLp_gamma_of_lipschitz (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V f : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) (hf : Sobolev m f) :
    MemLp (gamma m V f) 2 m := by
  have hv := localSobolev_of_lipschitz hfinite hV
  apply (hf.2.2.const_mul (L:ℝ)).mono' (gamma_aestronglyMeasurable hfinite hv hf.2.1)
  filter_upwards [abs_gamma_le hfinite hpar hv hf.2.1,weakGradient_le_lipschitz hfinite hV,
    weakGradient_nonneg (m := m) f] with x h hL hn
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg L.coe_nonneg,abs_of_nonneg hn] using
    h.trans (mul_le_mul_of_nonneg_right hL hn)
end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegralExponentialMeasure
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

lemma IsLaplacian.reweight (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A V : X → ℝ}
    (hA : IsLaplacian m u A) {L : ℝ≥0} (hV : LipschitzWith L V)
    {B : ℝ} (hB : ∀ x, |V x| ≤ B) :
    IsLaplacian (exponentialMeasure m V) u (fun x => A x+gamma m V u x) := by
  obtain ⟨_,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hu := hA.1
  have hVu := memLp_gamma_of_lipschitz hfinite hpar hV hu
  refine ⟨(sobolev_exponentialMeasure_iff hB u).mp hu,
    MemLp.of_measure_le_smul ENNReal.ofReal_ne_top hν (hA.2.1.add hVu), ?_⟩
  intro v hvν
  have hv := (sobolev_exponentialMeasure_iff hB v).mpr hvν
  have hb : ∀ᵐ x ∂m, V x ≤ B := ae_of_all m fun x => (le_abs_self _).trans (hB x)
  have heb : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx
  have hem := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hig : Integrable (fun x => Real.exp (V x)*gamma m u v x) m :=
    (integrable_gamma hfinite hu hv).bdd_mul hem heb
  have hiD : Integrable (fun x => Real.exp (V x)*(gamma m V u x*v x)) m :=
    (hVu.integrable_mul hv.1).bdd_mul hem heb
  have hiA : Integrable (fun x => Real.exp (V x)*(A x*v x)) m :=
    (hA.2.1.integrable_mul hv.1).bdd_mul hem heb
  have htest := hA.2.2 (fun x => v x*Real.exp (V x)) (hv.mul_exp hfinite hV hb)
  have heq : gamma m u (fun x => v x*Real.exp (V x)) =ᵐ[m]
      (fun x => Real.exp (V x)*gamma m u v x + Real.exp (V x)*(gamma m V u x*v x)) := by
    filter_upwards [gamma_mul_exp_left hfinite hpar hv.2.1
      (localSobolev_of_lipschitz hfinite hV) hu.2.1 hb
      (weakGradient_le_lipschitz hfinite hV),
      gamma_comm (m := m) u (fun x => v x*Real.exp (V x)),gamma_comm (m := m) v u]
      with x hp hc hcv
    rw [hc,hp,hcv]
    ring
  rw [integral_congr_ae heq, integral_add hig hiD] at htest
  have heA : (∫ x, A x*(v x*Real.exp (V x)) ∂m) =
      ∫ x, Real.exp (V x)*(A x*v x) ∂m := by
    congr 1
    funext x
    ring
  rw [heA] at htest
  have hg := gamma_exponentialMeasure (m := m) hB u v
  rw [integral_exponentialMeasure hV.continuous.aemeasurable,
    integral_exponentialMeasure hV.continuous.aemeasurable]
  calc
    (∫ x, Real.exp (V x)*gamma (exponentialMeasure m V) u v x ∂m) =
        ∫ x, Real.exp (V x)*gamma m u v x ∂m :=
      integral_congr_ae (by filter_upwards [hg] with x hx; rw [hx])
    _ = -(∫ x, Real.exp (V x)*(A x*v x) ∂m) -
        (∫ x, Real.exp (V x)*(gamma m V u x*v x) ∂m) := by linarith
    _ = -(∫ x, Real.exp (V x)*((A x+gamma m V u x)*v x) ∂m) := by
      rw [show (fun x => Real.exp (V x)*((A x+gamma m V u x)*v x)) =
        (fun x => Real.exp (V x)*(A x*v x)+ Real.exp (V x)*(gamma m V u x*v x)) by
          funext x; ring,integral_add hiA hiD]
      ring
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_Smul
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
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m ν : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma IsLaplacian.congr_ae {f g L M : X → ℝ}
    (hf : IsLaplacian m f L) (hfg : f =ᵐ[m] g) (hLM : L =ᵐ[m] M) :
    IsLaplacian m g M := by
  refine ⟨(sobolev_congr_ae hfg).mp hf.1, hf.2.1.ae_eq hLM, ?_⟩
  intro v hv
  rw [← integral_congr_ae (gamma_congr_ae hfg (Filter.EventuallyEq.rfl)), hf.2.2 v hv]
  congr 1
  apply integral_congr_ae
  filter_upwards [hLM] with x hx
  rw [hx]

end WeakHessian

end
end InlinedFile0

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

lemma sobolev_of_cheegerEnergy_lt_top (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : cheegerEnergy m f < ∞) : Sobolev m f := by
  have hfm : MemLp f 2 m := by
    by_contra hn
    simp only [cheegerEnergy, ite_eq_right hn, lt_self_iff_false] at hf
  obtain ⟨D,hD,_⟩ := exists_minimalGradient_energy_le_cheeger hfinite hfm hf
  refine ⟨hfm,⟨fun _ _ _ => hfm.restrict _, D,hD⟩,?_⟩
  exact (Lp.memLp D).ae_eq (hD.ae_eq (weakGradient_isMinimal ⟨D,hD⟩))

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_DaviesGradient
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

lemma IsLaplacian.davies_gradient (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) :
    (∫ x, (weakGradient m u x)^2 * Real.exp (2*V x) ∂m) ≤
      -2*(∫ x, A x * u x * Real.exp (2*V x) ∂m)+
        4*(L:ℝ)^2*(∫ x, (u x)^2 * Real.exp (2*V x) ∂m) := by
  have hV2 : LipschitzWith (‖(2:ℝ)‖₊*L) (fun x => 2*V x) := (lipschitzWith_smul (2:ℝ)).comp hV
  have hB2 : ∀ᵐ x ∂m, 2*V x ≤ 2*B := hB.mono (fun x hx => by linarith)
  have hv := hu.1.mul_exp hfinite hV2 hB2
  have hexp : AEStronglyMeasurable (fun x => Real.exp (V x)) m :=
    Real.continuous_exp.comp_aestronglyMeasurable hV.continuous.aestronglyMeasurable
  have hexpB : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B :=
    hB.mono (fun x hx => by simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx)
  have hi : Integrable (fun x => (u x)^2*Real.exp (2*V x)) m := by
    apply (memLp_mul_bounded hu.1.1 hexp hexpB).integrable_sq.congr
    exact ae_of_all _ (fun x => by simp only [mul_pow,sq_exp_eq])
  have hDi : Integrable (fun x => (weakGradient m u x)^2*Real.exp (2*V x)) m := by
    apply (memLp_mul_bounded hu.1.2.2 hexp hexpB).integrable_sq.congr
    exact ae_of_all _ (fun x => by simp only [mul_pow,sq_exp_eq])
  have hlap := hu.2.2 (fun x => u x*Real.exp (2*V x)) hv
  have hg : gamma m u (fun x => u x*Real.exp (2*V x)) =ᵐ[m]
      (fun x => Real.exp (2*V x)*((weakGradient m u x)^2+2*u x*gamma m V u x)) := by
    filter_upwards [gamma_comm (m := m) u (fun x => u x*Real.exp (2*V x)),
      gamma_mul_exp_left hfinite hpar hu.1.2.1 (localSobolev_of_lipschitz hfinite hV2)
        hu.1.2.1 hB2 (weakGradient_le_lipschitz hfinite hV2),gamma_self (m := m) u,
      gamma_const_mul_left hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1 2]
      with x hc hm hs hc2
    rw [hc,hm,hs,hc2]; ring
  have hb : ∀ᵐ x ∂m, (weakGradient m u x)^2*Real.exp (2*V x) ≤
      2*gamma m u (fun x => u x*Real.exp (2*V x)) x+4*(L:ℝ)^2*((u x)^2*Real.exp (2*V x)) := by
    filter_upwards [hg,abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1,
      weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u] with x hx hgam hLip hD
    have hgL : |gamma m V u x| ≤ (L:ℝ)*weakGradient m u x :=
      hgam.trans (mul_le_mul_of_nonneg_right hLip hD)
    have hm : |u x*gamma m V u x| ≤ |u x| *(L:ℝ)*weakGradient m u x := by
      rw [abs_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left hgL (abs_nonneg _)
    have hp : (weakGradient m u x)^2 ≤
        2*((weakGradient m u x)^2+2*u x*gamma m V u x)+4*(L:ℝ)^2*(u x)^2 := by
      have hlo := (abs_le.mp hm).1
      nlinarith [sq_nonneg (weakGradient m u x-2*(L:ℝ)*|u x|),sq_abs (u x)]
    rw [hx]
    have HH := mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*V x)).le
    nlinarith [HH]
  have HI := integral_mono_ae hDi (((integrable_gamma hfinite hu.1 hv).const_mul 2).add (hi.const_mul _)) hb
  simp only [Pi.add_apply] at HI
  rw [integral_add ((integrable_gamma hfinite hu.1 hv).const_mul 2) (hi.const_mul _),
    integral_const_mul,integral_const_mul,hlap] at HI
  have he : (∫ x, A x*u x*Real.exp (2*V x) ∂m) =
      ∫ x, A x*(u x*Real.exp (2*V x)) ∂m := by
    apply integral_congr_ae; exact ae_of_all _ (fun x => mul_assoc _ _ _)
  rw [he]; linarith

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerResolventDavies
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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerResolvent_davies {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB
        (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u)‖ ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖/(1-t*(L:ℝ)^2) := by
  let Q := cheeger_closedQuadraticEnergy h
  let v := (Q.scale ht).resolvent u
  let A := t⁻¹ • (v-u)
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hu : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht u v).mp rfl
  have hG := hcd.global_isLaplacian_of_formGenerator hfinite o h v A hu
  have HD := hG.davies_form hfinite (hcd.global_localGradientParallelogram hfinite o h) hV hB
  rw [← expMulLp_inner hV.continuous.aestronglyMeasurable hB v A,
    ← expMulLp_norm_sq hV.continuous.aestronglyMeasurable hB v] at HD
  change ⟪T v,T A⟫_ℝ ≤ (L:ℝ)^2*‖T v‖^2 at HD
  have he : ⟪T v,T A⟫_ℝ = t⁻¹*(‖T v‖^2-⟪T v,T u⟫_ℝ) := by
    simp only [A,map_smul,map_sub,real_inner_smul_right,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [he] at HD
  have HC := real_inner_le_norm (T v) (T u)
  have HI := mul_le_mul_of_nonneg_left HD ht.le
  rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at HI
  change ‖T v‖ ≤ ‖T u‖/(1-t*(L:ℝ)^2)
  rw [le_div_iff₀ (sub_pos.mpr hsmall)]
  by_cases hv : ‖T v‖ = 0
  · simp only [hv,zero_mul]; positivity
  · have hvp : 0 < ‖T v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith


lemma CurvatureDimension.cheegerResolvent_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    MemLp (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x)) 2 m := by
  apply (memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable _ (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) ?_).1
  intro n
  have HD := hcd.cheegerResolvent_davies hfinite o h u ht (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
  have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
  have H := HD.trans (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)
  exact pow_le_pow_left₀ (norm_nonneg _) H 2

lemma CurvatureDimension.cheegerResolvent_weighted_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖(hcd.cheegerResolvent_weighted hfinite o h u ht hV hU hsmall).toLp
      (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x))‖ ≤ ‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2) := by
  have H := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
    (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) (by
      intro n
      have HD := hcd.cheegerResolvent_davies hfinite o h u ht (hV.min_const (n:ℝ))
        (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
      have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      exact pow_le_pow_left₀ (norm_nonneg _) (HD.trans
        (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)) 2)
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (sub_pos.mpr hsmall).le)).mp
  rw [norm_toLp_sq_eq_integral]
  exact H.2

lemma IsLaplacian.memLp_gradient_mul_exp (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m) :
    MemLp (fun x => weakGradient m u x*Real.exp (V x)) 2 m := by
  let D := hu.1.2.2.toLp (weakGradient m u)
  let U := hU.toLp (fun x => u x*Real.exp (V x))
  let W := hA.toLp (fun x => A x*Real.exp (V x))
  have HD : D =ᵐ[m] weakGradient m u := hu.1.2.2.coeFn_toLp
  have Hfat := memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable D
    (B := 2*‖U‖*‖W‖+4*(L:ℝ)^2*‖U‖^2) (by
      intro n
      let bnd : ∀ᵐ x ∂m, min (V x) (n:ℝ) ≤ (n:ℝ) := ae_of_all _ (fun x => min_le_right _ _)
      let T := expMulLp (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable bnd
      have H := hu.davies_gradient hfinite hpar (hV.min_const (n:ℝ)) bnd
      have he : ‖T D‖^2 = ∫ x, (weakGradient m u x)^2*Real.exp (2*min (V x) (n:ℝ)) ∂m := by
        rw [expMulLp_norm_sq]
        exact integral_congr_ae (HD.mono (fun x hx => by dsimp only; rw [hx]))
      rw [← he,← expMulLp_inner (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable bnd u A,
        ← expMulLp_norm_sq (hV.min_const (n:ℝ)).continuous.aestronglyMeasurable bnd u] at H
      have hTu : ‖T u‖ ≤ ‖U‖ := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
      have hTa : ‖T A‖ ≤ ‖W‖ := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable A hA n
      have hc : -⟪T u,T A⟫_ℝ ≤ ‖T u‖*‖T A‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      have hp : ‖T u‖*‖T A‖ ≤ ‖U‖*‖W‖ := mul_le_mul hTu hTa (norm_nonneg _) (norm_nonneg _)
      have hsq : ‖T u‖^2 ≤ ‖U‖^2 := pow_le_pow_left₀ (norm_nonneg _) hTu 2
      have hsq' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*(L:ℝ)^2 by positivity)
      change ‖T D‖^2 ≤ _
      nlinarith)
  exact MemLp.ae_eq (HD.mono (fun x hx => by dsimp only; rw [hx])) Hfat.1

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatLaplacianIntegral
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

lemma CurvatureDimension.cheegerHeat_laplacian_integral_zero {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t A x ∂m) = 0 := by
  have hUt := (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1
  have hAt := (hcd.cheegerHeat_weighted hfinite o h A hV hA ht).1
  have hpar := hcd.global_localGradientParallelogram hfinite o h
  have hLap := hcd.global_isLaplacian_of_formGenerator hfinite o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  exact hLap.integral_eq_zero hfinite hpar o (integrable_of_memLp_mul_exp hAt hdecay)
    (integrable_of_memLp_mul_exp (hLap.memLp_gradient_mul_exp hfinite hpar hV hUt hAt) hdecay)

lemma CurvatureDimension.cheegerHeat_mass_weighted_generator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, cheegerHeat h t u x ∂m) = ∫ x, u x ∂m := by
  let C := ‖hA.toLp (fun x => A x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t)*
      ‖hdecay.toLp (fun x => Real.exp (-V x))‖
  let fn : ℕ → ℝ → ℝ := fun n s => ∫ x, cheegerHeat h s A x*radialCutoff o n x ∂m
  have hfn (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    have he : fn n = fun s => (innerSL ℝ (radialCutoffLp hfinite o n)) (cheegerHeat h s A) := by
      funext s; exact integral_radialCutoff_eq_inner hfinite o n _
    rw [he]
    exact (innerSL ℝ (radialCutoffLp hfinite o n)).continuous.comp_continuousOn
      (cheegerHeat_continuousOn hfinite h A)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 t) : ‖fn n s‖ ≤ C := by
    have hsW := (hcd.cheegerHeat_weighted hfinite o h A hV hA hs.1).1
    have HH := integral_cutoff_le_weighted hsW hdecay
      (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [abs_of_nonneg (radialCutoff_nonneg o n x)] using radialCutoff_le_one o n x)
    apply HH.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (hcd.cheegerHeat_weighted_norm hfinite o h A hV hA hs.1).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 (sq_nonneg _))
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop (𝓝 0) := by
    have H := integral_radialCutoff_tendsto o
      (integrable_of_memLp_mul_exp (hcd.cheegerHeat_weighted hfinite o h A hV hA hs).1 hdecay)
    rw [hcd.cheegerHeat_laplacian_integral_zero hfinite o h hu hV hU hA hdecay hs] at H
    exact H
  have htime : Tendsto (fun n => ∫ s in 0..t, fn n s) atTop (𝓝 0) := by
    have H := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := t) (f := fun _ => (0:ℝ)) (fun _ => C)
      (Eventually.of_forall (fun n =>
        ((hfn n).mono (show uIoc (0:ℝ) t ⊆ Ici 0 by rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc))
      (Eventually.of_forall (fun n => ae_of_all _ fun s hs =>
        hb n s (by rw [uIoc_of_le ht] at hs; exact ⟨hs.1.le,hs.2⟩)))
      (intervalIntegrable_const)
      (ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le))
    simpa only [intervalIntegral.integral_zero] using H
  have hFTC (n : ℕ) : (∫ s in 0..t, fn n s) =
      (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ (radialCutoffLp hfinite o n)
    have hAint : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t := ((cheegerHeat_continuousOn hfinite h A).mono
      (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfinite h hu ht)
    rw [← T.intervalIntegral_comp_comm hAint,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_radialCutoff_eq_inner hfinite o n] using H
  have hsp := (integral_radialCutoff_tendsto o
    (integrable_of_memLp_mul_exp (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1 hdecay)).sub
      (integral_radialCutoff_tendsto o (integrable_of_memLp_mul_exp hU hdecay))
  rw [show (fun n => ∫ s in 0..t, fn n s) = (fun n =>
    (∫ x, cheegerHeat h t u x*radialCutoff o n x ∂m)-(∫ x, u x*radialCutoff o n x ∂m)) from funext hFTC] at htime
  exact sub_eq_zero.mp (tendsto_nhds_unique hsp htime)
end WeakHessian

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

lemma integral_tendsto_of_weighted_bound {V : X → ℝ}
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hfinite : FiniteOnBoundedSets m) (o : X)
    {fs : ℕ → Lp ℝ 2 m} {f : Lp ℝ 2 m} (hlim : Tendsto fs atTop (𝓝 f))
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hfs : ∀ n, MemLp (fun x => fs n x*Real.exp (V x)) 2 m)
    {B : ℝ} (hB : ∀ n, ‖(hfs n).toLp (fun x => fs n x*Real.exp (V x))‖ ≤ B) :
    Tendsto (fun n => ∫ x,fs n x ∂m) atTop (𝓝 (∫ x,f x ∂m)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let D := ‖hf.toLp (fun x => f x*Real.exp (V x))‖
  have htail : Tendsto (fun j => (B+D)*‖decayCutoffLp hV o j‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decayCutoffLp_norm_tendsto hV o).const_mul (B+D)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j,hj⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hc : Tendsto (fun n => ∫ x,fs n x*radialCutoff o j x ∂m) atTop
      (𝓝 (∫ x,f x*radialCutoff o j x ∂m)) := by
    simp_rw [integral_radialCutoff_eq_inner hfinite o j]
    exact (innerSL ℝ (radialCutoffLp hfinite o j)).continuous.continuousAt.tendsto.comp hlim
  filter_upwards [(Metric.tendsto_nhds.mp hc) (ε/2) (half_pos hε)] with n hn
  have he1 := (integral_cutoff_error_le_weighted (hfs n) hV o j).trans
    (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))
  have he2 := integral_cutoff_error_le_weighted hf hV o j
  have htri := dist_triangle (∫ x,fs n x ∂m) (∫ x,fs n x*radialCutoff o j x ∂m) (∫ x,f x ∂m)
  have htri2 := dist_triangle (∫ x,fs n x*radialCutoff o j x ∂m)
    (∫ x,f x*radialCutoff o j x ∂m) (∫ x,f x ∂m)
  simp only [dist_eq_norm] at htri htri2 hn ⊢
  rw [norm_sub_rev (∫ x,f x*radialCutoff o j x ∂m)] at htri2
  dsimp only [D] at hj
  nlinarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatMassWeighted
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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_mass_of_weighted_resolvents {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    {ts : ℕ → ℝ} (hpos : ∀ n, 0 < ts n)
    (hsmall : ∀ n, ts n*(L:ℝ)^2 ≤ 1/2) (hlim : Tendsto ts atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let us : ℕ → Lp ℝ 2 m := fun n => (Q.scale (hpos n)).resolventLinear u
  let As : ℕ → Lp ℝ 2 m := fun n => (ts n)⁻¹ • (us n-u)
  have hsmall' (n : ℕ) : ts n*(L:ℝ)^2 < 1 := (hsmall n).trans_lt (by norm_num)
  have hus (n : ℕ) : Q.IsFormGenerator (us n) (As n) :=
    (Q.scaled_resolvent_iff (hpos n) u (us n)).mp rfl
  have hW (n : ℕ) : MemLp (fun x => us n x*Real.exp (V x)) 2 m :=
    hcd.cheegerResolvent_weighted hfinite o h u (hpos n) hV hU (hsmall' n)
  have hWnorm (n : ℕ) : ‖(hW n).toLp (fun x => us n x*Real.exp (V x))‖ ≤
      2*‖hU.toLp (fun x => u x*Real.exp (V x))‖ := by
    apply (hcd.cheegerResolvent_weighted_norm hfinite o h u (hpos n) hV hU (hsmall' n)).trans
    apply (div_le_iff₀ (sub_pos.mpr (hsmall' n))).mpr
    have H := mul_le_mul_of_nonneg_left (hsmall n) (norm_nonneg (hU.toLp _))
    nlinarith
  have hAw (n : ℕ) : MemLp (fun x => As n x*Real.exp (V x)) 2 m := by
    have H := ((hW n).sub hU).const_smul ((ts n)⁻¹)
    apply MemLp.ae_eq _ H
    filter_upwards [Lp.coeFn_smul ((ts n)⁻¹) (us n-u),Lp.coeFn_sub (us n) u] with x hs hd
    dsimp only [As]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hd]
    simp only [Pi.sub_apply]
    ring
  have hum : Tendsto us atTop (𝓝 u) := Q.scaled_resolvent_tendsto (cheeger_domain_dense h) hpos hlim u
  have H1 := integral_tendsto_of_weighted_bound hdecay hfinite o hum hU hW hWnorm
  have hWt (n : ℕ) := (hcd.cheegerHeat_weighted hfinite o h (us n) hV (hW n) ht).1
  have hWtnorm (n : ℕ) : ‖(hWt n).toLp (fun x => cheegerHeat h t (us n) x*Real.exp (V x))‖ ≤
      (2*‖hU.toLp (fun x => u x*Real.exp (V x))‖)*Real.exp ((L:ℝ)^2*t) := by
    exact (hcd.cheegerHeat_weighted_norm hfinite o h (us n) hV (hW n) ht).trans
      (mul_le_mul_of_nonneg_right (hWnorm n) (Real.exp_pos _).le)
  have H2 := integral_tendsto_of_weighted_bound hdecay hfinite o
    ((cheegerHeat h t).continuous.continuousAt.tendsto.comp hum)
    (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1 hWt hWtnorm
  have he (n : ℕ) : (∫ x,cheegerHeat h t (us n) x ∂m) = ∫ x,us n x ∂m :=
    hcd.cheegerHeat_mass_weighted_generator hfinite o h (hus n) hV (hW n) (hAw n) hdecay ht
  simp_rw [Function.comp_def,he] at H2
  exact tendsto_nhds_unique H2 H1

lemma CurvatureDimension.cheegerHeat_mass_localized {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))) atTop (𝓝 ((0:ℝ)/(2*((L:ℝ)^2+1)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have H := mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))
    nlinarith
  exact hcd.cheegerHeat_mass_of_weighted_resolvents hfinite o h u hV hU hdecay hpos hsmall hlim ht
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

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

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma CurvatureDimension.cheegerHeat_mass_supported {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {R : ℝ} (hR : ∀ᵐ x ∂m, R ≤ dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) m ∧ (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  obtain ⟨a,ha,hd⟩ := hcd.exists_decay_weight hN hfull hfin o
  have hV : LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |a*dist x o-a*dist y o| ≤ |a| * dist x y
    rw [← mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)
  have hW := memLp_exp_dist_of_support u ha.le o hR
  have hd' : MemLp (fun x => Real.exp (-(a*dist x o))) 2 m := by
    simpa only [neg_mul] using hd
  refine ⟨integrable_of_memLp_mul_exp (hcd.cheegerHeat_weighted hfin o h u hV hW ht).1 hd', ?_⟩
  exact hcd.cheegerHeat_mass_localized hfin o h u hV hW hd' ht

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegrableFatouNonneg
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
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma cheegerHeat_submass (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hpos : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) m ∧ (∫ x,cheegerHeat h t u x ∂m) ≤ ∫ x,u x ∂m := by
  let v := cheegerHeat h t u
  have hv : ∀ᵐ x ∂m, 0 ≤ v x := cheegerHeat_nonneg h ht u hpos
  have hchi (n : ℕ) : ∀ᵐ x ∂m, radialCutoffLp hfinite o n x ∈ Icc (0:ℝ) 1 := by
    filter_upwards [radialCutoffLp_ae hfinite o n] with x hx
    rw [hx]
    exact ⟨radialCutoff_nonneg o n x,radialCutoff_le_one o n x⟩
  have hheat (n : ℕ) := cheegerHeat_interval h ht (le_refl (0:ℝ)) zero_le_one _ (hchi n)
  have hsym (n : ℕ) : (∫ x,v x*radialCutoff o n x ∂m) =
      ∫ x,u x*cheegerHeat h t (radialCutoffLp hfinite o n) x ∂m := by
    rw [integral_radialCutoff_eq_inner hfinite o n]
    change ⟪radialCutoffLp hfinite o n,cheegerHeat h t u⟫_ℝ = _
    have H := cheegerHeat_symmetric h t (radialCutoffLp hfinite o n) u
    change ⟪cheegerHeat h t (radialCutoffLp hfinite o n),u⟫_ℝ = ⟪radialCutoffLp hfinite o n,cheegerHeat h t u⟫_ℝ at H
    rw [← H, L2.inner_def]
    rfl
  have hbounded (n : ℕ) : (∫ x,v x*radialCutoff o n x ∂m) ≤ ∫ x,u x ∂m := by
    rw [hsym n]
    apply integral_mono_ae
    · exact hi.mul_bdd (Lp.memLp _).aestronglyMeasurable (by
        filter_upwards [hheat n] with x hx
        change |cheegerHeat h t (radialCutoffLp hfinite o n) x| ≤ (1:ℝ)
        rw [abs_of_nonneg hx.1]; exact hx.2)
    · exact hi
    · filter_upwards [hpos,hheat n] with x hx hc
      exact mul_le_of_le_one_right hx hc.2
  apply integrable_fatou_nonneg (Lp.memLp v).aestronglyMeasurable hv
    (fs := fun n x => v x*radialCutoff o n x)
  · intro n
    exact (Lp.memLp v).integrable_mul (sobolev_of_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n) (radialCutoff_compact o n)).1
  · intro n
    exact hv.mono fun x hx => mul_nonneg hx (radialCutoff_nonneg o n x)
  · exact ae_of_all _ fun x => by
      simpa only [mul_one] using (tendsto_const_nhds (x := v x)).mul (radialCutoff_tendsto o x)
  · exact hbounded
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CheegerHeatMassNonneg
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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_mass_nonneg {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) m ∧ (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  have hsub := cheegerHeat_submass hfin o h u hu hi ht
  refine ⟨hsub.1,le_antisymm hsub.2 ?_⟩
  have hχ (n : ℕ) : ∀ᵐ x ∂m, |radialCutoff o n x| ≤ (1:ℝ) := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let us (n : ℕ) : Lp ℝ 2 m := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (hχ n) u
  have he (n : ℕ) : us n =ᵐ[m] fun x => u x*radialCutoff o n x := boundedMulLp_ae _ _ u
  have hs (n : ℕ) : ∀ᵐ x ∂m, (n:ℝ)+1 ≤ dist x o → us n x = 0 := by
    filter_upwards [he n] with x hx hdist
    rw [hx]
    have hz : radialCutoff o n x = 0 := by
      apply max_eq_left
      have H : 1 ≤ dist x o/((n:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr (by simpa using hdist)
      linarith
    rw [hz,mul_zero]
  have hle (n : ℕ) : ∀ᵐ x ∂m, us n x ≤ u x := by
    filter_upwards [he n,hu] with x hx hpos
    rw [hx]
    exact mul_le_of_le_one_right hpos (radialCutoff_le_one o n x)
  have hmass (n : ℕ) := hcd.cheegerHeat_mass_supported hN hfull hfin o h (us n) (hs n) ht
  have hbound (n : ℕ) : (∫ x,u x*radialCutoff o n x ∂m) ≤ ∫ x,cheegerHeat h t u x ∂m := by
    rw [← integral_congr_ae (he n),← (hmass n).2]
    exact integral_mono_ae (hmass n).1 hsub.1 (cheegerHeat_order h ht (us n) u (hle n))
  exact le_of_tendsto (integral_radialCutoff_tendsto o hi) (Eventually.of_forall hbound)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_DriftResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile148
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def driftResolvent (h : QuadraticCheegerEnergy m) {τ : ℝ} (hτ : 0 < τ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  τ • ((cheeger_closedQuadraticEnergy h).scale hτ).resolventLinear

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma driftResolvent_formGenerator (h : QuadraticCheegerEnergy m) {τ : ℝ} (hτ : 0 < τ) (u : Lp ℝ 2 m) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator (driftResolvent h hτ u)
      (τ⁻¹ • driftResolvent h hτ u-u) := by
  let Q := cheeger_closedQuadraticEnergy h
  change Q.IsFormGenerator (τ • (Q.scale hτ).resolvent u)
    (τ⁻¹ • (τ • (Q.scale hτ).resolvent u)-u)
  rw [smul_smul,inv_mul_cancel₀ hτ.ne',one_smul]
  have H := Q.formGenerator_smul τ ((Q.scaled_resolvent_iff hτ u ((Q.scale hτ).resolvent u)).mp rfl)
  simpa only [smul_smul,mul_inv_cancel₀ hτ.ne',one_smul] using H

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.driftResolvent_isLaplacian {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (o : X) {τ : ℝ} (hτ : 0 < τ) (u : Lp ℝ 2 m) :
    IsLaplacian m (driftResolvent h hτ u) (τ⁻¹ • driftResolvent h hτ u-u : Lp ℝ 2 m) :=
  hcd.global_isLaplacian_of_formGenerator hfin o h _ _ (driftResolvent_formGenerator h hτ u)

end WeakHessian

end
end InlinedFile148

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

lemma IsLaplacian.unique (hfinite : FiniteOnBoundedSets m) {f L M : X → ℝ}
    (hL : IsLaplacian m f L) (hM : IsLaplacian m f M) : L =ᵐ[m] M := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
      hfinite _ Metric.isBounded_ball⟩⟩
  have hzero : (fun x => L x - M x) =ᵐ[m] 0 := by
    apply WeakHessianCalculus.ae_eq_zero_of_integral_lipschitz_compact
      ((hL.2.1.sub hM.2.1).locallyIntegrable (by norm_num))
    intro φ hc hφ
    obtain ⟨C, hC⟩ := hφ
    have hS := sobolev_of_lipschitz_compactSupport hfinite hC hc
    have hI : Integrable (fun x => L x * φ x) m := hL.2.1.integrable_mul hS.1
    have hJ : Integrable (fun x => M x * φ x) m := hM.2.1.integrable_mul hS.1
    change (∫ x, (L x - M x) * φ x ∂m) = 0
    simp_rw [sub_mul]
    rw [integral_sub hI hJ]
    have heq := (hL.2.2 φ hS).symm.trans (hM.2.2 φ hS)
    linarith
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

lemma IsLaplacian.ae_laplacian (hfinite : FiniteOnBoundedSets m) {f L : X → ℝ}
    (hf : IsLaplacian m f L) : laplacian m f =ᵐ[m] L :=
  (laplacian_isLaplacian ⟨L,hf⟩).unique hfinite hf

end WeakHessian

end
end InlinedFile110

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

variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

def CurvatureDimension.heatProbability {K N : ℝ} (hcd : CurvatureDimension m K N)
    (hN : 1 < N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hm : ∫ x,u x ∂m = 1) (t : ℝ) : ProbabilityMeasure X :=
  integrableDensityProbability (cheegerHeat h (max t 0) u)
    (cheegerHeat_nonneg h (le_max_right _ _) u hun)
    ((hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hun (integrable_of_integral_eq_one hm) (le_max_right _ _)).2.trans hm)

end WeakHessian

end
end InlinedFile75

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TestLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile128
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

omit [ProperSpace X] in
lemma IsLaplacian.add (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v A B : X → ℝ} (hu : IsLaplacian m u A) (hv : IsLaplacian m v B) :
    IsLaplacian m (fun x => u x+v x) (fun x => A x+B x) := by
  refine ⟨hu.1.add hfin hv.1,hu.2.1.add hv.2.1,?_⟩
  intro w hw
  have h1 := hu.2.2 w hw
  have h2 := hv.2.2 w hw
  have he := integral_congr_ae (gamma_add_left hfin hpar hu.1.2.1 hv.1.2.1 hw.2.1)
  rw [integral_add (integrable_gamma hfin hu.1 hw) (integrable_gamma hfin hv.1 hw)] at he
  rw [he]
  have hr : (∫ x,(A x+B x)*w x ∂m) = (∫ x,A x*w x ∂m)+(∫ x,B x*w x ∂m) := by
    simp_rw [add_mul]
    exact integral_add (hu.2.1.integrable_mul hw.1) (hv.2.1.integrable_mul hw.1)
  rw [hr]
  linarith

lemma IsTestFunction.add (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v : X → ℝ} (hu : IsTestFunction m u) (hv : IsTestFunction m v) :
    IsTestFunction m (fun x => u x+v x) := by
  have hgen := (laplacian_isLaplacian hu.1).add hfin hpar (laplacian_isLaplacian hv.1)
  obtain ⟨B,hB⟩ := hu.2.1
  obtain ⟨C,hC⟩ := hv.2.1
  obtain ⟨L,hL⟩ := hu.2.2.1
  obtain ⟨M,hM⟩ := hv.2.2.1
  refine ⟨⟨_,hgen⟩,⟨B+C,fun x => (abs_add_le _ _).trans (add_le_add (hB x) (hC x))⟩,
    ⟨L+M,hL.add hM⟩,?_⟩
  exact (sobolev_congr_ae (hgen.ae_laplacian hfin)).mpr (hu.2.2.2.add hfin hv.2.2.2)

end WeakHessian

end
end InlinedFile128

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_FormGamma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile163
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
variable {K N : ℝ} (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
variable (h : QuadraticCheegerEnergy m) (o : X) {χ : X → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)

include hcd hfin o in
omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.sobolev_formDomain (u : (cheeger_closedQuadraticEnergy h).domain) :
    Sobolev m ((u : Lp ℝ 2 m) : X → ℝ) := by
  exact (hcd.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp (u : Lp ℝ 2 m))).mpr u.property

def CurvatureDimension.formGammaLp :
    (cheeger_closedQuadraticEnergy h).domain →ₗ[ℝ] Lp ℝ 2 m where
  toFun u := (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ
    (hcd.sobolev_formDomain hfin h o u)).toLp (gamma m χ (u : Lp ℝ 2 m))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o (u+v))),
      MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)),
      MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o v)),
      Lp.coeFn_add ((memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)).toLp _)
        ((memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o v)).toLp _),
      gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl (Lp.coeFn_add (u : Lp ℝ 2 m) (v : Lp ℝ 2 m)),
      gamma_add_right hfin (hcd.global_localGradientParallelogram hfin o h) (localSobolev_of_lipschitz hfin hχ)
        (hcd.sobolev_formDomain hfin h o u).2.1 (hcd.sobolev_formDomain hfin h o v).2.1] with x ha hb hc hd he hf
    simp only [ha,hd,Pi.add_apply,hb,hc]
    exact (he.trans hf)
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o (c • u))),
      MemLp.coeFn_toLp (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)),
      Lp.coeFn_smul c ((memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hχ (hcd.sobolev_formDomain hfin h o u)).toLp _),
      gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl (Lp.coeFn_smul c (u : Lp ℝ 2 m)),
      gamma_const_mul_right hfin (hcd.global_localGradientParallelogram hfin o h) (localSobolev_of_lipschitz hfin hχ)
        (hcd.sobolev_formDomain hfin h o u).2.1 c] with x ha hb hc hd he
    simp only [ha,hc,Pi.smul_apply,smul_eq_mul,hb,RingHom.id_apply]
    exact hd.trans he

end WeakHessian

end
end InlinedFile163

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LaplacianLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile165
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_zero_on_const_set (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {χ v : X → ℝ} (hχ : LocalSobolev m χ) (hv : LocalSobolev m v)
    {S : Set X} (hS : MeasurableSet S) {c : ℝ} (hc : ∀ᵐ x ∂m,x ∈ S → χ x=c) :
    ∀ᵐ x ∂m,x ∈ S → gamma m χ v x=0 := by
  have hcS : LocalSobolev m (fun _ : X => c) := localSobolev_of_lipschitz hfin (LipschitzWith.const c)
  filter_upwards [weakGradient_locality hχ hcS hS hc,weakGradient_const (m := m) c,
    abs_gamma_le hfin hpar hχ hv] with x h1 h2 h3 hx
  apply abs_nonpos_iff.mp
  simpa only [h1 hx,h2,zero_mul] using h3

end WeakHessian

end
end InlinedFile165

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TestScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile170
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [ProperSpace X] in
lemma IsLaplacian.const_mul (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u A : X → ℝ} (hu : IsLaplacian m u A) (c : ℝ) :
    IsLaplacian m (fun x => c*u x) (fun x => c*A x) := by
  refine ⟨hu.1.const_mul c,hu.2.1.const_mul c,?_⟩
  intro w hw
  rw [integral_congr_ae (gamma_const_mul_left hfin hpar hu.1.2.1 hw.2.1 c),integral_const_mul,
    hu.2.2 w hw]
  simp_rw [mul_assoc c]
  rw [integral_const_mul]
  ring

lemma IsTestFunction.const_mul (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u : X → ℝ} (hu : IsTestFunction m u) (c : ℝ) : IsTestFunction m (fun x => c*u x) := by
  have hg := (laplacian_isLaplacian hu.1).const_mul hfin hpar c
  obtain ⟨B,hB⟩ := hu.2.1
  refine ⟨⟨_,hg⟩,⟨|c| * B,fun x => ?_⟩,hu.2.2.1.const_mul c,?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg _)
  · exact (sobolev_congr_ae (hg.ae_laplacian hfin)).mpr (hu.2.2.2.const_mul c)

omit [ProperSpace X] in
lemma isLaplacian_zero (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m) :
    IsLaplacian m (0 : X → ℝ) 0 := by
  have hs : Sobolev m (0 : X → ℝ) :=
    sobolev_of_lipschitz_compactSupport hfin (LipschitzWith.const 0) HasCompactSupport.zero
  refine ⟨hs,MemLp.zero,?_⟩
  intro w hw
  have hz : gamma m (0 : X → ℝ) w =ᵐ[m] 0 := by
    filter_upwards [gamma_zero_on_const_set hfin hpar hs.2.1 hw.2.1 MeasurableSet.univ
      (c := 0) (ae_of_all _ fun x hx => rfl)] with x hx
    exact hx (mem_univ x)
  rw [integral_congr_ae hz]
  simp only [Pi.zero_apply,zero_mul,integral_zero,neg_zero]

lemma isTestFunction_zero (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m) :
    IsTestFunction m (0 : X → ℝ) := by
  have hg := isLaplacian_zero hfin hpar
  refine ⟨⟨0,hg⟩,⟨0,fun x => by simp⟩,⟨0,LipschitzWith.const 0⟩,?_⟩
  exact (sobolev_congr_ae (hg.ae_laplacian hfin)).mpr hg.1
end WeakHessian

end
end InlinedFile170

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_CompactGeneratorRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile171
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def compactGeneratorRange (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m) :
    Submodule ℝ (Lp ℝ 2 m) where
  carrier := {f | ∃ g : X → ℝ,IsTestFunction m g ∧ HasCompactSupport g ∧
    ∃ u A : Lp ℝ 2 m,g =ᵐ[m] u ∧ IsLaplacian m g A ∧ f = u-A}
  zero_mem' := by
    refine ⟨0,isTestFunction_zero hfin hpar,HasCompactSupport.zero,0,0,
      (Lp.coeFn_zero ℝ 2 m).symm,?_,by simp⟩
    exact (isLaplacian_zero hfin hpar).congr_ae EventuallyEq.rfl (Lp.coeFn_zero ℝ 2 m).symm
  add_mem' := by
    rintro f j ⟨g,hg,hgc,u,A,hge,hgA,rfl⟩ ⟨k,hk,hkc,v,B,hke,hkB,rfl⟩
    refine ⟨fun x => g x+k x,hg.add hfin hpar hk,hgc.add hkc,u+v,A+B,?_,?_,by abel⟩
    · filter_upwards [hge,hke,Lp.coeFn_add u v] with x hx hy hz
      simpa only [Pi.add_apply,hx,hy] using hz.symm
    · exact (hgA.add hfin hpar hkB).congr_ae EventuallyEq.rfl (Lp.coeFn_add A B).symm
  smul_mem' := by
    rintro c f ⟨g,hg,hgc,u,A,hge,hgA,rfl⟩
    refine ⟨fun x => c*g x,hg.const_mul hfin hpar c,hgc.mul_left,c • u,c • A,?_,?_,smul_sub c u A⟩
    · filter_upwards [hge,Lp.coeFn_smul c u] with x hx hy
      simpa only [Pi.smul_apply,smul_eq_mul,hx] using hy.symm
    · exact (hgA.const_mul hfin hpar c).congr_ae EventuallyEq.rfl (Lp.coeFn_smul c A).symm

end WeakHessian

end
end InlinedFile171

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EnergyIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile182
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable (hfin : FiniteOnBoundedSets m)
variable (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
  ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))

include hfin hID

lemma identified_sobolev_iff_energy {f : X → ℝ} :
    Sobolev m f ↔ cheegerEnergy m f < ∞ := by
  constructor
  · intro hf
    rw [hID f hf]
    exact ENNReal.ofReal_lt_top
  · exact sobolev_of_cheegerEnergy_lt_top hfin

lemma identified_integral_gamma_eq {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    (∫ x,gamma m f g x ∂m) =
      ((cheegerEnergy m (fun x => f x+g x)).toReal-
        (cheegerEnergy m (fun x => f x-g x)).toReal)/2 := by
  have hp := hf.add hfin hg
  have hn := hf.sub hfin hg
  simp only [gamma,integral_div,integral_sub hp.2.2.integrable_sq hn.2.2.integrable_sq,
    identified_cheegerEnergy_toReal hID hp,identified_cheegerEnergy_toReal hID hn]
  ring

lemma identified_integral_gamma_form (h : QuadraticCheegerEnergy m)
    (f g : (cheeger_closedQuadraticEnergy h).domain) :
    (∫ x,gamma m (f.val : X → ℝ) (g.val : X → ℝ) x ∂m) =
      2*(cheeger_closedQuadraticEnergy h).form f g := by
  have hf := (identified_sobolev_iff_energy hfin hID).mpr f.property
  have hg := (identified_sobolev_iff_energy hfin hID).mpr g.property
  rw [identified_integral_gamma_eq hfin hID hf hg,ClosedQuadraticEnergy.form_apply]
  simp only [energyPolar,ClosedQuadraticEnergy.realEnergy,Submodule.coe_add,
    Submodule.coe_sub,cheegerEnergy_congr_ae (Lp.coeFn_add f.val g.val),
    cheegerEnergy_congr_ae (Lp.coeFn_sub f.val g.val)]
  change ((cheegerEnergy m (fun x => f.val x+g.val x)).toReal-
    (cheegerEnergy m (fun x => f.val x-g.val x)).toReal)/2 =
    2*(((cheegerEnergy m (fun x => f.val x+g.val x)).toReal-
      (cheegerEnergy m (fun x => f.val x-g.val x)).toReal)/4)
  ring

lemma identified_isLaplacian_of_formGenerator (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) :
    IsLaplacian m (u : X → ℝ) A := by
  refine ⟨(identified_sobolev_iff_energy hfin hID).mpr hu.1,Lp.memLp A,?_⟩
  intro v hv
  let v' := hv.1.toLp v
  have hv' : cheegerEnergy m (v' : X → ℝ) < ∞ := by
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (identified_sobolev_iff_energy hfin hID).mp hv
  have heq := identified_integral_gamma_form hfin hID h ⟨u,hu.1⟩ ⟨v',hv'⟩
  have heq' := hu.2 ⟨v',hv'⟩
  calc
    (∫ x,gamma m (u : X → ℝ) v x ∂m) =
        ∫ x,gamma m (u : X → ℝ) (v' : X → ℝ) x ∂m :=
      integral_congr_ae (gamma_congr_ae EventuallyEq.rfl hv.1.coeFn_toLp.symm)
    _ = -⟪A,v'⟫_ℝ := heq.trans heq'
    _ = -(∫ x,A x*v x ∂m) := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hv.1.coeFn_toLp] with x hx
      change v' x*A x=A x*v x
      rw [show v' x=v x from hx]
      exact mul_comm _ _
end WeakHessian

end
end InlinedFile182

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_LaplacianResolventUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile153
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.sub (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u v A B : X → ℝ}
    (hu : IsLaplacian m u A) (hv : IsLaplacian m v B) :
    IsLaplacian m (fun x => u x-v x) (fun x => A x-B x) := by
  refine ⟨hu.1.sub hfinite hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro z hz
  rw [integral_congr_ae (gamma_sub_left hfinite hpar hu.1.2.1 hv.1.2.1 hz.2.1),
    integral_sub (integrable_gamma hfinite hu.1 hz) (integrable_gamma hfinite hv.1 hz),
    hu.2.2 z hz,hv.2.2 z hz]
  simp_rw [sub_mul]
  have hiA : Integrable (fun x => A x*z x) m := hu.2.1.integrable_mul hz.1
  have hiB : Integrable (fun x => B x*z x) m := hv.2.1.integrable_mul hz.1
  rw [integral_sub hiA hiB]
  ring

end WeakHessian

end
end InlinedFile153

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DriftPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile149
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]
variable {K N : ℝ} (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
variable (h : QuadraticCheegerEnergy m) (o : X) {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
variable {τ : ℝ} (hτ : 0 < τ)

def CurvatureDimension.driftPerturbation (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (memLp_gamma_of_lipschitz hfin (hcd.global_localGradientParallelogram hfin o h) hV
    (hcd.driftResolvent_isLaplacian hfin h o hτ u).1).toLp (gamma m V (driftResolvent h hτ u))

end WeakHessian

end
end InlinedFile149

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_VariableDuhamelClosure
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
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def HeatVariableDissipation {m : Measure X} (h : QuadraticCheegerEnergy m)
    (k : X → ℝ) (f ξ : Lp ℝ 2 m) (T : ℝ) : Prop :=
  IntervalIntegrable (fun s => ∫ x, (cheegerHeat h s ξ x*k x)*
    gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m) volume 0 T ∧
  2*(∫ s in 0..T, ∫ x, (cheegerHeat h s ξ x*k x)*
    gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m) ≤
      (∫ x, cheegerHeat h T ξ x*gamma m f f x ∂m) -
      (∫ x, ξ x*gamma m (cheegerHeat h T f) (cheegerHeat h T f) x ∂m)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatBridge
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
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

def heatBridgeEnergy (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (T s : ℝ) : ℝ :=
  ∫ x,cheegerHeat h s ξ x*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m

def heatBridgeError (h : QuadraticCheegerEnergy m) (f ξ : Lp ℝ 2 m) (J : X → ℝ) (T s : ℝ) : ℝ :=
  ∫ x,(cheegerHeat h s ξ x*J x)*gamma m (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂m

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_PlanHeatEntropy
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
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

noncomputable def compactHopfDualBound (hfin : FiniteOnBoundedSets m) (o : X)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) : ℝ :=
  (compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)).choose_spec.choose

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_IdentifiedConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile216
noncomputable section
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma identified_cheegerHeat_davies_generator
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (_origin : X)
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
    have hG := identified_isLaplacian_of_formGenerator hfinite hID h (cheegerHeat h s u)
      (cheegerHeat h s A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu s)
    have HD := hG.davies_form hfinite (hpar) hV hB
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

lemma identified_cheegerResolvent_davies
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (_origin : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) (hsmall : t*(L:ℝ)^2 < 1) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB
        (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u)‖ ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖/(1-t*(L:ℝ)^2) := by
  let Q := cheeger_closedQuadraticEnergy h
  let v := (Q.scale ht).resolvent u
  let A := t⁻¹ • (v-u)
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hu : Q.IsFormGenerator v A := (Q.scaled_resolvent_iff ht u v).mp rfl
  have hG := identified_isLaplacian_of_formGenerator hfinite hID h v A hu
  have HD := hG.davies_form hfinite (hpar) hV hB
  rw [← expMulLp_inner hV.continuous.aestronglyMeasurable hB v A,
    ← expMulLp_norm_sq hV.continuous.aestronglyMeasurable hB v] at HD
  change ⟪T v,T A⟫_ℝ ≤ (L:ℝ)^2*‖T v‖^2 at HD
  have he : ⟪T v,T A⟫_ℝ = t⁻¹*(‖T v‖^2-⟪T v,T u⟫_ℝ) := by
    simp only [A,map_smul,map_sub,real_inner_smul_right,inner_sub_right,real_inner_self_eq_norm_sq]
  rw [he] at HD
  have HC := real_inner_le_norm (T v) (T u)
  have HI := mul_le_mul_of_nonneg_left HD ht.le
  rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at HI
  change ‖T v‖ ≤ ‖T u‖/(1-t*(L:ℝ)^2)
  rw [le_div_iff₀ (sub_pos.mpr hsmall)]
  by_cases hv : ‖T v‖ = 0
  · simp only [hv,zero_mul]; positivity
  · have hvp : 0 < ‖T v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith

lemma identified_cheegerResolvent_weighted
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) (hsmall : t*(L:ℝ)^2 < 1) :
    MemLp (fun x => (((cheeger_closedQuadraticEnergy h).scale ht).resolventLinear u) x*
      Real.exp (V x)) 2 m := by
  apply (memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable _ (B :=
    (‖hU.toLp (fun x => u x*Real.exp (V x))‖/(1-t*(L:ℝ)^2))^2) ?_).1
  intro n
  have HD := identified_cheegerResolvent_davies hID hpar hfinite o h u ht (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) hsmall
  have HU := expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n
  have H := HD.trans (div_le_div_of_nonneg_right HU (sub_pos.mpr hsmall).le)
  exact pow_le_pow_left₀ (norm_nonneg _) H 2

lemma identified_cheegerHeat_davies
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
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
    exact identified_cheegerHeat_davies_generator hID hpar hfinite o h (Q.isFormGenerator_resolvent w) hV hB ht
  · exact isClosed_le ((T.continuous.comp (cheegerHeat h t).continuous).norm.pow 2)
      ((T.continuous.norm.pow 2).mul_const _)

lemma identified_cheegerHeat_weighted
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun x => cheegerHeat h t u x*Real.exp (V x)) 2 m ∧
      (∫ x, (cheegerHeat h t u x*Real.exp (V x))^2 ∂m) ≤
        ‖hU.toLp (fun x => u x*Real.exp (V x))‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  apply memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
  intro n
  have H := identified_cheegerHeat_davies hID hpar hfinite o h u (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) ht
  exact H.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n) 2)
    (Real.exp_pos _).le)

end WeakHessian

end
end InlinedFile216

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalizedCertificate
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
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def localizedHeatError {m : Measure X} (h : QuadraticCheegerEnergy m) (ξ : Lp ℝ 2 m)
    (G : X → ℝ) (K a c CG T : ℝ) (f : Lp ℝ 2 m) : ℝ :=
  (2*a/localizedHeatDen K a c CG T)*(∫ s in 0..T,heatBridgeError h f ξ (fun x => max (G x-c) 0) T s)

end WeakHessian

end
end

end OAI
end


