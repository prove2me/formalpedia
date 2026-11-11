-- Prove2me | Definitions.Def_OAIQ239Tc025
-- name    : OAIQ239Tc025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:50.617035+00:00
-- url     : https://prove2.me/theorems/979fd5b4-a29e-4e6a-b674-c485a51dcc65
-- title:
--   Definitions bundle OAIQ239Tc025 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 25 definitions, 1 instance and 25 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.Hermitian.transversePairKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.gammaTailKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.gammaWedgeTailKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.heatEvaluation`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.heatEvaluationVector`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingEvaluation`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingEvaluationTerm`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingEvaluationVector`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatEvaluation`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatVector`, `OAI.TamingCompatibility.GeometricHilbert.LocalHodgeSmoothing.representative`, `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiEnergyDualLM`, `OAI.TamingCompatibility.GeometricHilbert.antiGraph`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy`, `OAI.TamingCompatibility.GeometricHilbert.energyInclusion`, `OAI.TamingCompatibility.GeometricHilbert.energyToH1`, `OAI.TamingCompatibility.GeometricHilbert.energyToScalarJet`, `OAI.TamingCompatibility.GeometricHilbert.hodgeBoundedSpectralMultiplier`, `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaShift`, `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaShiftLinear`, `OAI.TamingCompatibility.GeometricHilbert.hodgeHeatBoost`, `OAI.TamingCompatibility.GeometricHilbert.hodgeHeatDiagonal`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSpectralHeat`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_DifferentialForms_AntiEnergy`, `TamingCompatibility_DifferentialForms_ScalarJet`, `TamingCompatibility_DifferentialForms_UnitTransversePair`, `TamingCompatibility_Elliptic_AntiChartH1`, `TamingCompatibility_Functional_GeometricCompact`, `TamingCompatibility_Functional_RadialEnergyDual`, `TamingCompatibility_HeatFlow_HodgeHeatEvaluation`, `TamingCompatibility_HeatFlow_HodgeHeatSmoothing`, `TamingCompatibility_HeatFlow_HodgePairingHeat`, `TamingCompatibility_HeatFlow_HodgeResolventParameters`, `TamingCompatibility_HeatFlow_HodgeSpectralHeat`, `TamingCompatibility_Hodge_HodgeCutoffIntegral`, `TamingCompatibility_Hodge_HodgeFrameH1`, `TamingCompatibility_Hodge_HodgeH1`, `TamingCompatibility_Hodge_HodgeLocalCodifferential`, `TamingCompatibility_Hodge_HodgeLocalEvaluation`, `TamingCompatibility_Hodge_HodgePairingIntegral`, `TamingCompatibility_Hodge_HodgeScalarJet`, `TamingCompatibility_Hodge_HodgeScaleSmoothing`, `TamingCompatibility_Hodge_HodgeSmoothSpatial`, `TamingCompatibility_Hodge_HodgeWedgeTail`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc021`, `OAIQ239Tc022` and `OAIQ239Tc023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc028` and `OAIQ239Tc029`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatVector_star`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_variation_limit` and `OAI.TamingCompatibility.GeometricHilbert.Hermitian.separating_probability_transverse_product_limit`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Definitions.Def_OAIQ239Tc022
import Definitions.Def_OAIQ239Tc023

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def antiGraph : antiPre A J α hs ht →ₗ[ℝ]
    WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false) :=
  (WithLp.linearEquiv 2 ℝ (L2 A J α hs ht true × L2 A J α hs ht false)).symm.toLinearMap.comp <|
  ((smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype).prod
    ((smoothL2 A J α hs ht false).toLinearMap.comp (antiDelta A J α hs ht))

def antiEnergy : Submodule ℝ (WithLp 2 (L2 A J α hs ht true × L2 A J α hs ht false)) :=
  (LinearMap.range (antiGraph A J α hs ht)).topologicalClosure

instance antiEnergy_complete : CompleteSpace (antiEnergy A J α hs ht) :=
  ((LinearMap.range (antiGraph A J α hs ht)).isClosed_topologicalClosure).completeSpace_coe

end GeometricHilbert
end TamingCompatibility

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_AntiChartH1
attribute [-instance] _root_.OAI.TamingCompatibility.Fredholm.instCompleteSpaceSubtypeMemSubmoduleRealNullspace _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma antiGraph_norm_sq (a : antiPre A J α hs ht) :
    ‖antiGraph A J α hs ht a‖^2 =
      (∫ x, GeometricAdjoint.pairing J α ht a.val.val a.val.val x ∂ManifoldVolume.geometricVolume A J α) +
      (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val.val)
        (codifferential J α ht a.val.val) x ∂ManifoldVolume.geometricVolume A J α) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖smoothL2 A J α hs ht true a.val‖^2 +
    ‖smoothL2 A J α hs ht false (antiDelta A J α hs ht a)‖^2 = _
  rw [(smoothL2 A J α hs ht true).norm_map,(smoothL2 A J α hs ht false).norm_map,
    preL2_norm_sq,preL2_norm_sq]
  rfl

def antiToEnergy : antiPre A J α hs ht →ₗ[ℝ] antiEnergy A J α hs ht :=
  ClosureLinear.toClosure (antiGraph A J α hs ht)

lemma antiToEnergy_dense : DenseRange (antiToEnergy A J α hs ht) :=
  ClosureLinear.toClosure_dense (antiGraph A J α hs ht)

def energyToH1 : antiEnergy A J α hs ht →L[ℝ] globalH1 A 2 :=
  (antiToH1 A J α hs ht).extendOfNorm (antiToEnergy A J α hs ht)

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma scalarToJet_bound (p : A.centers) : ∃ C : ℝ, ∀ a : antiPre A J α hs ht,
    ‖scalarToJet A J α hs ht D hD p a‖ ≤ C * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨Real.sqrt (20*C),fun a => ?_⟩
  have h := ScalarPair.make_jet_bound (scalarSchwartz A J α ht D hD p a.val.val a.val.property 2)
    (scalarSchwartz A J α ht D hD p a.val.val a.val.property 3)
  have hga := hb a.val.val a.val.property a.property
  rw [← antiGraph_norm_sq A J α hs ht a] at hga
  change (∫ z, EuclideanEnergy.gradientEnergy (scalarSchwartz A J α ht D hD p a.val.val a.val.property 2)
    (scalarSchwartz A J α ht D hD p a.val.val a.val.property 3) z) +
    (∫ z, (scalarSchwartz A J α ht D hD p a.val.val a.val.property 2 z)^2 +
      (scalarSchwartz A J α ht D hD p a.val.val a.val.property 3 z)^2) ≤
      C * ‖antiToEnergy A J α hs ht a‖^2 at hga
  have hn : ‖scalarToJet A J α hs ht D hD p a‖^2 ≤ 20*C*‖antiToEnergy A J α hs ht a‖^2 := by
    exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hga (show (0:ℝ) ≤ 20 by norm_num))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 20*C)]
  exact hn

def energyToScalarJet (p : A.centers) : antiEnergy A J α hs ht →L[ℝ] ScalarPair.Jet :=
  (scalarToJet A J α hs ht D hD p).extendOfNorm (antiToEnergy A J α hs ht)

lemma energyToScalarJet_smooth (p : A.centers) (a : antiPre A J α hs ht) :
    energyToScalarJet A J α hs ht D hD p (antiToEnergy A J α hs ht a) = scalarToJet A J α hs ht D hD p a :=
  LinearMap.extendOfNorm_eq (antiToEnergy_dense A J α hs ht) (scalarToJet_bound A J α hs ht D hD p) a

lemma energy_scalar_derivative (p : A.centers) (u : antiEnergy A J α hs ht)
    (i : Fin (Module.finrank ℝ Space)) :
    LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,ScalarPair.F) (stdOrthonormalBasis ℝ Space i)
      (ScalarPair.jetDistribution none (energyToScalarJet A J α hs ht D hD p u)) =
      ScalarPair.jetDistribution (some i) (energyToScalarJet A J α hs ht D hD p u) := by
  let L := LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,ScalarPair.F) (stdOrthonormalBasis ℝ Space i) ∘L
    ScalarPair.jetDistribution none ∘L energyToScalarJet A J α hs ht D hD p
  let R := ScalarPair.jetDistribution (some i) ∘L energyToScalarJet A J α hs ht D hD p
  exact (antiToEnergy_dense A J α hs ht).induction_on u (isClosed_eq L.continuous R.continuous) (fun a => by
    change L (antiToEnergy A J α hs ht a) = R (antiToEnergy A J α hs ht a)
    dsimp only [L,R,ContinuousLinearMap.comp_apply]
    rw [energyToScalarJet_smooth]
    exact ScalarPair.jet_derivative _ i)
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricCompact
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def energyInclusion : antiEnergy A J α hs ht →L[ℝ] L2 A J α hs ht true :=
  (WithLp.fstL 2 ℝ _ _) ∘L (antiEnergy A J α hs ht).subtypeL

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RadialEnergyDual
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def antiEnergyDualLM : antiPre A J α hs ht →ₗ[ℝ] StrongDual ℝ (antiEnergy A J α hs ht) where
  toFun f := (innerSL ℝ (smoothL2 A J α hs ht true f.val)).comp (energyInclusion A J α hs ht)
  map_add' f g := by ext u; simp
  map_smul' c f := by ext u; simp

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalCodifferential
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricChart
open Set _root_.MeasureTheory ContinuousAlternatingMap
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (hs : IsSmooth α)

include hs hD in
lemma system_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a, ∀ z,
      ‖system A J α ht D hD p a ha z‖^2 ≤ C *
      (coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z +
      coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))
        (codifferential J α ht (cutoffForm A p (starTwo J α ht a)))) z) := by
  obtain ⟨C,hC,hbound⟩ := density_lower_on_support A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a ha z
  by_cases hz : z ∈ coordinateSupport A p
  · rw [← system_energy A J α ht D hD hs p a ha hz]
    have hh := mul_le_mul_of_nonneg_right (hbound z hz) (sq_nonneg ‖system A J α ht D hD p a ha z‖)
    nlinarith
  · rw [system_zero_off A J α ht D hD p a ha hz,norm_zero,zero_pow (by decide : 2≠0)]
    exact mul_nonneg hC.le (add_nonneg
      (coordinateIntegrand_self_nonneg J α ht p.val _ z)
      (coordinateIntegrand_self_nonneg J α ht p.val _ z))

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_system_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a,
      (∫ z, ‖system A J α ht D hD p a ha z‖^2) ≤ C *
      (∫ x, GeometricAdjoint.pairing J α ht
        (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a)) x +
      GeometricAdjoint.pairing J α ht
        (codifferential J α ht (starTwo J α ht (cutoffForm A p a)))
        (codifferential J α ht (starTwo J α ht (cutoffForm A p a))) x ∂geometricVolume A J α) := by
  obtain ⟨C,hC,hbound⟩ := system_norm_bound A J α ht D hD hs p
  refine ⟨C,hC,?_⟩
  intro a ha
  have hi₁ := localDelta_density_integrable A J α ht hs p ha
  have hi₂ := localDelta_density_integrable A J α ht hs p (starTwo_smooth J α hs ht ha)
  have hh := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg
    ‖system A J α ht D hD p a ha z‖)) ((hi₁.add hi₂).const_mul C)
    (Filter.Eventually.of_forall (hbound a ha))
  simp only [Pi.add_apply] at hh
  rw [integral_const_mul,integral_add hi₁ hi₂,
    integral_localDelta_density A J α ht hs p ha,
    integral_localDelta_density A J α ht hs p (starTwo_smooth J α hs ht ha)] at hh
  have hcut : starTwo J α ht (cutoffForm A p a) = cutoffForm A p (starTwo J α ht a) :=
    hodgeStar_fun_smul J α ht (A.partition p) a
  rw [hcut]
  let := geometricVolume_finite A J α hs ht
  have hd₁ := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
  have hd₂ := GeometricAdjoint.codifferential_smooth J α hs ht
    (cutoffForm_smooth A p (starTwo_smooth J α hs ht ha))
  rw [integral_add
    ((GeometricAdjoint.pairing_one_smooth J α hs ht hd₁ hd₁).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((GeometricAdjoint.pairing_one_smooth J α hs ht hd₂ hd₂).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  exact hh
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCutoffIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume EuclideanEnergy
open Set _root_.MeasureTheory GeometricChart
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hs in

theorem scalar_garding (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a,
      (∫ z, HodgeMatrixEnergy.gradient (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a ha) z) +
      (∫ z, ‖HodgeMatrixEnergy.value (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a ha) z‖^2) ≤
      C * ((∫ x, GeometricAdjoint.pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a)
          (codifferential J α ht a) x +
          GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a))
            (codifferential J α ht (starTwo J α ht a)) x ∂geometricVolume A J α)) := by
  obtain ⟨Cδ,hCδ,hδ⟩ := integral_system_bound A J α ht (fun q => (D q).toData) hD hs p
  obtain ⟨Cs,hCs,hS⟩ := integral_scalar_bound A J α hs ht (fun q => (D q).toData) hD p
  obtain ⟨Cf,hCf,hf⟩ := GeometricHilbert.full_cutoff_energy_bound A J α hs ht (A.partition p).contMDiff
  let K := (D p).fullEnergyConstant*Cδ + ((D p).fullLowerConstant+1)*Cs
  have hK : 0 < K := add_pos (mul_pos (D p).fullEnergy_pos hCδ)
    (mul_pos (by linarith [(D p).fullLower_pos]) hCs)
  refine ⟨K*Cf,mul_pos hK hCf,?_⟩
  intro a ha
  let f := scalarSchwartz A J α ht (fun q => (D q).toData) hD p a ha
  have hg := (D p).fullGarding f (fun j => scalarSchwartz_support A J α ht
    (fun q => (D q).toData) hD p a ha j)
  change (∫ z, HodgeMatrixEnergy.gradient f z) ≤ (D p).fullEnergyConstant *
    (∫ z, ‖system A J α ht (fun q => (D q).toData) hD p a ha z‖^2) + (D p).fullLowerConstant *
      (∫ z, ‖HodgeMatrixEnergy.value f z‖^2) at hg
  let L := ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a) (cutoffForm A p a) x ∂geometricVolume A J α
  let Q := ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a)) x +
    GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht (cutoffForm A p a)))
      (codifferential J α ht (starTwo J α ht (cutoffForm A p a))) x ∂geometricVolume A J α
  have hL : 0 ≤ L := integral_nonneg (fun x => MetricForms.pairing_self_nonneg _ _)
  have hQ : 0 ≤ Q := integral_nonneg (fun x => add_nonneg
    (MetricForms.pairing_self_nonneg _ _) (MetricForms.pairing_self_nonneg _ _))
  have hδa := hδ a ha
  have hSa := hS a ha
  change _ ≤ Cδ*Q at hδa
  change (∫ z, ‖HodgeMatrixEnergy.value f z‖^2) ≤ Cs*L at hSa
  have hfa := hf a ha
  change L+Q ≤ _ at hfa
  have hpre : (∫ z, HodgeMatrixEnergy.gradient f z) +
      (∫ z, ‖HodgeMatrixEnergy.value f z‖^2) ≤ K*(L+Q) := by
    have hd := mul_le_mul_of_nonneg_left hδa (D p).fullEnergy_pos.le
    have hsl := mul_le_mul_of_nonneg_left hSa (by linarith [(D p).fullLower_pos] : 0 ≤ (D p).fullLowerConstant+1)
    have he₁ := mul_nonneg (mul_pos (D p).fullEnergy_pos hCδ).le hL
    have he₂ := mul_nonneg (mul_pos (by linarith [(D p).fullLower_pos] : 0 < (D p).fullLowerConstant+1) hCs).le hQ
    dsimp only [K]
    nlinarith
  exact hpre.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfa hK.le)
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFrameH1
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume EuclideanEnergy
open Set _root_.MeasureTheory HodgeFrame GeometricChart
open scoped Manifold ContDiff SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hs hD in
omit [T2Space X] in

theorem localized_jet_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : smoothForms X 2,
      ∀ j : DerivativeIndex, ‖localizeH1 A 2 a j p‖^2 ≤
        C * ((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x +
            GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a.val))
              (codifferential J α ht (starTwo J α ht a.val)) x ∂geometricVolume A J α)) := by
  let P : Space → HodgeNormalSymbol.W →L[ℝ] CoordinateFiber 2 := fun x =>
    formCoordinates 2 ∘L reconstruct (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x)
  have hg := (coordinateMetric_smooth J α hs ht p.val).mono (D p).domain_subset
  have hP : ContDiffOn ℝ ∞ P (D p).domain := by
    apply contDiffOn_clm_apply.mpr
    intro u
    change ContDiffOn ℝ ∞ (fun x => formCoordinates 2 (∑ j, u j •
      basisForm (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) j)) (D p).domain
    apply (formCoordinates 2).contDiff.comp_contDiffOn
    exact ContDiffOn.sum (fun j _ => (basisForm_smooth hg (D p).frame_smooth j).const_smul (u j))
  obtain ⟨C,hC,hframe⟩ := HodgeMatrixEnergy.frame_h1_bound (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht (fun q => (D q).toData) hD p) P hP
  obtain ⟨K,hK,hgard⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨16*(C*K),mul_pos (by norm_num) (mul_pos hC hK),?_⟩
  intro a j
  let f := scalarSchwartz A J α ht (fun q => (D q).toData) hD p a.val a.property
  have he : (⇑(localizedLinear A 2 p a)) = fun x => P x (HodgeMatrixEnergy.value f x) := by
    funext x
    change formCoordinates 2 (localizedFunction A p a.val x) =
      formCoordinates 2 (reconstruct _ _ _)
    rw [scalar_expansion A J α ht (fun q => (D q).toData) hD p a.val x,reconstruct_apply]
    rfl
  have hb := hframe f (localizedLinear A 2 p a) (localizedLinear_support A p a) he
  have hga := hgard a.val a.property
  rw [localizeH1_apply,schwartz_l2_norm_sq]
  have hbound : C*((∫ x, HodgeMatrixEnergy.gradient f x)+(∫ x, ‖HodgeMatrixEnergy.value f x‖^2)) ≤
      C*K*((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x +
            GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a.val))
              (codifferential J α ht (starTwo J α ht a.val)) x ∂geometricVolume A J α)) :=
    (mul_le_mul_of_nonneg_left hga hC.le).trans_eq (mul_assoc _ _ _).symm
  have hnonneg : 0 ≤ C*((∫ x, HodgeMatrixEnergy.gradient f x)+(∫ x, ‖HodgeMatrixEnergy.value f x‖^2)) :=
    (integral_nonneg fun x => sq_nonneg ‖localizedLinear A 2 p a x‖).trans hb.1
  have htarget := mul_le_mul_of_nonneg_left hbound (show (0:ℝ) ≤ 16 by norm_num)
  cases j with
  | none => exact (hb.1.trans (by nlinarith : _ ≤ 16*(C*((∫ x, HodgeMatrixEnergy.gradient f x)+
        (∫ x, ‖HodgeMatrixEnergy.value f x‖^2))))).trans (by simpa only [mul_assoc] using htarget)
  | some i =>
    change (∫ x, ‖(∂_{stdOrthonormalBasis ℝ Space i} (localizedLinear A 2 p a)) x‖^2) ≤ _
    have hv : ‖stdOrthonormalBasis ℝ Space i‖ ≤ 1 := le_of_eq
      ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i)
    have hd := direction_integral_bound (localizedLinear A 2 p a)
      (stdOrthonormalBasis ℝ Space i) hv
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb.2 k)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_ofNat] at hsum
    exact (hd.trans (by nlinarith : _ ≤ 16*(C*((∫ x, HodgeMatrixEnergy.gradient f x)+
        (∫ x, ‖HodgeMatrixEnergy.value f x‖^2))))).trans (by simpa only [mul_assoc] using htarget)
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeH1
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hD in
lemma hodgeToH1_bound : ∃ C : ℝ, ∀ a : PreL2 A J α hs ht true,
    ‖hodgeToH1 A J α hs ht a‖ ≤ C * ‖hodgeSmooth A J α hs ht a‖ := by
  classical
  choose C hC hb using localized_jet_bound A J α hs ht D hD
  let B : ℝ := 1 + ∑ p : A.centers, C p
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ p : A.centers, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hcB (p : A.centers) : C p ≤ B :=
    (Finset.single_le_sum (fun p _ => (hC p).le) (Finset.mem_univ p)).trans
      (by change (∑ p : A.centers, C p) ≤ 1 + (∑ p : A.centers, C p); linarith)
  let N : ℝ := Fintype.card DerivativeIndex * Fintype.card A.centers
  have hN : 0 ≤ N := by dsimp [N] <;> positivity
  refine ⟨Real.sqrt (N*B),fun a => ?_⟩
  have hsq : ‖hodgeToH1 A J α hs ht a‖^2 ≤ N*B*‖hodgeSmooth A J α hs ht a‖^2 := by
    change ‖localizeH1 A 2 a‖^2 ≤ N*B*‖hodgeGraph A J α hs ht a‖^2
    simp only [PiLp.norm_sq_eq_of_L2]
    have hlocal (j : DerivativeIndex) (p : A.centers) :
        ‖localizeH1 A 2 a j p‖^2 ≤ B*‖hodgeGraph A J α hs ht a‖^2 := by
      have h := hb p a j
      rw [← hodgeGraph_norm_sq A J α hs ht a] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hcB p) (sq_nonneg _))
    calc
      _ ≤ ∑ j : DerivativeIndex, ∑ p : A.centers, B*‖hodgeGraph A J α hs ht a‖^2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun p _ => hlocal j p
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; dsimp [N] <;> ring
  have hroot : (Real.sqrt (N*B)*‖hodgeSmooth A J α hs ht a‖)^2 =
      N*B*‖hodgeSmooth A J α hs ht a‖^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hN hB.le)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp (hsq.trans_eq hroot.symm)

include hD in
lemma hodgeEnergyToH1_smooth (a : PreL2 A J α hs ht true) :
    hodgeEnergyToH1 A J α hs ht (hodgeSmooth A J α hs ht a) = hodgeToH1 A J α hs ht a :=
  LinearMap.extendOfNorm_eq (hodgeSmooth_dense A J α hs ht) (hodgeToH1_bound A J α hs ht D hD) a
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarJet
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart _root_.MeasureTheory
open EuclideanSobolevOperators TemperedDistribution
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeScalarToJet_bound (p : A.centers) : ∃ C : ℝ, ∀ a : PreL2 A J α hs ht true,
    ‖hodgeScalarToJet A J α hs ht D hD p a‖ ≤ C * ‖hodgeSmooth A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨Real.sqrt (20*C),fun a => ?_⟩
  have h := HodgeScalar.make_jet_bound (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a.val a.property)
  have hga := hb a.val a.property
  rw [← hodgeGraph_norm_sq A J α hs ht a] at hga
  have hn : ‖hodgeScalarToJet A J α hs ht D hD p a‖^2 ≤ 20*C*‖hodgeSmooth A J α hs ht a‖^2 := by
    change ‖HodgeScalar.jet (HodgeScalar.make (scalarSchwartz A J α ht (fun q => (D q).toData) hD p a.val a.property))‖^2 ≤ 20*C*‖hodgeGraph A J α hs ht a‖^2
    exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hga (show (0:ℝ) ≤ 20 by norm_num))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 20*C)]
  exact hn

lemma hodgeEnergyToScalarJet_smooth (p : A.centers) (a : PreL2 A J α hs ht true) :
    hodgeEnergyToScalarJet A J α hs ht D hD p (hodgeSmooth A J α hs ht a) =
      hodgeScalarToJet A J α hs ht D hD p a :=
  LinearMap.extendOfNorm_eq (hodgeSmooth_dense A J α hs ht) (hodgeScalarToJet_bound A J α hs ht D hD p) a
lemma hodge_energy_scalar_derivative (p : A.centers) (u : hodgeEnergy A J α hs ht)
    (i : Fin (Module.finrank ℝ Space)) :
    LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,HodgeScalar.F) (stdOrthonormalBasis ℝ Space i)
      (HodgeScalar.jetDistribution none (hodgeEnergyToScalarJet A J α hs ht D hD p u)) =
      HodgeScalar.jetDistribution (some i) (hodgeEnergyToScalarJet A J α hs ht D hD p u) := by
  let L := LineDeriv.lineDerivOpCLM ℝ 𝓢'(Space,HodgeScalar.F) (stdOrthonormalBasis ℝ Space i) ∘L
    HodgeScalar.jetDistribution none ∘L hodgeEnergyToScalarJet A J α hs ht D hD p
  let R := HodgeScalar.jetDistribution (some i) ∘L hodgeEnergyToScalarJet A J α hs ht D hD p
  exact (hodgeSmooth_dense A J α hs ht).induction_on u (isClosed_eq L.continuous R.continuous) (fun a => by
    change L (hodgeSmooth A J α hs ht a) = R (hodgeSmooth A J α hs ht a)
    dsimp only [L,R,ContinuousLinearMap.comp_apply]
    rw [hodgeEnergyToScalarJet_smooth]
    exact HodgeScalar.jet_derivative _ i)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

namespace LocalHodgeSmoothing
variable {A J α hs ht D hD} {p : A.centers} {q : Space} {r : ℝ} {hr : 0 < r}
variable (L : LocalHodgeSmoothing A J α hs ht D hD p q r hr)

def representative (f : L2 A J α hs ht true) : Space →ᵇ C 6 :=
  sobolevToBounded 5 (by norm_num [Space]) (L.lift f)

end LocalHodgeSmoothing
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hD in
lemma hodgeInclusion_factor : hodgeInclusion A J α hs ht =
    chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L hodgeEnergyToH1 A J α hs ht := by
  apply DFunLike.coe_injective
  apply (hodgeSmooth_dense A J α hs ht).equalizer
    (hodgeInclusion A J α hs ht).continuous
    (chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L hodgeEnergyToH1 A J α hs ht).continuous
  funext a
  change smoothL2 A J α hs ht true a =
    chartToMetric A J α hs ht (h1ToL2 A 2 (hodgeEnergyToH1 A J α hs ht (hodgeSmooth A J α hs ht a)))
  rw [hodgeEnergyToH1_smooth A J α hs ht D hD]
  exact (chartToMetric_smooth A J α hs ht (fun p => (D p).toData) hD a).symm

include hD in

theorem hodgeInclusion_compact : IsCompactOperator (hodgeInclusion A J α hs ht) := by
  rw [hodgeInclusion_factor A J α hs ht D hD]
  exact ((h1ToL2_compact A 2).comp_clm (hodgeEnergyToH1 A J α hs ht)).clm_comp
    (chartToMetric A J α hs ht)

include hD in

lemma hodgeResolvent_compact (r : ℝ) (hr : 0 < r) :
    IsCompactOperator (hodgeResolvent A J α hs ht r) := by
  rw [hodgeResolvent_eq A J α hs ht r hr]
  exact (hodgeInclusion_compact A J α hs ht D hD).comp_clm
    (hodgeWeakSolution A J α hs ht r hr)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

variable (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

lemma hodgeResolvent_eigenspaces_total :
    (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x)ᗮ = ⊥ := by
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (hodgeResolvent_compact A J α hs ht D hD 1 zero_lt_one)
    (hodgeResolvent_symmetric A J α hs ht 1)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeSpectralHeat
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include D hD in

theorem hodgeSpectralSum : IsHilbertSum ℝ
    (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x)
    (fun x => (Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal _ (hodgeResolvent_symmetric A J α hs ht 1).orthogonalFamily_eigenspaces
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    hodgeResolvent_eigenspaces_total A J α hs ht D hD]
  simp

def hodgeHeatDiagonal (t : ℝ) :
    lp (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x) 2 →L[ℝ]
    lp (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x) 2 :=
  lp.mapCLM 2 (fun x => hodgeHeatMultiplier t x • ContinuousLinearMap.id ℝ _) zero_le_one (by
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (hodgeHeatMultiplier_pos t x), one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one t x))

lemma hodgeHeatDiagonal_apply (t : ℝ)
    (f : lp (fun x : ℝ => Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x) 2)
    (x : ℝ) : hodgeHeatDiagonal A J α hs ht t f x = hodgeHeatMultiplier t x • f x := rfl

def hodgeSpectralHeat (t : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((hodgeHeatDiagonal A J α hs ht t).comp E.toContinuousLinearEquiv.toContinuousLinearMap)

lemma hodgeSpectralHeat_repr (t : ℝ) (f : L2 A J α hs ht true) (x : ℝ) :
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeSpectralHeat A J α hs ht D hD t f) x = hodgeHeatMultiplier t x •
        (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x := by
  change ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
    ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.symm
      (hodgeHeatDiagonal A J α hs ht t
        ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f)))) x = _
  rw [LinearIsometryEquiv.apply_symm_apply, hodgeHeatDiagonal_apply]

lemma hodgeSpectralHeat_norm_le (t : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeSpectralHeat A J α hs ht D hD t f‖ ≤ ‖f‖ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  rw [← E.norm_map (hodgeSpectralHeat A J α hs ht D hD t f), ← E.norm_map f]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  rw [hodgeSpectralHeat_repr, norm_smul, Real.norm_eq_abs,
    abs_of_pos (hodgeHeatMultiplier_pos t x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one t x)

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeSpectralHeat_continuous (f : L2 A J α hs ht true) :
    Continuous (fun t => hodgeSpectralHeat A J α hs ht D hD t f) := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  let v := E f
  let F := fun t => hodgeHeatDiagonal A J α hs ht t v
  have hc : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq (t : ℝ) : ‖F t - F t₀‖^2 =
        ∑' x : ℝ, ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2 := by
      have hh := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (F t-F t₀)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hh
      rw [hh]
      congr 1
      funext x
      change ‖hodgeHeatMultiplier t x • v x - hodgeHeatMultiplier t₀ x • v x‖^2 = _
      rw [← sub_smul]
    have hsum : Summable (fun x : ℝ => ‖v x‖^2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    have hb (x t : ℝ) :
        ‖‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2‖ ≤ ‖v x‖^2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ha : |hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x| ≤ 1 := by
        apply abs_le.mpr
        have h1 := hodgeHeatMultiplier_pos t x
        have h2 := hodgeHeatMultiplier_pos t₀ x
        have h3 := hodgeHeatMultiplier_le_one t x
        have h4 := hodgeHeatMultiplier_le_one t₀ x
        constructor <;> linarith
      have hn : ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖ ≤ ‖v x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) ha
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hcts : Continuous (fun t => ∑' x : ℝ,
        ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2) :=
      continuous_tsum (fun x => (((hodgeHeatMultiplier_continuous x).sub continuous_const).smul
        continuous_const).norm.pow 2) hsum hb
    have hlim := (Real.continuous_sqrt.comp hcts).tendsto t₀
    have hh : (fun t => Real.sqrt (∑' x : ℝ,
        ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2)) =
        (fun t => ‖F t-F t₀‖) := by
      funext t
      rw [← hsq t, Real.sqrt_sq (norm_nonneg _)]
    change Tendsto (fun t => Real.sqrt (∑' x : ℝ,
      ‖(hodgeHeatMultiplier t x - hodgeHeatMultiplier t₀ x) • v x‖^2)) _ _ at hlim
    rw [hh] at hlim
    change Tendsto (fun t => ‖F t-F t₀‖) (𝓝 t₀) (𝓝 (Real.sqrt
      (∑' x : ℝ, ‖(hodgeHeatMultiplier t₀ x-hodgeHeatMultiplier t₀ x) • v x‖^2))) at hlim
    simpa using hlim
  exact E.symm.continuous.comp hc

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeBoundedSpectralMultiplier (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun x => m x • ContinuousLinearMap.id ℝ _) hK (by
      intro x
      apply ContinuousLinearMap.opNorm_le_bound _ hK
      intro v
      simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _))).comp
      E.toContinuousLinearEquiv.toContinuousLinearMap)

def hodgeHeatBoost (r : ℝ) : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  hodgeBoundedSpectralMultiplier A J α hs ht D hD
    (fun x => (1+r^2*hodgeSpectralRate x)^3 * Real.exp (-(r^2*hodgeSpectralRate x)))
    (6 * Real.exp 1) (by positivity)
    (fun x => heat_boost_bound _ (mul_nonneg (sq_nonneg _) (le_max_left _ _)))

end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
variable {A J α hs ht D hD}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def heatEvaluation (u : MetricUnit g) : L2 A J α hs ht true →L[ℝ] ℝ :=
  (C.evaluation g u).comp (hodgeHeatBoost A J α hs ht D hD r)

def heatEvaluationVector (u : MetricUnit g) : L2 A J α hs ht true :=
  (C.heatEvaluation g u).adjoint 1

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

def pairingEvaluationTerm (b : PreL2 A J α hs ht true) (i : C.centers) (j : Fin 6) (x : X) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  GeometricAdjoint.pairing J α ht b.val (C.basisForm i j).val x •
    (EuclideanSpace.proj j).comp ((C.patch i).smoothing.realEvaluation
      (extChartAt Model (C.patch i).chart.val x))

def pairingEvaluation (b : PreL2 A J α hs ht true) (x : X) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  ∑ i : C.centers, ∑ j : Fin 6, C.pairingEvaluationTerm b i j x

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairingIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}

namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

def pairingEvaluationVector (b : PreL2 A J α hs ht true) (x : X) : L2 A J α hs ht true :=
  (C.pairingEvaluation b x).adjoint 1

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeGammaShift_integrable {T : ℝ} (hT : 0 ≤ T) (r δ : ℝ)
    (f : L2 A J α hs ht true) :
    IntegrableOn (fun s : ℝ => hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f) (Ioi (T/r^2)) := by
  have hc : Continuous (fun s : ℝ => hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f) := hodgeGammaWeight_continuous.smul
    ((hodgeSpectralHeat_continuous A J α hs ht D hD f).comp (by fun_prop))
  have hsub : Ioi (T/r^2) ⊆ Ioi (0:ℝ) := fun _ h => (div_nonneg hT (sq_nonneg r)).trans_lt h
  apply ((hodgeGammaWeight_integrable.mono_set hsub).mul_const ‖f‖).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
  have hs0 : 0 ≤ s := (hsub hsp).le
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs0)]
  exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
    (hodgeGammaWeight_nonneg hs0)

def hodgeGammaShiftLinear (T : ℝ) (hT : 0 ≤ T) (r δ : ℝ) :
    L2 A J α hs ht true →ₗ[ℝ] L2 A J α hs ht true where
  toFun f := (1/120 : ℝ) • ∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s •
    hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f
  map_add' f g := by
    simp only [map_add,smul_add]
    rw [integral_add (hodgeGammaShift_integrable A J α hs ht D hD hT r δ f)
      (hodgeGammaShift_integrable A J α hs ht D hD hT r δ g),smul_add]
  map_smul' c f := by
    simp only [map_smul,RingHom.id_apply,smul_comm (hodgeGammaWeight _) c]
    rw [integral_smul,smul_comm]

lemma hodgeGammaShiftLinear_bound (T : ℝ) (hT : 0 ≤ T) (r δ : ℝ)
    (f : L2 A J α hs ht true) :
    ‖hodgeGammaShiftLinear A J α hs ht D hD T hT r δ f‖ ≤
      (1/120 : ℝ) * HodgeKernelBounds.gammaTail (T/r^2)*‖f‖ := by
  have hsub : Ioi (T/r^2) ⊆ Ioi (0:ℝ) := fun _ h => (div_nonneg hT (sq_nonneg r)).trans_lt h
  have hi := hodgeGammaShift_integrable A J α hs ht D hD hT r δ f
  have hw := hodgeGammaWeight_integrable.mono_set hsub
  have hh : ‖∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s •
      hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f‖ ≤ HodgeKernelBounds.gammaTail (T/r^2)*‖f‖ := by
    calc
      _ ≤ ∫ s : ℝ in Ioi (T/r^2), ‖hodgeGammaWeight s •
          hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s*‖f‖ := by
        apply integral_mono_ae hi.norm (hw.mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
        have hs0 : 0 ≤ s := (hsub hsp).le
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs0)]
        exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
          (hodgeGammaWeight_nonneg hs0)
      _ = _ := by rw [integral_mul_const]; rfl
  change ‖(1/120 : ℝ) • (∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s •
    hodgeSpectralHeat A J α hs ht D hD (r^2*s-δ) f)‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/120)]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

def hodgeGammaShift (T : ℝ) (hT : 0 ≤ T) (r δ : ℝ) :
    L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true :=
  (hodgeGammaShiftLinear A J α hs ht D hD T hT r δ).mkContinuous
    ((1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2))
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r δ)

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def gammaTailKernel (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) : ℝ :=
  ⟪C.heatEvaluationVector g u,
    hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2) (C.heatEvaluationVector g v)⟫

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgePairingHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)

def pairingHeatEvaluation (b : PreL2 A J α hs ht true) (x : X) :
    L2 A J α hs ht true →L[ℝ] ℝ :=
  (C.pairingEvaluation b x).comp (hodgeHeatBoost A J α hs ht D hD ρ)

def pairingHeatVector (b : PreL2 A J α hs ht true) (x : X) : L2 A J α hs ht true :=
  (C.pairingHeatEvaluation b x).adjoint 1

def pairingGammaTail (T : ℝ) (hT : 0 ≤ T) (r : ℝ)
    (a b : PreL2 A J α hs ht true) (x y : X) : ℝ :=
  ⟪C.pairingHeatVector b x,
    hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2) (C.pairingHeatVector a y)⟫

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransversePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def transversePairKernel (p : A.centers) (K : Set Space) (r : ℝ) : UnitPair J α hs ht → ℝ :=
  ((unitChartDomain J α hs ht p.val K) ×ˢ (unitChartDomain J α hs ht p.val K)).indicator
    (fun uv => A.partition p uv.1.val.proj *
      radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖ *
      ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def gammaWedgeTailKernel (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) : ℝ :=
  ⟪C.heatEvaluationVector g u,
    hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)
      (l2Star A J α hs ht (C.heatEvaluationVector g v))⟫

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end


