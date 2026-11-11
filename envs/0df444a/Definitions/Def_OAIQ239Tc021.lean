-- Prove2me | Definitions.Def_OAIQ239Tc021
-- name    : OAIQ239Tc021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:43.574188+00:00
-- url     : https://prove2.me/theorems/175ad09b-0ec7-4768-83c7-a438ebf4f257
-- title:
--   Definitions bundle OAIQ239Tc021 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 166 declarations of OpenAI's Lean: 109 definitions, 3 inductive types or structures and 54 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ConcentrationActivationData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.HilbertFrame`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.ConcentrationCutoff`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.ConcentrationCutoff.bump`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.concentrationCompact`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.concentrationCutoff`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoffResidual`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoffSection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalChart`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCompact`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.normalCutoff`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.physicalCompact`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.weakSliceDomain`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.UnitPair`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularBase`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularChartCoordinates`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularCoordinates`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularDomain`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularNear`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularNearSet`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularWeight`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.assemble`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.boundedFrameSection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentrationDensity`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentrationPatch`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentrationTest`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.coordinateDecode`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.coordinateEncode`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.coordinateMatrix`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanAngularGlobal`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanAngularNear`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanAngularWeight`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanDistanceGlobal`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanLine`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanNearSet`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameCoefficient`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameDecode`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameEncode` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_EuclideanCoordinateLine`, `TamingCompatibility_Concentration_ConcentrationActivations`, `TamingCompatibility_Concentration_ConcentrationChart`, `TamingCompatibility_Concentration_ConcentrationTest`, `TamingCompatibility_Concentration_ConcentrationVariationBound`, `TamingCompatibility_Concentration_HodgeResidualSlices`, `TamingCompatibility_DifferentialForms_AntiEnergy`, `TamingCompatibility_DifferentialForms_ClosedLiftData`, `TamingCompatibility_DifferentialForms_Dpos`, `TamingCompatibility_DifferentialForms_EuclideanAngularDomain`, `TamingCompatibility_DifferentialForms_EuclideanAngularPoint`, `TamingCompatibility_DifferentialForms_FirstMatrixJoint`, `TamingCompatibility_DifferentialForms_FourthWeightedKernel`, `TamingCompatibility_DifferentialForms_HermitianCombinedForms`, `TamingCompatibility_DifferentialForms_HermitianCorrectedLower`, `TamingCompatibility_DifferentialForms_PhysicalSchur`, `TamingCompatibility_DifferentialForms_RadialGeometricAssembly`, `TamingCompatibility_DifferentialForms_ScalarBoundaryIntegrals`, `TamingCompatibility_DifferentialForms_SecondPlaneVariation`, `TamingCompatibility_DifferentialForms_SecondVariationIntegral`, `TamingCompatibility_Elliptic_ChartGarding`, `TamingCompatibility_Functional_CompactPairingBound`, `TamingCompatibility_Functional_NormalInverseCompact`, `TamingCompatibility_Functional_PhysicalProfile`, `TamingCompatibility_HeatFlow_HodgeHeatBoundL2`, `TamingCompatibility_HeatFlow_HodgePushedHeatBound`, `TamingCompatibility_Hodge_HodgeActualAngular`, `TamingCompatibility_Hodge_HodgeAtlasPatches`, `TamingCompatibility_Hodge_HodgeBoundedSection`, `TamingCompatibility_Hodge_HodgeCompactExtension`, `TamingCompatibility_Hodge_HodgeCoordinateRetraction`, `TamingCompatibility_Hodge_HodgeFiniteFrameResolution`, `TamingCompatibility_Hodge_HodgeGammaLinearTransfer`, `TamingCompatibility_Hodge_HodgeGaussianSchur`, `TamingCompatibility_Hodge_HodgeGlobalCorrection`, `TamingCompatibility_Hodge_HodgeGlobalKernelForms`, `TamingCompatibility_Hodge_HodgeGlobalParametrix`, `TamingCompatibility_Hodge_HodgeInputInitial`, `TamingCompatibility_Hodge_HodgeKernelAction`, `TamingCompatibility_Hodge_HodgeKernelTestTransform`, `TamingCompatibility_Hodge_HodgeKernelWeakAction`, `TamingCompatibility_Hodge_HodgeL2Coefficients`, `TamingCompatibility_Hodge_HodgeNormalSliceIntegral`, `TamingCompatibility_Hodge_HodgeParametrixDomain`, `TamingCompatibility_Hodge_HodgeParametrixFormWeak`, `TamingCompatibility_Hodge_HodgeParametrixWeakEquation`, `TamingCompatibility_Hodge_HodgePatchAllCenters`, `TamingCompatibility_Hodge_HodgePatchContinuity`, `TamingCompatibility_Hodge_HodgePatchPairing`, `TamingCompatibility_Hodge_HodgeQuantitative`, `TamingCompatibility_Hodge_HodgeSmoothSpatial`, `TamingCompatibility_Hodge_HodgeUnitDual`, `TamingCompatibility_Hodge_HodgeUnitKernelBounds`, `TamingCompatibility_Hodge_HodgeVolterraPairing`, `TamingCompatibility_Hodge_HodgeWedgeQuantitative`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc017` and `OAIQ239Tc018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc025` and `OAIQ239Tc027`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_double_physical_tail`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_volume_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_continuousAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingFiberForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingKernelForm_weak_laplacian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFiberForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_domain`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_variation_limit`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.cutoff_form_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_square_eq`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.actual_cutoff_weak_local`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_double_physical_tail`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_plane_estimate`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_actual_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gammaNormalWedge_angular`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_volume_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection_continuous_bounds`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_continuousAt`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual_heatBound`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingFiberForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSliceForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leadingSlice_weak_deriv`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.physicalGradientMass_L2_limit`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.pulledA_scalar_at`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualCoordinate_gaussian`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualFiberForm_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualPatch_joint_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_domain`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_pairing_integral`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.residualSlice_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.pulled_principal`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scaled_basis_local_bound` and `OAI.TamingCompatibility.taming_implies_compatibility`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc017
import Definitions.Def_OAIQ239Tc018

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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

def antiDelta : antiPre A J α hs ht →ₗ[ℝ] PreL2 A J α hs ht false where
  toFun a := ⟨codifferential J α ht a.val.val, GeometricAdjoint.codifferential_smooth J α hs ht a.val.property⟩
  map_add' a b := by
    apply Subtype.ext
    change codifferential J α ht (a.val.val+b.val.val) =
      codifferential J α ht a.val.val + codifferential J α ht b.val.val
    have ha : antiInvariantPart J a.val.val = a.val.val := a.property
    have hb : antiInvariantPart J b.val.val = b.val.val := b.property
    have hsa : Smooth a.val.val := a.val.property
    have hsb : Smooth b.val.val := b.val.property
    have hab : antiInvariantPart J (a.val.val+b.val.val) = a.val.val+b.val.val := by
      with_reducible rw [antiInvariantPart_add,ha,hb]
    with_reducible rw [codifferential_anti J α ht hab,
      codifferential_anti J α ht ha,codifferential_anti J α ht hb,
      exteriorDerivative_add hsa hsb,starThree_add,neg_add]
  map_smul' c a := by
    apply Subtype.ext
    change codifferential J α ht (c • a.val.val) = c • codifferential J α ht a.val.val
    have ha : antiInvariantPart J a.val.val = a.val.val := a.property
    have hca : antiInvariantPart J (c • a.val.val) = c • a.val.val := by
      with_reducible rw [antiInvariantPart_smul,ha]
    with_reducible rw [codifferential_anti J α ht hca,
      codifferential_anti J α ht ha,exteriorDerivative_smul,starThree_smul,smul_neg]

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_ChartGarding
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator EuclideanEnergy
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs in
omit [T2Space X] in

theorem scalar_garding (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a, antiInvariantPart J a = a →
      (∫ z, gradientEnergy (scalarSchwartz A J α ht D hD p a ha 2)
        (scalarSchwartz A J α ht D hD p a ha 3) z) +
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) ≤
      C * ((∫ x, GeometricAdjoint.pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a)
          (codifferential J α ht a) x ∂geometricVolume A J α)) := by
  obtain ⟨Cδ,hCδ,hδ⟩ := integral_localDelta_bound A J α ht hs D hD p
  obtain ⟨Cs,hCs,hS⟩ := integral_scalar_bound A J α hs ht D hD p
  obtain ⟨Cf,hCf,hf⟩ := GeometricHilbert.cutoff_energy_bound A J α hs ht (A.partition p).contMDiff
  let K := (D p).energyConstant*Cδ + ((D p).lowerConstant+1)*Cs
  have hK : 0 < K := add_pos (mul_pos (D p).energy_pos hCδ)
    (mul_pos (by linarith [(D p).lower_pos]) hCs)
  refine ⟨K*Cf,mul_pos hK hCf,?_⟩
  intro a ha hanti
  let s := scalarSchwartz A J α ht D hD p a ha 2
  let t := scalarSchwartz A J α ht D hD p a ha 3
  have hg := (D p).garding s t (scalarSchwartz_support A J α ht D hD p a ha 2)
    (scalarSchwartz_support A J α ht D hD p a ha 3)
  have he : (fun y => s y • AntiInvariantFrame.realPart (coordinateMetric J α ht p.val y) (fun i => (D p).frame i y) +
      t y • AntiInvariantFrame.imagPart (coordinateMetric J α ht p.val y) (fun i => (D p).frame i y)) =
      localizedFunction A p a := by
    funext z
    exact (scalar_expansion A J α ht D hD p hanti z).symm
  rw [he] at hg
  change (∫ z, gradientEnergy s t z) ≤ (D p).energyConstant *
    (∫ z, ‖oneVector (localDelta A J α ht p a z)‖^2) + (D p).lowerConstant *
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) at hg
  let L := ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a) (cutoffForm A p a) x ∂geometricVolume A J α
  let Q := ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α
  have hL : 0 ≤ L := integral_nonneg (fun x => MetricForms.pairing_self_nonneg _ _)
  have hQ : 0 ≤ Q := integral_nonneg (fun x => MetricForms.pairing_self_nonneg _ _)
  have hδa := hδ a ha hanti
  have hSa := hS a ha hanti
  change _ ≤ Cδ*Q at hδa
  change _ ≤ Cs*L at hSa
  have hfa := hf a ha hanti
  change L+Q ≤ _ at hfa
  have hpre : (∫ z, gradientEnergy s t z) +
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) ≤ K*(L+Q) := by
    have hd := mul_le_mul_of_nonneg_left hδa (D p).energy_pos.le
    have hs' := mul_le_mul_of_nonneg_left hSa (by linarith [(D p).lower_pos] : 0 ≤ (D p).lowerConstant+1)
    have hplus₁ := mul_nonneg (mul_pos (D p).energy_pos hCδ).le hL
    have hplus₂ := mul_nonneg (mul_pos (by linarith [(D p).lower_pos] : 0 < (D p).lowerConstant+1) hCs).le hQ
    dsimp only [K]
    nlinarith
  exact hpre.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfa hK.le)
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
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
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def closedLiftOfInverse
    (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht) :
    antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 :=
  let B₁ : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 := (d.comp (antiDelta A J α hs ht)).comp Gs
  let B₂ : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2 := (antiPre A J α hs ht).subtype.comp H
  B₁ + B₂

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricAssembly
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

def correctedDdc (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : smoothForms X 2 :=
  smoothDdc J hf - closedLiftOfInverse A J α hs ht H Gs
    (smoothAntiProjection A J α hs ht (smoothDdc J hf))

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCorrectedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set Filter
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def logForm {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : smoothForms X 2 :=
  correctedDdc A J α hs ht H Gs
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffLog_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans hball).trans D.domain_subset))

def sqrtForm {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : smoothForms X 2 :=
  correctedDdc A J α hs ht H Gs
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffSqrt_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans hball).trans D.domain_subset))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def logSource {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : antiPre A J α hs ht :=
  smoothAntiProjection A J α hs ht (smoothDdc J
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffLog_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans hball).trans D.domain_subset)))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCombinedForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)
  {R s : ℝ} (a : ℝ) (hR : 0 < R) (hsp : 0 < s) (b : Space)
  (hball : Metric.closedBall b (2*R) ⊆ D.domain)

def combinedForm : smoothForms X 2 :=
  logForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball +
    a • sqrtForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def frameEquiv (g : MetricModel.Metric Space) (b : Fin 4 → Space)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) : Space ≃L[ℝ] Space := by
  have hi : Function.Injective (frameMap b) := by
    intro u v huv
    have hz : frameMap b (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have hh := frameMap_metric g b hb (u-v) (u-v)
    rw [hz] at hh
    have : u-v = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by simpa using hh.symm)
    exact sub_eq_zero.mp this
  exact ContinuousLinearEquiv.ofBijective (frameMap b)
    (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective (f := (frameMap b).toLinearMap)).mp hi))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupMetricTensorV_1_raeac36_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV_1_raeac36_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
lemma regularMetrics_open : IsOpen regularMetrics :=
  (isOpen_lt continuous_const detGram_contDiff.continuous).inter
    ((ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := V) (F := V)).preimage metricOperator.continuous)

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
def normalDomain : Set (Space × Space) :=
  regularSet J α ht p D g B ∩ normalMetric g B ⁻¹' regularMetrics

def gaugedDomain : Set (Space × Space) :=
  normalDomain J α ht p D g B ∩ (fun x : Space × Space => (x.1,0)) ⁻¹' normalDomain J α ht p D g B

lemma normalDomain_open (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    IsOpen (normalDomain J α ht p D g B) :=
  (regularSet_open J α ht p D g B hg hB).inter
    (regularMetrics_open.preimage (normalMetric_contDiff g B hg hB).continuous)

lemma gaugedDomain_open (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B) :
    IsOpen (gaugedDomain J α ht p D g B) :=
  (normalDomain_open J α ht p D g B hg hB).inter
    ((normalDomain_open J α ht p D g B hg hB).preimage (continuous_fst.prodMk continuous_const))

lemma ActualData.center {q : Space} (hactual : ActualData J α ht p D q g B) :
    (q,0) ∈ gaugedDomain J α ht p D g B := by
  have hm := hactual.metric_zero J α ht p D g B
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  have hq := hOD hqO
  have hBq : (B q).IsInvertible := by
    rw [hBact q hqO]
    exact ⟨frameEquiv _ _ (D.frame_gram q hq),rfl⟩
  have hn : (q,0) ∈ normalDomain J α ht p D g B :=
    ⟨regularSet_center J α ht p D g B q hq hBq,by rw [Set.mem_preimage,hm]; exact euclidean_mem_regularMetrics⟩
  exact ⟨hn,hn⟩

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixDomain
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDomainMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDomainMetricTensorNormedSpace
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
  (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
  (q₀ : Space) (Bq : Space ≃L[ℝ] Space) (hBq : B q₀ = Bq)

def parametrixDomain (O : Set Space) : Set (Space × Space) :=
  (geometricNormalChart g B hg hB q₀ Bq hBq).source ∩
  (geometricNormalChart g B hg hB q₀ Bq hBq) ⁻¹'
    inverseRegularDomain (geometricNormalChart g B hg hB q₀ Bq hBq) ∩
  gaugedDomain J α ht p D g B ∩
  (fun x : Space × Space => normalMap g B x.1 x.2) ⁻¹' O

lemma parametrixDomain_open (O : Set Space) (hO : IsOpen O) :
    IsOpen (parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O) :=
  (((geometricNormalChart g B hg hB q₀ Bq hBq).open_source.inter
    ((inverseRegularDomain_open _ (geometricNormalChart_smooth g B hg hB q₀ Bq hBq)).preimage
      (geometricNormalChart_smooth g B hg hB q₀ Bq hBq).continuous)).inter
        (gaugedDomain_open J α ht p D g B hg hB)).inter
    (hO.preimage (normalMap_joint g B hg hB).continuous)

lemma parametrixDomain_center (O : Set Space) (hqO : q₀ ∈ O)
    (hactual : ActualData J α ht p D q₀ g B) :
    (q₀,0) ∈ parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O := by
  refine ⟨⟨⟨?_,?_⟩,hactual.center J α ht p D g B⟩,?_⟩
  · exact centeredChart_mem_source B (metricJet g B) hB (metricJet_contDiff g B hg hB) q₀ Bq hBq
  · simpa only [Set.mem_preimage,geometricNormalChart_apply,normalMap_zero]
      using geometricNormalChart_center g B hg hB q₀ Bq hBq
  · simpa only [Set.mem_preimage,normalMap_zero] using hqO

lemma exists_parametrix_tube (O : Set Space) (hO : IsOpen O) (hqO : q₀ ∈ O)
    (hactual : ActualData J α ht p D q₀ g B) :
    ∃ a : ℝ, 0 < a ∧ Metric.closedBall q₀ a ×ˢ Metric.closedBall (0 : Space) a ⊆
      parametrixDomain J α ht p D g B hg hB q₀ Bq hBq O := by
  obtain ⟨a,ha,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((parametrixDomain_open J α ht p D g B hg hB q₀ Bq hBq O hO).mem_nhds
      (parametrixDomain_center J α ht p D g B hg hB q₀ Bq hBq O hqO hactual))
  refine ⟨a,ha,?_⟩
  rintro ⟨q,z⟩ ⟨hq,hz⟩
  apply hsub
  rw [Metric.mem_closedBall,Prod.dist_eq]
  exact max_le hq hz

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
structure ParametrixData (J : AlmostComplexStructure X) (α : TwoForm X)
    (ht : Tames α J) (p : X) where
  chart : GeometricChart.Data J α ht p
  metricExtension : Space → MetricTensor (V := Space)
  frameExtension : Space → Space →L[ℝ] Space
  metric_smooth : ContDiff ℝ ∞ metricExtension
  frame_smooth : ContDiff ℝ ∞ frameExtension
  actualDomain : Set Space
  actual_open : IsOpen actualDomain
  actual_center : extChartAt Model p p ∈ actualDomain
  actual_subset : actualDomain ⊆ chart.domain
  metric_actual : ∀ y ∈ actualDomain, metricExtension y = (coordinateMetric J α ht p y).bilinear
  frame_actual : ∀ y ∈ actualDomain, frameExtension y = frameMap (fun i => chart.frame i y)
  metric_symmetric : ∀ y v w, metricExtension y v w = metricExtension y w v
  centerFrame : Space ≃L[ℝ] Space
  centerFrame_eq : frameExtension (extChartAt Model p p) = centerFrame
  radius : ℝ
  radius_pos : 0 < radius
  tube : Metric.closedBall (extChartAt Model p p) radius ×ˢ Metric.closedBall (0 : Space) radius ⊆
    parametrixDomain J α ht p chart metricExtension frameExtension metric_smooth frame_smooth
      (extChartAt Model p p) centerFrame centerFrame_eq actualDomain

lemma parametrixData_nonempty (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) : Nonempty (ParametrixData J α ht p) := by
  let D := GeometricChart.data J α hs ht p
  let q := extChartAt Model p p
  have hq : q ∈ D.domain := D.ball_subset (Metric.mem_closedBall_self (by linarith [D.radius_pos]))
  obtain ⟨g,B,O,hg,hB,hO,hqO,hOD,hga,hBa,hgs⟩ :=
    exists_metric_frame_extension J α hs ht p D hq
  let Bq := frameEquiv (coordinateMetric J α ht p q) (fun i => D.frame i q) (D.frame_gram q hq)
  have hBq : B q = Bq := (hBa q hqO).trans rfl
  have hact : ActualData J α ht p D q g B := ⟨O,hO,hqO,hOD,hga,hBa,hgs⟩
  obtain ⟨r,hr,htube⟩ := exists_parametrix_tube J α ht p D g B hg hB q Bq hBq O hO hqO hact
  exact ⟨⟨D,g,B,hg,hB,O,hO,hqO,hOD,hga,hBa,hgs,Bq,hBq,r,hr,htube⟩⟩

def parametrixData (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) : ParametrixData J α ht p :=
  Classical.choice (parametrixData_nonempty J α hs ht p)

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
def source : Set X := (extChartAt Model p).source ∩
  (extChartAt Model p) ⁻¹' Metric.ball (extChartAt Model p p) (D.radius/2)

lemma centers_actual : Metric.closedBall (extChartAt Model p p) D.radius ⊆ D.actualDomain := by
  intro q hq
  have hh := (D.tube (show (q,0) ∈ Metric.closedBall (extChartAt Model p p) D.radius ×ˢ
      Metric.closedBall (0 : Space) D.radius from
        ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩)).2
  simpa only [Set.mem_preimage,normalMap_zero] using hh

lemma source_image_subset : (extChartAt Model p) '' D.source ⊆
    Metric.closedBall (extChartAt Model p p) (D.radius/2) := by
  rintro q ⟨y,hy,rfl⟩
  exact Metric.ball_subset_closedBall hy.2

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeAtlasPatches
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_raeac36_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_raeac36_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def normalCutoff : ContDiffBump (0 : Space) :=
  ⟨D.radius/4,D.radius/2,by linarith [D.radius_pos],by linarith [D.radius_pos]⟩

def normalCompact : Set (Space × Space) :=
  Metric.closedBall (extChartAt Model p p) D.radius ×ˢ Metric.closedBall (0 : Space) D.radius

lemma normalCompact_compact : IsCompact D.normalCompact :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

def normalChart : OpenPartialHomeomorph (Space × Space) (Space × Space) :=
  geometricNormalChart D.metricExtension D.frameExtension D.metric_smooth D.frame_smooth
    (extChartAt Model p p) D.centerFrame D.centerFrame_eq

lemma normalCompact_source : D.normalCompact ⊆ D.normalChart.source := fun _ hx => (D.tube hx).1.1.1

def physicalCompact : Set (Space × Space) := D.normalChart '' D.normalCompact

lemma physicalCompact_compact : IsCompact D.physicalCompact :=
  D.normalCompact_compact.image_of_continuousOn (D.normalChart.continuousOn.mono D.normalCompact_source)

lemma physicalCompact_domain : D.physicalCompact ⊆ D.chart.domain ×ˢ D.chart.domain := by
  rintro y ⟨x,hx,rfl⟩
  change x.1 ∈ D.chart.domain ∧ normalMap D.metricExtension D.frameExtension x.1 x.2 ∈ D.chart.domain
  exact ⟨D.actual_subset (D.centers_actual hx.1),D.actual_subset (D.tube hx).2⟩
end ParametrixData

variable [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

local instance hodgeAtlasPatchesMetricTensorNormedAddCommGroup_raeac36_2 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeAtlasPatchesMetricTensorNormedSpace_raeac36_2 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def partitionLeading (p : A.centers) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  leadingPatch J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff t

def partitionResidual (p : A.centers) (t : ℝ) : Space × Space → W →L[ℝ] W :=
  residualPatch J α ht p.val (D p).chart (D p).metricExtension (D p).frameExtension
    (D p).metric_smooth (D p).frame_smooth (extChartAt Model p.val p.val)
    (D p).centerFrame (D p).centerFrame_eq (coordinatePartition A p) (D p).normalCutoff t

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixFormWeak
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_8_raeac36_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_8_raeac36_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def weakSliceDomain (q : Space) : Set Space :=
  (fun z => (q,z)) ⁻¹' parametrixDomain J α ht p E.chart E.metricExtension E.frameExtension
    E.metric_smooth E.frame_smooth (extChartAt Model p p) E.centerFrame E.centerFrame_eq E.actualDomain

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_9_raeac36_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_9_raeac36_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def leadingSlice (p : A.centers) (q : Space) (t : ℝ) (u : W) : Space → W :=
  fun y => partitionLeading J α ht A E p t (q,y) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualSlices
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance residualSlicesMetricTensorNormedAddCommGroup_raeac36_1 :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance residualSlicesMetricTensorNormedSpace_raeac36_1 :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
omit [CompactSpace X] in

def ParametrixData.cutoffResidual {p : X} (D : ParametrixData J α ht p)
    (q : Space) (t : ℝ) (u : W) : Space → W := fun z =>
  normalGauge J α ht p D.chart D.metricExtension D.frameExtension (q,z)
    (NormalHeatResidual.residual
      (fun y => CutoffFamilies.principal (normalPrincipal D.metricExtension D.frameExtension)
        D.normalCutoff (q,y))
      (fun y => CutoffFamilies.first (normalPrincipal D.metricExtension D.frameExtension)
        (gaugedFirst J α ht p D.chart D.metricExtension D.frameExtension) D.normalCutoff (q,y))
      (fun y => CutoffFamilies.zero (normalPrincipal D.metricExtension D.frameExtension)
        (gaugedFirst J α ht p D.chart D.metricExtension D.frameExtension)
        (gaugedZero J α ht p D.chart D.metricExtension D.frameExtension) D.normalCutoff (q,y)) t z u)

def residualSlice (p : A.centers) (q : Space) (t : ℝ) (u : W) : Space → W :=
  fun y => partitionResidual J α ht A E p t (q,y) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalSliceIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

local instance instNormedAddCommGroupMetricTensorSpace_11_raeac36_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_11_raeac36_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def cutoffSection (q : Space) (t : ℝ) (u : W) : Space → W := fun z =>
  normalGauge J α ht p E.chart E.metricExtension E.frameExtension (q,z)
    (E.normalCutoff z • NormalHeatResidual.modelSection t u z)

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchPairing
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
attribute [local irreducible] normalGauge normalFirst pulledA pulledB normalDensity
  normalPrincipal gaugedFirst gaugedZero NormalHeatResidual.residual
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupMetricTensorSpace_14_raeac36_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_14_raeac36_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def leadingSliceForm (p : A.centers) (q : Space) (t : ℝ) (u : W) : TwoForm X :=
  HodgeChart.manifoldTest J α ht p.val (E p).chart (leadingSlice J α ht A E p q t u)
def residualSliceForm (p : A.centers) (q : Space) (t : ℝ) (u : W) : TwoForm X :=
  HodgeChart.manifoldTest J α ht p.val (E p).chart (residualSlice J α ht A E p q t u)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchAllCenters
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def globalFrame (p : A.centers) (j : Fin 6) : TwoForm X :=
  HodgeChart.manifoldTest J α ht p.val (D p).chart
    (fun z => coordinatePartition A p z • EuclideanSpace.basisFun (Fin 6) ℝ j)

include hD in
lemma globalFrame_smooth (hs : IsSmooth α) (p : A.centers) (j : Fin 6) :
    IsSmooth (globalFrame J α ht A D p j) := by
  have hp := coordinatePartition_smooth_compact A p
  have hc : HasCompactSupport (fun z => coordinatePartition A p z • EuclideanSpace.basisFun (Fin 6) ℝ j) :=
    hp.2.smul_right
  have hsup : tsupport (fun z => coordinatePartition A p z • EuclideanSpace.basisFun (Fin 6) ℝ j) ⊆
      coordinateSupport A p :=
    (tsupport_smul_subset_left _ _).trans (coordinatePartition_tsupport A p)
  apply HodgeChart.manifoldTest_smooth J α hs ht p.val (D p).chart
    (hp.1.smul contDiff_const) hc
  apply hsup.trans
  rintro q ⟨x,hx,rfl⟩
  have hh := (D p).source_image_subset ⟨x,hD p hx,rfl⟩
  exact (D p).actual_subset ((D p).centers_actual
    (Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos]) hh))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFiniteFrameResolution
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma globalFrame_zero (p : A.centers) (j : Fin 6) {x : X} (hx : A.partition p x = 0) :
    globalFrame J α ht A D p j x = 0 := by
  classical
  unfold globalFrame HodgeChart.manifoldTest chartLift
  split_ifs with hxs
  · rw [HodgeChart.coordinateTest,coordinatePartition_apply A p hxs,hx,zero_smul,map_zero]
    rfl
  · rfl

omit [T2Space X] [CompactSpace X] in
lemma globalFrame_pullback (p : A.centers) (j : Fin 6) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) :
    ManifoldForms.pullback (globalFrame J α ht A D p j) (extChartAt Model p.val).symm z =
      coordinatePartition A p z • basisForm (coordinateMetric J α ht p.val z)
        (fun i => (D p).chart.frame i z) j := by
  rw [globalFrame,HodgeChart.pullback_manifoldTest J α ht p.val (D p).chart _ hz]
  rw [HodgeChart.coordinateTest,map_smul,reconstruct_basisFun]

omit [T2Space X] [CompactSpace X] in
lemma globalFrame_resolution_chart (p : A.centers) (a : TwoForm X) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) (hzD : z ∈ (D p).chart.domain) :
    ∑ j : Fin 6,
      GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) ((extChartAt Model p.val).symm z) •
      globalFrame J α ht A D p j ((extChartAt Model p.val).symm z) =
        (A.partition p ((extChartAt Model p.val).symm z))^2 • a ((extChartAt Model p.val).symm z) := by
  classical
  let L := (inverseChartEquiv p.val z hz).symm.continuousAlternatingMapCongrLeft
    (ι := Fin 2) (F := ℝ)
  have hL (c : TwoForm X) : L (c ((extChartAt Model p.val).symm z)) =
      ManifoldForms.pullback c (extChartAt Model p.val).symm z := by
    change (c _).compContinuousLinearMap (inverseChartEquiv p.val z hz).toContinuousLinearMap = _
    rw [inverseChartEquiv_coe]
    rfl
  apply L.injective
  simp only [map_sum,map_smul]
  have hg (j : Fin 6) : L (globalFrame J α ht A D p j ((extChartAt Model p.val).symm z)) =
      coordinatePartition A p z • basisForm (coordinateMetric J α ht p.val z)
        (fun i => (D p).chart.frame i z) j := by
    rw [hL,globalFrame_pullback J α ht A D p j hz]
  have hpair (j : Fin 6) :
      GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) ((extChartAt Model p.val).symm z) =
      coordinatePartition A p z * MetricForms.pairing (coordinateMetric J α ht p.val z)
        (L (a ((extChartAt Model p.val).symm z)))
        (basisForm (coordinateMetric J α ht p.val z) (fun i => (D p).chart.frame i z) j) := by
    rw [← GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D p j) hz,
      globalFrame_pullback J α ht A D p j hz,MetricForms.pairing_smul_right,hL]
  simp_rw [hg,hpair,smul_smul]
  have hscalar (b : ℝ) : coordinatePartition A p z*b*coordinatePartition A p z =
      (coordinatePartition A p z)^2*b := by ring
  simp_rw [hscalar,← smul_smul]
  rw [← Finset.smul_sum,basisForm_resolution _ (by simp [Space]) _ ((D p).chart.frame_gram z hzD)]
  rw [coordinatePartition,Set.indicator_of_mem hz]

include hD in
omit [T2Space X] [CompactSpace X] in
lemma globalFrame_resolution (p : A.centers) (a : TwoForm X) (x : X) :
    ∑ j : Fin 6, GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) x •
      globalFrame J α ht A D p j x = (A.partition p x)^2 • a x := by
  classical
  by_cases hp : A.partition p x = 0
  · simp only [globalFrame_zero J α ht A D p _ hp,smul_zero,Finset.sum_const_zero,hp,
      zero_pow (by norm_num : 2 ≠ 0),zero_smul]
  have hx : x ∈ (extChartAt Model p.val).source := A.subordinate p (subset_tsupport _ hp)
  have hz := (extChartAt Model p.val).map_source hx
  have hzD : extChartAt Model p.val x ∈ (D p).chart.domain := by
    have hh := (D p).source_image_subset ⟨x,hD p (subset_tsupport _ hp),rfl⟩
    exact (D p).actual_subset ((D p).centers_actual
      (Metric.closedBall_subset_closedBall (by linarith [(D p).radius_pos]) hh))
  have he := globalFrame_resolution_chart J α ht A D p a hz hzD
  let P : X → Prop := fun y =>
    ∑ j : Fin 6, GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) y •
      globalFrame J α ht A D p j y = (A.partition p y)^2 • a y
  exact (congrArg P ((extChartAt Model p.val).left_inv hx)).mp he

include hD in
omit [T2Space X] [CompactSpace X] in
lemma globalFrame_full_resolution (a : TwoForm X) (x : X) :
    ∑ p : A.centers, ∑ j : Fin 6,
      ((squareMass A x)⁻¹ * GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D p j) x) •
        globalFrame J α ht A D p j x = a x := by
  simp_rw [← smul_smul,← Finset.smul_sum,globalFrame_resolution J α ht A D hD]
  rw [← Finset.sum_smul]
  change (squareMass A x)⁻¹ • squareMass A x • a x = a x
  rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (squareMass_pos A x)),one_smul]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def frameEncode (x : X) : MetricForms.Form Space 2 →L[ℝ] FrameSpace A :=
  ContinuousLinearMap.pi (fun i => (MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2).flip
    (globalFrame J α ht A D i.1 i.2 x))

def frameDecode (x : X) : FrameSpace A →L[ℝ] MetricForms.Form Space 2 :=
  (squareMass A x)⁻¹ • ∑ p : A.centers, ∑ j : Fin 6,
    (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ).smulRight (globalFrame J α ht A D p j x)

omit [T2Space X] [CompactSpace X] in
lemma frameEncode_apply (a : TwoForm X) (x : X) (i : A.centers × Fin 6) :
    frameEncode J α ht A D x (a x) i =
      GeometricAdjoint.pairing J α ht a (globalFrame J α ht A D i.1 i.2) x := rfl

omit [T2Space X] [CompactSpace X] in
lemma frameDecode_apply (x : X) (v : FrameSpace A) :
    frameDecode J α ht A D x v = ∑ p : A.centers, ∑ j : Fin 6,
      ((squareMass A x)⁻¹ * v (p,j)) • globalFrame J α ht A D p j x := by
  change (squareMass A x)⁻¹ • ((∑ p : A.centers, ∑ j : Fin 6,
    (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ).smulRight
      (globalFrame J α ht A D p j x)) v) = _
  rw [_root_.sum_apply]
  simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    Finset.smul_sum,smul_smul]

include hD in
omit [T2Space X] [CompactSpace X] in
lemma frameDecode_encode (x : X) (v : MetricForms.Form Space 2) :
    frameDecode J α ht A D x (frameEncode J α ht A D x v) = v := by
  rw [frameDecode_apply]
  exact globalFrame_full_resolution J α ht A D hD (fun _ => v) x

include hD in
lemma frameEncode_section_smooth (hs : IsSmooth α) (a : TwoForm X) (ha : IsSmooth a) :
    ContMDiff Model 𝓘(ℝ,FrameSpace A) ∞ (fun x => frameEncode J α ht A D x (a x)) := by
  apply contMDiff_pi_space.mpr
  intro i
  exact GeometricAdjoint.pairing_two_smooth J α hs ht ha (globalFrame_smooth J α ht A D hD hs i.1 i.2)

include hD in
lemma frameDecode_section_smooth (hs : IsSmooth α) (v : X → FrameSpace A)
    (hv : ContMDiff Model 𝓘(ℝ,FrameSpace A) ∞ v) :
    IsSmooth (fun x => frameDecode J α ht A D x (v x)) := by
  have h (p : A.centers) (j : Fin 6) :
      Smooth (fun x => ((squareMass A x)⁻¹ * v x (p,j)) • globalFrame J α ht A D p j x) :=
    Smooth.fun_smul ((squareMass_inv_smooth A).mul (contMDiff_pi_space.mp hv (p,j)))
      (globalFrame_smooth J α ht A D hD hs p j)
  have hh := Smooth.sum Finset.univ (fun p : A.centers => ∑ j : Fin 6,
    (fun x => ((squareMass A x)⁻¹ * v x (p,j)) • globalFrame J α ht A D p j x))
    (fun p _ => Smooth.sum Finset.univ _ (fun j _ => h p j))
  have he : (fun x => frameDecode J α ht A D x (v x)) =
      ∑ p : A.centers, ∑ j : Fin 6,
        (fun x => ((squareMass A x)⁻¹ * v x (p,j)) • globalFrame J α ht A D p j x) := by
    funext x
    simp only [Finset.sum_apply,frameDecode_apply]
    rfl
  rw [he]
  exact hh

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def coordinateEncode (p : A.centers) (q : Space) : W →L[ℝ] FrameSpace A :=
  ContinuousLinearMap.pi (fun i => innerSL ℝ
    (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q))

def coordinateDecode (p : A.centers) (q : Space) : FrameSpace A →L[ℝ] W :=
  (squareMass A ((extChartAt Model p.val).symm q))⁻¹ • ∑ i : A.centers × Fin 6,
    (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
      (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGaussianSchur
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def coordinateMatrix (p : A.centers) (K : Space × Space → W →L[ℝ] W) (z : Space × Space) :
    FrameSpace A →L[ℝ] FrameSpace A :=
  coordinateEncode J α ht A D p z.2 ∘L K z ∘L coordinateDecode J α ht A D p z.1

def leadingMatrix (p : A.centers) (t : ℝ) : Space × Space → FrameSpace A →L[ℝ] FrameSpace A :=
  coordinateMatrix J α ht A D p (partitionLeading J α ht A D p t)

def residualMatrix (p : A.centers) (t : ℝ) : Space × Space → FrameSpace A →L[ℝ] FrameSpace A :=
  coordinateMatrix J α ht A D p (partitionResidual J α ht A D p t)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

def assemble (K : A.centers → ℝ → Space × Space → FrameSpace A →L[ℝ] FrameSpace A)
    (t : ℝ) (x y : X) : FrameSpace A →L[ℝ] FrameSpace A :=
  if 0 < t then ∑ p : A.centers, ManifoldKernelExtension.push p.val (K p t) (y,x) else 0

def globalLeading := assemble A (leadingMatrix J α ht A D)
def globalResidual := assemble A (residualMatrix J α ht A D)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaLinearTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory Set
open scoped Manifold

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

def gammaPartitionLeading (T r : ℝ) (p : A.centers) (z : Space × Space) : UnitaryFrame.W →L[ℝ] UnitaryFrame.W :=
  (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s • partitionLeading J α ht A E p (r^2*s) z)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelForms
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeNormalSymbol HodgeFrame Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def leadingFiberForm (p : A.centers) (y : X) (t : ℝ) (v : FrameSpace A) : TwoForm X :=
  if y ∈ (extChartAt Model p.val).source then
    leadingSliceForm J α ht A E p (extChartAt Model p.val y) t
      (coordinateDecode J α ht A E p (extChartAt Model p.val y) v) else 0

def residualFiberForm (p : A.centers) (y : X) (t : ℝ) (v : FrameSpace A) : TwoForm X :=
  if y ∈ (extChartAt Model p.val).source then
    residualSliceForm J α ht A E p (extChartAt Model p.val y) t
      (coordinateDecode J α ht A E p (extChartAt Model p.val y) v) else 0

def leadingKernelForm (t : ℝ) (y : X) (v : FrameSpace A) : TwoForm X :=
  if 0 < t then ∑ p : A.centers, leadingFiberForm J α ht A E p y t v else 0

def residualKernelForm (t : ℝ) (y : X) (v : FrameSpace A) : TwoForm X :=
  if 0 < t then ∑ p : A.centers, residualFiberForm J α ht A E p y t v else 0

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def framePairing (a : TwoForm X) (x : X) : FrameSpace A →L[ℝ] ℝ :=
  (squareMass A x)⁻¹ • ∑ p : A.centers, ∑ j : Fin 6,
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x •
      (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ)

omit [CompactSpace X] [T2Space X] in
lemma framePairing_apply (a : TwoForm X) (x : X) (v : FrameSpace A) :
    framePairing A J α ht E a x v = GeometricAdjoint.pairing J α ht a
      (fun z => frameDecode J α ht A E z v) x := by
  change X → MetricForms.Form Space 2 at a
  let L : MetricForms.Form Space 2 →L[ℝ] ℝ :=
    MetricForms.pairingCLM (GeometricAdjoint.pointMetric J α ht x) 2 (a x)
  change _ = L (frameDecode J α ht A E x v)
  rw [frameDecode_apply]
  have he (g : A.centers → Fin 6 → MetricForms.Form Space 2) (c : A.centers → Fin 6 → ℝ) :
      L (∑ p : A.centers, ∑ j : Fin 6, c p j • g p j) =
        ∑ p : A.centers, ∑ j : Fin 6, c p j * L (g p j) := by
    simp only [map_sum,map_smul,smul_eq_mul]
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A x)⁻¹ * v (p,j)) * L (globalFrame J α ht A E p j x) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (squareMass A x)⁻¹ * (GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x * v (p,j)) =
        ((squareMass A x)⁻¹ * v (p,j)) * GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) x
      ring
    _ = _ := (he (fun p j => globalFrame J α ht A E p j x)
      (fun p j => (squareMass A x)⁻¹*v (p,j))).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelWeakAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def kernelWeakAction (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (v : X → FrameSpace A) (a : TwoForm X) (t : ℝ) : ℝ :=
  ∫ y, ∫ x, framePairing A J α ht E a x (K t x y (v y)) ∂geometricVolume A J α ∂geometricVolume A J α

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgePushedHeatBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization ManifoldKernelExtension Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology NNReal
variable {X B : Type*} [MetricSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [NormedRing B]

def pushedHeatKernel (p : X) (K : ℝ → Space × Space → B) (t : ℝ) (x y : X) : B :=
  if 0 < t then push p (K t) (y,x) else 0

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeInputInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def kernelTestSlice (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (y : X) (v : FrameSpace A) (a : TwoForm X) (t : ℝ) : ℝ :=
  ∫ x, framePairing A J α ht E a x (K t x y v) ∂geometricVolume A J α

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelTestTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def kernelTestLinear (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (a : TwoForm X) (t : ℝ) (y : X) : FrameSpace A →L[ℝ] ℝ :=
  ∫ x, (framePairing A J α ht E a x).comp (K t x y) ∂geometricVolume A J α

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.MetricForms
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
lemma abs_pairing_le_sqrt {k : ℕ} (g : MetricModel.Metric V) (a b : Form V k) :
    |pairing g a b| ≤ Real.sqrt (pairing g a a) * Real.sqrt (pairing g b b) := by
  unfold pairing FormMetric.pairing
  simpa only [real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_norm] using
    abs_real_inner_le_norm (FormMetric.sharp (a.compContinuousLinearMap (MetricModel.equiv g).toContinuousLinearMap))
      (FormMetric.sharp (b.compContinuousLinearMap (MetricModel.equiv g).toContinuousLinearMap))
end TamingCompatibility.MetricForms

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization ManifoldVolume _root_.MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

def pointNorm (a : TwoForm X) (x : X) : ℝ :=
  Real.sqrt (GeometricAdjoint.pairing J α ht a a x)

include hs in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma pointNorm_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (pointNorm J α ht a) :=
  (GeometricAdjoint.pairing_two_smooth J α hs ht ha ha).continuous.sqrt

lemma bounded_pairing_integrable (a b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    Integrable (fun x => f x * GeometricAdjoint.pairing J α ht a.val b.val x) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  have hi := (((pointNorm_continuous J α hs ht a.val a.property).mul
    (pointNorm_continuous J α hs ht b.val b.property)).integrable_of_hasCompactSupport
      (μ := geometricVolume A J α) (HasCompactSupport.of_compactSpace _)).const_mul C
  apply hi.mono' (hfm.mul (GeometricAdjoint.pairing_two_smooth J α hs ht a.property b.property).continuous.aestronglyMeasurable)
  filter_upwards [hf] with x hx
  dsimp only [Pi.mul_apply]
  erw [norm_mul,Real.norm_eq_abs]
  exact mul_le_mul hx (MetricForms.abs_pairing_le_sqrt _ _ _) (abs_nonneg _) hC

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeBoundedSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldLocalization ManifoldVolume _root_.MeasureTheory Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

local instance instNormedAddCommGroupTangentSpaceRealSpaceModel_raeac36_1 (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
  inferInstanceAs (NormedAddCommGroup Space)
local instance instNormedSpaceRealTangentSpaceSpaceModel_raeac36_1 (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
  inferInstanceAs (NormedSpace ℝ Space)
local instance instFiniteDimensionalRealTangentSpaceSpaceModel_raeac36_1 (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
  inferInstanceAs (FiniteDimensional ℝ Space)
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scalar_pair_add (f : X → ℝ) (a c b : TwoForm X) :
    (fun x => f x * GeometricAdjoint.pairing J α ht (a+c) b x) =
      (fun x => f x * GeometricAdjoint.pairing J α ht a b x +
        f x * GeometricAdjoint.pairing J α ht c b x) := by
  funext x
  change f x * MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (a x+c x) (b x) = _
  erw [MetricForms.pairing_add_left',mul_add]
  rfl

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scalar_pair_smul (f : X → ℝ) (a b : TwoForm X) (c : ℝ) :
    (fun x => f x * GeometricAdjoint.pairing J α ht (c • a) b x) =
      (fun x => c * (f x * GeometricAdjoint.pairing J α ht a b x)) := by
  funext x
  change f x * MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (c • a x) (b x) = _
  erw [MetricForms.pairing_smul_left]
  change f x * (c * GeometricAdjoint.pairing J α ht a b x) = _
  ring

def scalarSectionFunctional (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    PreL2 A J α hs ht true →ₗ[ℝ] ℝ where
  toFun a := ∫ x, f x * GeometricAdjoint.pairing J α ht a.val b.val x ∂geometricVolume A J α
  map_add' a c := by
    change (∫ x, f x * GeometricAdjoint.pairing J α ht (a.val+c.val) b.val x ∂geometricVolume A J α) = _
    rw [scalar_pair_add]
    exact integral_add (bounded_pairing_integrable A J α hs ht a b f hfm hC hf)
      (bounded_pairing_integrable A J α hs ht c b f hfm hC hf)
  map_smul' c a := by
    change (∫ x, f x * GeometricAdjoint.pairing J α ht (c • a.val) b.val x ∂geometricVolume A J α) = _
    rw [scalar_pair_smul,integral_const_mul]
    rfl

def boundedScalarSection (b : PreL2 A J α hs ht true)
    (f : X → ℝ) (hfm : AEStronglyMeasurable f (geometricVolume A J α))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ᵐ x ∂geometricVolume A J α, ‖f x‖ ≤ C) :
    L2 A J α hs ht true :=
  (InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm
    ((scalarSectionFunctional A J α hs ht b f hfm C hC hf).extendOfNorm
      (smoothL2 A J α hs ht true).toLinearMap)

end TamingCompatibility.GeometricHilbert

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma frameMassBound_exists : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(squareMass A x)⁻¹‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (squareMass_inv_smooth A).continuous.continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x => (hC x (mem_univ x)).trans (le_max_left _ _)⟩

def frameMassBound : ℝ := (frameMassBound_exists A).choose
omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma frameMassBound_nonneg : 0 ≤ frameMassBound A := (frameMassBound_exists A).choose_spec.1
omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma frameMassBound_bound (x : X) : ‖(squareMass A x)⁻¹‖ ≤ frameMassBound A :=
  (frameMassBound_exists A).choose_spec.2 x

include hs hE in
def globalFramePreL2 (p : A.centers) (j : Fin 6) : PreL2 A J α hs ht true :=
  ⟨globalFrame J α ht A E p j,globalFrame_smooth J α ht A E hE hs p j⟩

def frameCoefficient (v : X → FrameSpace A) (p : A.centers) (j : Fin 6) (x : X) : ℝ :=
  (squareMass A x)⁻¹ * v x (p,j)

omit [CompactSpace X] [T2Space X] in
lemma frameCoefficient_measurable (v : X → FrameSpace A)
    (hv : AEStronglyMeasurable v (geometricVolume A J α)) (p : A.centers) (j : Fin 6) :
    AEStronglyMeasurable (frameCoefficient A v p j) (geometricVolume A J α) :=
  (squareMass_inv_smooth A).continuous.aestronglyMeasurable.mul
    ((continuous_apply (p,j)).comp_aestronglyMeasurable hv)

omit [T2Space X] [BorelSpace X] in
lemma frameCoefficient_bound (v : X → FrameSpace A) {V : ℝ}
    (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V) (p : A.centers) (j : Fin 6) :
    ∀ᵐ x ∂geometricVolume A J α, ‖frameCoefficient A v p j x‖ ≤ frameMassBound A * V := by
  filter_upwards [hv] with x hx
  rw [frameCoefficient,norm_mul]
  exact mul_le_mul (frameMassBound_bound A x) ((norm_le_pi_norm _ (p,j)).trans hx)
    (norm_nonneg _) (frameMassBound_nonneg A)

def boundedFrameSection (v : X → FrameSpace A)
    (hvm : AEStronglyMeasurable v (geometricVolume A J α))
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ᵐ x ∂geometricVolume A J α, ‖v x‖ ≤ V) :
    L2 A J α hs ht true :=
  ∑ p : A.centers, ∑ j : Fin 6, boundedScalarSection A J α hs ht
    (globalFramePreL2 A J α hs ht E hE p j) (frameCoefficient A v p j)
    (frameCoefficient_measurable A J α v hvm p j) (frameMassBound A*V)
    (mul_nonneg (frameMassBound_nonneg A) hV) (frameCoefficient_bound A J α v hv p j)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def frameNormConstant : ℝ := frameMassBound A *
  ∑ p : A.centers, ∑ j : Fin 6, ‖globalFramePreL2 A J α hs ht E hE p j‖

def kernelSectionL2 (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hKm : StronglyMeasurable (Function.uncurry K))
    (H : ℝ) (hH : 0 ≤ H)
    (hKi : ∀ x, Integrable (fun y => ‖K x y‖) (geometricVolume A J α))
    (hKb : ∀ x, (∫ y, ‖K x y‖ ∂geometricVolume A J α) ≤ H)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) : L2 A J α hs ht true := by
  let := geometricVolume_finite A J α hs ht
  exact boundedFrameSection A J α hs ht E hE
    (KernelL2.action (geometricVolume A J α) K v)
    ((KernelL2.action_measurable _ K hKm v hvm).aestronglyMeasurable)
    (H*V) (mul_nonneg hH hV)
    (Eventually.of_forall (fun x => KernelL2.action_norm _ K v hV hv x (hKi x) (hKb x)))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

def globalCorrection (T : ℝ) :=
  KernelSeries.correction (geometricVolume A J α) T (globalResidual J α ht A D)

def globalError (T : ℝ) := VolterraKernel.convolution (geometricVolume A J α)
  (globalLeading J α ht A D) (globalCorrection J α ht A D T)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

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
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_encode (a b : TwoForm X) (x : X) :
    framePairing A J α ht E a x (frameEncode J α ht A E x (b x)) =
      GeometricAdjoint.pairing J α ht a b x := by
  rw [framePairing_apply]
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x) (a x)
    (frameDecode J α ht A E x (frameEncode J α ht A E x (b x))) = _
  erw [frameDecode_encode J α ht A E hE]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def unitFrameDirection (u : MetricUnit g) : FrameSpace A := fun i =>
  eval (globalFrame J α ht A E i.1 i.2) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)

attribute [local irreducible] frameDecode unitFrameDirection

def unitDual (u : MetricUnit g) : PreL2 A J α hs ht true :=
  ⟨fun z => frameDecode J α ht A E z (unitFrameDirection A J α ht E g u),by
    have hv : ContMDiff Model 𝓘(ℝ,FrameSpace A) ∞
        (fun _ : X => unitFrameDirection A J α ht E g u) := contMDiff_const
    exact frameDecode_section_smooth J α ht A E hE hs _ hv⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def unitFrameFunctional (u : MetricUnit g) : FrameSpace A →L[ℝ] ℝ :=
  (squareMass A u.val.proj)⁻¹ • ∑ p : A.centers, ∑ j : Fin 6,
    unitFrameDirection A J α ht E g u (p,j) •
      (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def unitStarDirection (u : MetricUnit g) : FrameSpace A := fun i =>
  eval (starTwo J α ht (globalFrame J α ht A E i.1 i.2)) u.val.proj u.val.2
    (J.endomorphism u.val.proj u.val.2)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeActualAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def unitCoordinate (p : A.centers) (q : Space)
    (u : MetricUnit (hermitianMetric J α hs ht)) : UnitaryFrame.W :=
  coordinateDecode J α ht A E p q
    (unitFrameDirection A J α ht E (hermitianMetric J α hs ht) u)

def normalAngular (p : A.centers) (z : Space × Space)
    (u v : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  ‖unitCoordinate A J α hs ht E p
      (normalMap (E p).metricExtension (E p).frameExtension z.1 z.2) u -
    normalGauge J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension z
      (unitCoordinate A J α hs ht E p z.1 v)‖

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_EuclideanCoordinateLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupMetricTensorSpace_15 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_15 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory
open scoped RealInnerProductSpace

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization HodgeFrame _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

abbrev HilbertFrame := EuclideanSpace ℝ (A.centers × Fin 6)

def normalizedFrameEncode (x : X) : MetricForms.Form Space 2 →L[ℝ] HilbertFrame A :=
  (Real.sqrt (squareMass A x))⁻¹ •
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : A.centers × Fin 6 => ℝ)).symm.toContinuousLinearMap ∘L
      frameEncode J α ht A E x)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedFrameEncode_apply (a : TwoForm X) (x : X) :
    normalizedFrameEncode A J α ht E x (a x) =
      (Real.sqrt (squareMass A x))⁻¹ • WithLp.toLp 2 (frameEncode J α ht A E x (a x)) := rfl

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedFrameEncode_inner (a b : TwoForm X) (x : X) :
    ⟪normalizedFrameEncode A J α ht E x (a x),normalizedFrameEncode A J α ht E x (b x)⟫ =
      GeometricAdjoint.pairing J α ht a b x := by
  have hsq : ((Real.sqrt (squareMass A x))⁻¹)^2 = (squareMass A x)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (squareMass_pos A x).le]
  rw [← framePairing_encode A J α ht E hE a b x]
  simp only [normalizedFrameEncode_apply,inner_smul_left,inner_smul_right,
    PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  rw [← mul_assoc,← pow_two,hsq]
  simp only [framePairing,FunLike.coe_smul,Pi.smul_apply,smul_eq_mul,
    _root_.sum_apply,ContinuousLinearMap.proj_apply,frameEncode_apply]
  rw [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  ring

include hs hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma normalizedFrameEncode_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (fun x => normalizedFrameEncode A J α ht E x (a x)) := by
  have hroot : Continuous (fun x => (Real.sqrt (squareMass A x))⁻¹) :=
    ((squareMass_smooth A).continuous.sqrt).inv₀
      (fun x => (Real.sqrt_pos.mpr (squareMass_pos A x)).ne')
  exact hroot.smul ((PiLp.continuous_toLp 2 (fun _ : A.centers × Fin 6 => ℝ)).comp
    (frameEncode_section_smooth J α ht A E hE hs a ha).continuous)

def smoothFrameEncode : PreL2 A J α hs ht true →ₗ[ℝ] (X → HilbertFrame A) where
  toFun a x := normalizedFrameEncode A J α ht E x (a.val x)
  map_add' a b := by funext x; exact map_add _ _ _
  map_smul' c a := by
    funext x
    change normalizedFrameEncode A J α ht E x (c • a.val x) =
      c • normalizedFrameEncode A J α ht E x (a.val x)
    exact map_smul _ _ _

include hE in
lemma smoothFrameEncode_memLp (a : PreL2 A J α hs ht true) :
    MemLp (smoothFrameEncode A J α hs ht E a) 2 (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (normalizedFrameEncode_continuous A J α hs ht E hE a.val a.property).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hE in
omit [T2Space X] in
lemma smoothFrameEncode_inner_integral (a b : PreL2 A J α hs ht true) :
    (∫ x, ⟪smoothFrameEncode A J α hs ht E a x,smoothFrameEncode A J α hs ht E b x⟫
      ∂geometricVolume A J α) = ⟪a,b⟫ := by
  rw [preL2_inner]
  unfold l2Pairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (normalizedFrameEncode_inner A J α ht E hE a.val b.val)

def l2Coefficients : L2 A J α hs ht true →ₗᵢ[ℝ]
    Lp (HilbertFrame A) 2 (geometricVolume A J α) :=
  isometryFromCompletion (lpEncodeIsometry (smoothFrameEncode A J α hs ht E)
    (smoothFrameEncode_memLp A J α hs ht E hE)
    (smoothFrameEncode_inner_integral A J α hs ht E hE))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalInverseCompact
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open Set UniformJets
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

lemma normalChart_smooth : ContDiff ℝ ∞ (D.normalChart : Space × Space → Space × Space) :=
  geometricNormalChart_smooth _ _ _ _ _ _ _

lemma normalChart_diagonal {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    (q,q) ∈ inverseRegularDomain D.normalChart ∧ D.normalChart.symm (q,q) = (q,0) := by
  have hx : (q,0) ∈ D.normalCompact := ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩
  have hi := (D.tube hx).1.1.2
  have he := D.normalChart.left_inv (D.normalCompact_source hx)
  have hh : D.normalChart (q,0) = (q,q) := by
    change (q,normalMap D.metricExtension D.frameExtension q 0) = (q,q)
    rw [normalMap_zero]
  change D.normalChart (q,0) ∈ inverseRegularDomain D.normalChart at hi
  rw [hh] at hi he
  exact ⟨hi,he⟩

lemma normal_inverse_near :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ q : Space,
      q ∈ Metric.closedBall (extChartAt Model p p) D.radius → ∀ y : Space, ‖y-q‖ ≤ ε →
      (q,y) ∈ D.physicalCompact ∧
      ‖(D.normalChart.symm (q,y)).2‖ ≤ L*‖y-q‖ ∧
      D.normalCutoff (D.normalChart.symm (q,y)).2 = 1 := by
  let K := Metric.closedBall (extChartAt Model p p) D.radius
  let T : Space × Space → Space × Space := fun x => (x.1,x.1+x.2)
  let O := T ⁻¹' inverseRegularDomain D.normalChart
  let F : Space × Space → Space := fun x => (D.normalChart.symm (T x)).2
  have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk (contDiff_fst.add contDiff_snd)
  have hO : IsOpen O := (inverseRegularDomain_open D.normalChart D.normalChart_smooth).preimage hT.continuous
  have hKO : K ×ˢ {(0 : Space)} ⊆ O := by
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    have hz' : z = 0 := hz
    subst z
    simpa only [O,T,Set.mem_preimage,add_zero] using (D.normalChart_diagonal hq).1
  have hF : ∀ x ∈ O, ContDiffAt ℝ ∞ F x := by
    intro x hx
    exact (((inverseRegularDomain_smooth D.normalChart D.normalChart_smooth) (T x) hx).contDiffAt
      ((inverseRegularDomain_open D.normalChart D.normalChart_smooth).mem_nhds hx)).comp x hT.contDiffAt |>.snd
  obtain ⟨C,hC,r,hr,hsub,hlin⟩ := local_linear_bound F K (isCompact_closedBall _ _) O hO hKO hF
  let L := C+1
  have hL : 0 < L := by dsimp [L] <;> linarith
  let ε := min r (D.radius/(4*L))
  have hε : 0 < ε := lt_min hr (div_pos D.radius_pos (by positivity))
  refine ⟨L,hL,ε,hε,fun q hq y hy => ?_⟩
  have hyr : ‖y-q‖ ≤ r := hy.trans (min_le_left _ _)
  have horg := hsub (show (q,y-q) ∈ K ×ˢ Metric.closedBall (0 : Space) r from
    ⟨hq,by simpa only [Metric.mem_closedBall,dist_zero_right] using hyr⟩)
  have hmem : (q,y) ∈ inverseRegularDomain D.normalChart := by
    simpa only [O,T,Set.mem_preimage,add_sub_cancel] using horg
  have he0 : F (q,0) = 0 := by
    dsimp only [F,T]
    rw [add_zero,(D.normalChart_diagonal hq).2]
  have hnorm : ‖(D.normalChart.symm (q,y)).2‖ ≤ L*‖y-q‖ := by
    have hh := hlin q hq (y-q) hyr
    rw [he0,sub_zero] at hh
    change ‖(D.normalChart.symm (q,q+(y-q))).2‖ ≤ C*‖y-q‖ at hh
    rw [add_sub_cancel] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [L] <;> linarith) (norm_nonneg _))
  have hz : ‖(D.normalChart.symm (q,y)).2‖ ≤ D.radius/4 := by
    apply hnorm.trans
    calc
      L*‖y-q‖ ≤ L*(D.radius/(4*L)) :=
        mul_le_mul_of_nonneg_left (hy.trans (min_le_right _ _)) hL.le
      _ = D.radius/4 := by field_simp
  have hfst : (D.normalChart.symm (q,y)).1 = q :=
    geometricNormalChart_symm_fst _ _ _ _ _ _ _ hmem.1
  have hn : D.normalChart.symm (q,y) ∈ D.normalCompact := by
    refine ⟨?_,?_⟩
    · rw [hfst]; exact hq
    · rw [Metric.mem_closedBall,dist_zero_right]
      exact hz.trans (by linarith [D.radius_pos])
  refine ⟨⟨D.normalChart.symm (q,y),hn,D.normalChart.right_inv hmem.1⟩,hnorm,?_⟩
  exact D.normalCutoff.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,normalCutoff] using hz)
end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian NormalMetricCalculus CoordinateOperator
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}

namespace ParametrixData

def concentrationCompact (D : ParametrixData J α ht p) : Set Space :=
  Prod.fst '' D.physicalCompact ∪ Prod.snd '' D.physicalCompact

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_compact (D : ParametrixData J α ht p) : IsCompact D.concentrationCompact :=
  (D.physicalCompact_compact.image continuous_fst).union (D.physicalCompact_compact.image continuous_snd)

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_target (D : ParametrixData J α ht p) :
    D.concentrationCompact ⊆ (extChartAt Model p).target := by
  rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
  · exact D.chart.domain_subset (D.physicalCompact_domain hxy).1
  · exact D.chart.domain_subset (D.physicalCompact_domain hxy).2

structure ConcentrationCutoff (D : ParametrixData J α ht p) where
  radius : ℝ
  positive : 0 < radius
  near : ∀ q ∈ Metric.closedBall (extChartAt Model p p) D.radius, ∀ y : Space,
    ‖y-q‖ ≤ radius → (q,y) ∈ D.physicalCompact

omit [T2Space X] [CompactSpace X] in
lemma concentrationCutoff_nonempty (D : ParametrixData J α ht p) : Nonempty D.ConcentrationCutoff := by
  obtain ⟨_,_,ε,hε,hnear⟩ := D.normal_inverse_near
  exact ⟨⟨ε,hε,fun q hq y hy => (hnear q hq y hy).1⟩⟩

def concentrationCutoff (D : ParametrixData J α ht p) : D.ConcentrationCutoff :=
  Classical.choice D.concentrationCutoff_nonempty

namespace ConcentrationCutoff
variable {D : ParametrixData J α ht p} (c : D.ConcentrationCutoff)

def bump : ContDiffBump (0 : Space) := ⟨c.radius/2,c.radius,by linarith [c.positive],by linarith [c.positive]⟩

omit [T2Space X] [CompactSpace X] in
lemma reflected_support {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius)
    (r : ℝ) : tsupport (fun y => cutKernel c.bump r (q-y)) ⊆ D.concentrationCompact := by
  have hs : tsupport (fun y => cutKernel c.bump r (q-y)) ⊆
      (fun y => q-y) ⁻¹' tsupport (cutKernel c.bump r) :=
    tsupport_comp_subset_preimage (f := fun y : Space => q-y)
      (cutKernel (c.bump : Space → ℝ) r) (continuous_const.sub continuous_id)
  intro y hy
  have hk : q-y ∈ tsupport (c.bump : Space → ℝ) := tsupport_mul_subset_left (hs hy)
  have hn : ‖y-q‖ ≤ c.radius := by
    rw [c.bump.tsupport_eq] at hk
    change dist (q-y) 0 ≤ c.radius at hk
    rwa [dist_zero_right,norm_sub_rev] at hk
  exact Or.inr ⟨(q,y),c.near q hq y hn,rfl⟩
end ConcentrationCutoff
end ParametrixData

variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel 

def localConcentration (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) : Space → ℝ :=
  planeConvolution J α hs ht p.val (E p).concentrationCompact μ
    (cutKernel (E p).concentrationCutoff.bump r)

lemma localConcentration_smooth (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (localConcentration A J α hs ht E μ p r) :=
  planeConvolution_smooth J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff)
      (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r)

def concentrationPatch (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) : X → ℝ :=
  scalarChartLift p.val (fun b => coordinatePartition A p b*localConcentration A J α hs ht E μ p r b)

lemma concentrationPatch_smooth (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (concentrationPatch A J α hs ht E μ p r) :=
  scalarChartLift_smooth p.val
    ((coordinatePartition_smooth_compact A p).1.mul (localConcentration_smooth A J α hs ht E μ p hr))
    (coordinatePartition_smooth_compact A p).2.mul_right
    (tsupport_mul_subset_left.trans ((coordinatePartition_tsupport A p).trans (coordinateSupport_subset A p)))

def globalConcentration (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) : X → ℝ :=
  ∑ p : A.centers, concentrationPatch A J α hs ht E μ p r

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel 

def concentrationDensity (p : A.centers) (r : ℝ) (b : Space) :
    MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
    (fun u => unitChartArea J α hs ht p.val u *
      cutKernel (E p).concentrationCutoff.bump r (b-unitChartBase J α hs ht p.val u))

omit [T2Space X] [CompactSpace X] in
lemma partition_center_ball
    (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
    (p : A.centers) {x : X} (hx : x ∈ tsupport (A.partition p)) :
    extChartAt Model p.val x ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius := by
  exact Metric.closedBall_subset_closedBall (by linarith [(E p).radius_pos])
    ((E p).source_image_subset ⟨x,hE p hx,rfl⟩)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactPairingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

local instance instNormedAddCommGroupContinuousLinearMapRealIdFormSpaceOfNatNat : NormedAddCommGroup (MetricForms.Form Space 2 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdFormSpaceOfNatNat : NormedSpace ℝ (MetricForms.Form Space 2 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PhysicalProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 

def physicalProfile (r : ℝ) (x y : X) : ℝ :=
  ((1+(hermitianEDist J α hs ht x y).toReal/r)⁻¹)^6

def physicalProfileMass (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) (x : X) : ℝ :=
  ∫ u, physicalProfile J α hs ht r x u.val.proj ∂μ

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def concentrationTest (p : A.centers) (r : ℝ) (hr : 0 < r)
    (x : X) (hx : x ∈ tsupport (A.partition p)) (v : Space) : smoothForms X 2 :=
  planeCurrentTest p.val (fun y => cutKernel (E p).concentrationCutoff.bump r (extChartAt Model p.val x-y)) v
    (reflected_smooth _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff) _)
    (reflected_compact _ (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r) _)
    (((E p).concentrationCutoff.reflected_support (partition_center_ball A J α ht E hE p hx) r).trans
      (E p).concentrationCompact_target)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PhysicalSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel

def physicalGradientMass (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (L r : ℝ) (x : X) : ℝ :=
  physicalProfileMass J α hs ht μ (L*r) x/r^3

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel 
variable {V : Type*} [NormedAddCommGroup V]

def physicalQError (q : X → V) (L r : ℝ) (x : X) : ℝ :=
  ∫ y, ‖q y‖*physicalProfile J α hs ht (L*r) x y/r^3 ∂geometricVolume A J α

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def gammaPatchWedge (T r : ℝ) (p : A.centers)
    (u v : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
    (ManifoldKernelExtension.push p.val
      (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p))
      (v.val.proj,u.val.proj) (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

abbrev UnitPair := MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht)

def angularBase (uv : UnitPair J α hs ht) : X × X := (uv.2.val.proj,uv.1.val.proj)

def angularDomain (p : A.centers) : Set (UnitPair J α hs ht) :=
  (angularBase J α hs ht) ⁻¹' ManifoldKernelExtension.liftSet p.val (E p).physicalCompact

def angularChartCoordinates (p : A.centers) (uv : UnitPair J α hs ht) : Space × Space :=
  (extChartAt Model p.val uv.2.val.proj,extChartAt Model p.val uv.1.val.proj)

def angularCoordinates (p : A.centers) (uv : UnitPair J α hs ht) : Space × Space :=
  (E p).normalChart.symm (angularChartCoordinates A J α hs ht p uv)

def angularWeight (p : A.centers) (uv : UnitPair J α hs ht) : ℝ :=
  let z := angularCoordinates A J α hs ht E p uv
  coordinatePartition A p z.1 * (E p).normalCutoff z.2 *
    (normalAngular A J α hs ht E p z uv.1 uv.2)^2

def angularNearSet (r : ℝ) (p : A.centers) : Set (UnitPair J α hs ht) :=
  angularDomain A J α hs ht E p ∩
    (fun uv => ‖(angularCoordinates A J α hs ht E p uv).2‖) ⁻¹' Iic r

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel 

def angularNear (r : ℝ) (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (angularNearSet A J α hs ht E r p).indicator (angularWeight A J α hs ht E p)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def euclideanLine (p : A.centers) (u : MetricUnit (hermitianMetric J α hs ht)) : W :=
  wedge (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatBoundL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def heatBoundL2 (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (T H : ℝ)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V) (t : ℝ) : L2 A J α hs ht true := by
  classical
  let := geometricMetricSpace J α hs ht
  exact if htp : t ∈ Ioc 0 T then
    kernelSectionL2 A J α hs ht E hE (K t)
      (VolterraKernel.kernel_section K hK.measurable t) H hK.nonneg
      (by simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK.row_int t htp)
      (by simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK.row t htp)
      v hvm V hV hv
    else 0

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def kernelInputTest (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (a : TwoForm X) (t : ℝ) (v : X → FrameSpace A) : ℝ :=
  ∫ y, kernelTestLinear A J α ht E K a t y (v y) ∂geometricVolume A J α

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

def unitWedgeKernel (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (u v : MetricUnit g) : ℝ :=
  unitFrameFunctional A J α ht E g u (K u.val.proj v.val.proj (unitStarDirection A J α ht E g v))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

def unitCurrentKernel (K : X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (u v : MetricUnit g) : ℝ :=
  unitFrameFunctional A J α ht E g u (K u.val.proj v.val.proj (unitFrameDirection A J α ht E g v))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)

def euclideanNearSet (s : ℝ) (p : A.centers) : Set (UnitPair J α hs ht) :=
  angularDomain A J α hs ht E p ∩
    {uv | ‖(angularChartCoordinates A J α hs ht p uv).2-
      (angularChartCoordinates A J α hs ht p uv).1‖ ≤ s}

def euclideanAngularWeight (p : A.centers) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj * ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2

variable [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel 

def euclideanAngularNear (s : ℝ) (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (euclideanNearSet A J α hs ht E s p).indicator (euclideanAngularWeight A J α hs ht p)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthWeightedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

def euclideanAngularGlobal (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (angularDomain A J α hs ht E p).indicator (euclideanAngularWeight A J α hs ht p)

def euclideanDistanceGlobal (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (angularDomain A J α hs ht E p).indicator
    (fun uv => ‖(angularChartCoordinates A J α hs ht p uv).2-(angularChartCoordinates A J α hs ht p uv).1‖)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationVariationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

def variationDensity (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj *
    (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
      (fun u => unitChartArea J α hs ht p.val u *
        |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
          (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val u)
          (unitChartFirst J α hs ht p.val uv.2-
            skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)
              (unitChartSecond J α hs ht p.val uv.2))|) uv.1

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

def variationRaw (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj * (unitChartArea J α hs ht p.val uv.1 *
    |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
      (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1)
      (unitChartFirst J α hs ht p.val uv.2-
        skew (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1)
          (unitChartSecond J α hs ht p.val uv.2))|)

def variationVector (p : A.centers) (uv : UnitPair J α hs ht) : Space :=
  unitChartFirst J α hs ht p.val uv.2-
    skew (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1)
      (unitChartSecond J α hs ht p.val uv.2)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondPlaneVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

def secondVariationDensity (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj *
    (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
      (fun u => unitChartArea J α hs ht p.val u *
        |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
          (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val u)
          (unitChartSecond J α hs ht p.val uv.2-
            skew (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u)
              (-unitChartFirst J α hs ht p.val uv.2))|) uv.1

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondVariationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

def secondVariationRaw (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) : ℝ :=
  A.partition p uv.2.val.proj * (unitChartArea J α hs ht p.val uv.1 *
    |fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r)
      (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1)
      (unitChartSecond J α hs ht p.val uv.2-
        skew (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1)
          (-unitChartFirst J α hs ht p.val uv.2))|)

def secondVariationVector (p : A.centers) (uv : UnitPair J α hs ht) : Space :=
  unitChartSecond J α hs ht p.val uv.2-
    skew (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1)
      (-unitChartFirst J α hs ht p.val uv.2)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarBoundaryIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

omit [IsManifold Model ∞ X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma smooth_boundary (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    IsSmooth (ManifoldForms.wedgeOne (scalarDifferential f) θ.val) :=
  (scalarDifferential_smooth hf).wedgeOne θ.property

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationActivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel 

structure ConcentrationActivationData
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (Q : L2 A J α hs ht true) where
  radius : ℕ → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_le : ∀ n, radius n ≤ 1
  radius_limit : Tendsto radius atTop (𝓝 0)
  cutoff : ℕ → X → ℝ
  nonneg : ∀ n x, 0 ≤ cutoff n x
  smooth : ∀ n, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (cutoff n)
  null : geometricVolume A J α (exceptional cutoff) = 0
  density_zero : ∀ x ∉ exceptional cutoff,
    Tendsto (fun n => globalConcentration A J α hs ht E μ (radius n) x) atTop (𝓝 0)
  unit_boundary : ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    (∫ u : MetricUnit (hermitianMetric J α hs ht),
      |eval (ManifoldForms.wedgeOne (scalarDifferential (cutoff n)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ) ≤ C*stepSize n
  Q_boundary : ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    (∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (cutoff n)) θ.val x)‖ ∂geometricVolume A J α) ≤ C*stepSize n

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end


