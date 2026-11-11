-- Prove2me | Definitions.Def_OAIQ240Bp019
-- name    : OAIQ240Bp019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:43:10.610178+00:00
-- url     : https://prove2.me/theorems/69f30aff-212a-467f-a50e-12bf1a16a93d
-- title:
--   Definitions bundle OAIQ240Bp019 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 237 declarations of OpenAI's Lean: 176 definitions, 1 inductive type or structure, 3 instances and 57 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.pointMarkedCRDeriv`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.srInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.testInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.StabilizedKernelFrame.smoothZeroAtlas`, `OAI.HigherDimensionalBallPacking.Rigidity.curveAreaDensity`, `OAI.HigherDimensionalBallPacking.Rigidity.dilatedCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.eljcInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.eljcInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.fhcInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.fhcInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.hcbInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.hcbInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.horizontalEnergy`, `OAI.HigherDimensionalBallPacking.Rigidity.horizontalSlice`, `OAI.HigherDimensionalBallPacking.Rigidity.markedLocalCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.phaseAverage`, `OAI.HigherDimensionalBallPacking.Rigidity.reInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.reInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.rescaledCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.verticalEnergy`, `OAI.HigherDimensionalBallPacking.Rigidity.verticalSlice`, `OAI.PackingSufficiencySupport.CubicModel.outerConePrimitive`, `OAI.PackingSufficiencySupport.CubicModel.physicalDiskCoordinates`, `OAI.PackingSufficiencySupport.CubicModel.physicalDiskRecovery`, `OAI.PackingSufficiencySupport.CubicModel.physicalPolynomialLift`, `OAI.PackingSufficiencySupport.CubicModel.radialEndProbability`, `OAI.PackingSufficiencySupport.CubicModel.radialEndRegularPrimitive`, `OAI.PackingSufficiencySupport.CubicModel.radialEndResidue`, `OAI.PackingSufficiencySupport.CubicModel.radialForm`, `OAI.PackingSufficiencySupport.CubicModel.reducedForm`, `OAI.PackingSufficiencySupport.CubicModel.reducedPrimitive`, `OAI.PackingSufficiencySupport.CubicModel.reducedProbability`, `OAI.PackingSufficiencySupport.CubicModel.regularCoefficientNorm`, `OAI.PackingSufficiencySupport.CubicModel.selectedForm`, `OAI.PackingSufficiencySupport.CubicModel.selectedPrimitive`, `OAI.PackingSufficiencySupport.CubicModel.selectedProbability`, `OAI.PackingSufficiencySupport.CubicModel.weightedChart`, `OAI.PackingSufficiencySupport.CubicModel.weightedEndQuotient`, `OAI.PackingSufficiencySupport.CubicModel.weightedEndRegular`, `OAI.PackingSufficiencySupport.CubicModel.weightedFSForm` and 137 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Annuli_AnnularChartNormalization`, `BallPacking_Annuli_AnnularHandleCurvature`, `BallPacking_Annuli_AnnularHandleDensity`, `BallPacking_Annuli_QuadricCylinderChart`, `BallPacking_Annuli_QuadricNormalizedCycle`, `BallPacking_Annuli_SurfacePathPositivity`, `BallPacking_Annuli_SurfaceSuspensionCoefficients`, `BallPacking_BallMaps_CubicBubbleSeparated`, `BallPacking_BallMaps_QuadricLargeAmbientPacking`, `BallPacking_BallMaps_QuadricRelativeShellFlow`, `BallPacking_BallMaps_SphereCartesianDescent`, `BallPacking_Campanato_MeasureEnergy`, `BallPacking_Campanato_TranslatedSquare`, `BallPacking_CircleAction_CircleRelativeRadialMoser`, `BallPacking_Compactness_FrozenCR`, `BallPacking_Compactness_MarkedCurves`, `BallPacking_DiskMaps_CubicAreaExhaustion`, `BallPacking_Energy_ResidualEnergy`, `BallPacking_Flows_NonautonomousManifoldFlow`, `BallPacking_Forms_CubicFubiniStudy`, `BallPacking_Forms_ManifoldMapDifferential`, `BallPacking_Forms_QuadricInfinityPrimitive`, `BallPacking_Fredholm_FreeLinearization`, `BallPacking_Fredholm_NonlinearReduction`, `BallPacking_Fredholm_PointwiseMarkedCR`, `BallPacking_Fredholm_SurjectiveParametricReduction`, `BallPacking_Fredholm_TranslationContinuity`, `BallPacking_Hamiltonian_AnnularDensityMass`, `BallPacking_Hamiltonian_CartesianMomentSlices`, `BallPacking_Hamiltonian_ScaledPlanarMotion`, `BallPacking_Hopf_DegreeHopfDeformation`, `BallPacking_Hopf_DegreeRelativeShell`, `BallPacking_Hopf_SixLargeQuadricPacking`, `BallPacking_Models_CubicPhysicalLocality`, `BallPacking_Models_DisjointClocks`, `BallPacking_Models_EqualNormalModelConvergence`, `BallPacking_Models_LiouvilleRadialCalculus`, `BallPacking_Models_SurfaceComparison`, `BallPacking_Moduli_SmoothZeroCharts`, `BallPacking_Moser_ManifoldExteriorNaturality`, `BallPacking_Moser_SmoothManifoldIntegral`, `BallPacking_Normal_CompactUniformCentral`, `BallPacking_Normal_CubicToricAmbient`, `BallPacking_Normal_QuadricMovingCone`, `BallPacking_Normal_TailLineCoordinates`, `BallPacking_Packings_ComplementPacking`, `BallPacking_Projective_CubicEndCoordinates`, `BallPacking_Projective_SixLargeCubicPacking`, `BallPacking_RelativeJets_EmbeddingAdaptedNeighborhood`, `BallPacking_Residues_AreaPolarChart`, `BallPacking_SurfaceArea_AnnularSecondPositivity`, `BallPacking_SurfaceArea_BoundedPlanarResidue`, `BallPacking_SurfaceArea_QuadricEndAnnuli`, `BallPacking_SurfaceArea_QuadricEndResidueMass`, `BallPacking_SurfaceArea_QuadricSmoothExhaustion`, `BallPacking_SurfaceArea_SurfaceInteriorBoxes`, `BallPacking_SurfaceArea_SurfaceRedistribution`, `BallPacking_Surfaces_QuadricCurveManifold`, `BallPacking_Surfaces_QuadricInfinityDiffeomorph`, `BallPacking_Toric_CubicCoefficientDifferential`, `BallPacking_Toric_CubicRadialFamilyExtension`, `BallPacking_Toric_RadialDiskSmooth`, `BallPacking_Toric_RestrictedMassIndependence`, `BallPacking_Toric_StationaryManifoldPullback`, `BallPacking_Toric_ToricClosedShift`.
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp013`, `OAIQ240Bp014`, `OAIQ240Bp015` and `OAIQ240Bp016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp020` and `OAIQ240Bp021`; the statements `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_exists_jet_fredholm_observations`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_homotopy_residual_energy_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_local_jet_cauchy`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_local_jet_cauchy_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_normalized_line_energy`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240`, `OAI_PackingSufficiencySupport_CubicModel_actual_cubic_representative_packing`, `OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240`, `OAI.PackingSufficiencySupport.CubicModel.cubic_bubble_target_packing_bp240`, `OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240`, `OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240`, `OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240`, `OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240`, `OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_radial_primitive_family_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_polynomial_target_embedding_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive_invertible_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCoupling_invertible_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive_area_limit_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.tendsto_curveCutoff_bounded_residue_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_global_surface_final_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_isInvertible_annular_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.normalize_primitive_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_relative_moser_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_degree_relative_shell_maps_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240`, `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240` and `OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240`; the proofs of `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_exists_jet_fredholm_observations`, `OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_endpoint_exists`, `OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_completed_line_closed`, `OAI_HigherDimensionalBallPacking_Rigidity_equicontinuous_CR_derivative_bound`, `OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_homotopy_residual_energy_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_line_local_energy_of_slope`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_czero_compactness`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_gradient_bound`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_uniform_defect_support`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_local_jet_cauchy`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_zeroSet_compact`, `OAI_HigherDimensionalBallPacking_Rigidity_exact_normalized_line_energy`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240`, `OAI.HigherDimensionalBallPacking.main_theorem`, `OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240`, `OAI.PackingSufficiencySupport.CubicModel.cubic_bubble_target_packing_bp240`, `OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_exact_family_with_zero_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240`, `OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240`, `OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240`, `OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240`, `OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240`, `OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.exists_actual_compact_normalized_dual_fixed_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_normal_exact_family_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_actual_radial_primitive_family_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_polynomial_target_embedding_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_exact_affine_moser_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive_invertible_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCoupling_invertible_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive_area_limit_bp240`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.tendsto_curveCutoff_bounded_residue_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_global_surface_final_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_step_two_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_isInvertible_annular_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_annular_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPath_isInvertible_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.normalize_primitive_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_relative_moser_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_degree_relative_shell_maps_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_scaled_slice_rearrangement_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.exists_surface_area_redistribution_bp240`, `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240`, `OAI.PackingSufficiencySupport.MomentPolytope.finite_surface_comparison_bp240`, `OAI.PackingSufficiencySupport.actual_complement_packing_bp240`, `OAI_PackingSufficiencySupport_hasPacking_six_large_normalized` and `OAI.PackingSufficiencySupport.hasPacking_six_large_normalized_bp240`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp013
import Definitions.Def_OAIQ240Bp014
import Definitions.Def_OAIQ240Bp015
import Definitions.Def_OAIQ240Bp016

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

instance curveComplexManifold : IsManifold 𝓘(ℂ,ℂ) ∞ (locus a) := by
  apply isManifold_of_contDiffOn 𝓘(ℂ,ℂ) ∞ (locus a)
  rintro e f ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [mfld_simps] using
    (normalChartAt a x).transition_smooth x (normalChartAt a y) y

instance realSurfaceManifold : IsManifold 𝓘(ℝ,RealModel) ∞ (locus a) := by
  apply isManifold_of_contDiffOn 𝓘(ℝ,RealModel) ∞ (locus a)
  rintro e f ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [mfld_simps] using real_transition_smooth a x y

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricInfinityDiffeomorph
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
open scoped BigOperators

variable {m : ℕ} {a : Fin m → ℂ}

def curveProjection (a : Fin m → ℂ) (x : locus a) : ℂ := x.val.1

theorem curveProjection_continuous (a : Fin m → ℂ) : Continuous (curveProjection a) :=
  continuous_fst.comp continuous_subtype_val

theorem curveProjection_proper (a : Fin m → ℂ) : IsProperMap (curveProjection a) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨curveProjection_continuous a,?_⟩
  intro K hK
  obtain ⟨R,_hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  exact (projectionDomain_compact a R).of_isClosed_subset
    (hK.isClosed.preimage (curveProjection_continuous a)) (fun x hx => hbound _ hx)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def curveEndCutoff (g : ℝ → ℝ) (x : locus a) : ℝ :=
  inverseComplementCutoff (fun z : ℂ => g (Complex.normSq z)) (curveProjection a x)

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem curveEndCutoff_compact {g : ℝ → ℝ} (h1 : g=ᶠ[𝓝 0] fun _ => 1) :
    HasCompactSupport (curveEndCutoff a g) := by
  have hn : (fun z : ℂ => g (Complex.normSq z))=ᶠ[𝓝 0] fun _ => 1 :=
    h1.comp_tendsto (by
      have ht := complex_normSq_smooth.continuous.continuousAt (x := (0:ℂ))
      change Tendsto (Complex.normSq : ℂ → ℝ) (𝓝 0) (𝓝 (Complex.normSq 0)) at ht
      simpa only [map_zero] using ht)
  have hc := inverseComplementCutoff_compact hn
  apply HasCompactSupport.intro ((curveProjection_proper a).isCompact_preimage hc)
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := inverseComplementCutoff (fun z : ℂ => g (Complex.normSq z))) hx

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem shrinking_curveEndCutoff_compact {g : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (h1 : ∀ t∈Ioo (-r) r,g t=1) (n : ℕ) :
    HasCompactSupport (curveEndCutoff a (shrinkingCutoff g n)) := by
  apply curveEndCutoff_compact a
  have hn : 0 < r/((n:ℝ)+1) := div_pos hr (by positivity)
  filter_upwards [isOpen_Ioo.mem_nhds
    (show (0:ℝ)∈Ioo (-(r/((n:ℝ)+1))) (r/((n:ℝ)+1)) by constructor <;> linarith)] with t ht
  exact shrinkingCutoff_one h1 n t ht

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def phaseInclusion (x : locus a) : PlanePhase (Option (Fin m)) := affinePhase m x.val

def curveFSPrimitive (c : ℝ) : ManifoldOneForm RealModel (locus a) :=
  manifoldPullbackOneForm (fun _ => affineFSPrimitive c) (phaseInclusion a) 0

def curveFSForm (c : ℝ) : ManifoldTwoForm RealModel (locus a) :=
  manifoldPullbackTwoForm (fun _ => affineFSForm c) (phaseInclusion a) 0

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_CubicFubiniStudy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def weightedChart (D m : ℕ) (b : BaseCurve) : ℂ → Affine 3 :=
  weightedProjection D m ∘ projection ∘ (normalChartAt (parameters 0) b).inclusionChart b

 def weightedFSForm (D m : ℕ) (c : ℝ) : ManifoldTwoForm RealModel BaseCurve :=
  manifoldPullbackTwoForm (fun _ => affineFSForm c) (weightedPhaseInclusion D m) 0

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian
open scoped BigOperators ComplexConjugate
section

variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

def infinityRegularPoint (s : ℂ) : Affine m := (s,infinityRoot a ε s)

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

def infinityRegularPhase (y : Plane) : PlanePhase (Option (Fin m)) :=
  affinePhase m (infinityRegularPoint a ε (Complex.equivRealProdCLM.symm y))

def infinityRegularPrimitive (c : ℝ) : Plane → Plane →L[ℝ] ℝ :=
  staticPullbackOneForm (affineFSPrimitive c) (infinityRegularPhase a ε)

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_CubicEndCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

def normalPolynomial (a : Fin m → ℂ) (t : ℝ) (z : Affine m) : NormalPolynomialIndex m → ℂ
  | .inl i => veronese (affineComplex m z) i
  | .inr j => (t:ℂ)⁻¹*equations a z j

def ambientFSPrimitive (c : ℝ) (z : Affine m) : Affine m →L[ℝ] ℝ :=
  (affineFSPrimitive c (affinePhase m z)).comp (affinePhase m)

def normalAmbientPrimitive (a : Fin m → ℂ) (c d t : ℝ) : Affine m → Affine m →L[ℝ] ℝ :=
  (1-2*d) • ambientFSPrimitive c+
    d • primitivePullback (affineFSPrimitive c) (fun z => complexCartesian (normalPolynomial a t z))

def normalAmbientForm (a : Fin m → ℂ) (c d t : ℝ) :=
  euclideanExteriorOneForm (normalAmbientPrimitive a c d t)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def weightedEndQuotient (D m : ℕ) (ε : EndIndex) (s : ℂ) : WeightedAffineIndex → ℂ :=
  affineComplex 3 (weightedProjection D m
    (endQuotient ε s none,endQuotient ε s (some 0)))

 def weightedEndRegular (D m : ℕ) (ε : EndIndex) (s : ℂ) : WeightedHomogeneousIndex → ℂ :=
  let L := D-m
  let A := endNumerator ε s
  let C := endCoefficient s
  if ε 0 then
    (if ε 1 then five (s^D) (s^m*A 0^L) (s^m*A 1^L) (A 0^L*A 1^m) (A 0^m*A 1^L)
    else five (s^L) (A 0^L) (s^(2*L)*C 1^L) (s^m*A 0^L*C 1^m) (s^(2*L-m)*A 0^m*C 1^L))
  else
    (if ε 1 then five (s^L) (s^(2*L)*C 0^L) (A 1^L) (s^(2*L-m)*C 0^L*A 1^m) (s^m*C 0^m*A 1^L)
    else complexAffineLift (affineComplex 3 (weightedProjection D m
      (s*C 0,s*C 1))))

 def weightedLift (D m : ℕ) (v w : ℂ) : WeightedHomogeneousIndex → ℂ :=
  complexAffineLift (affineComplex 3 (weightedProjection D m (v,w)))

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian

 def weightedRegularEndPhase (D m : ℕ) (ε : EndIndex) (y : Plane) : PlanePhase WeightedHomogeneousIndex :=
  complexCartesian (weightedEndRegular D m ε (Complex.equivRealProdCLM.symm y))

 def weightedRegularEndPrimitive (D m : ℕ) (ε : EndIndex) (c : ℝ) : Plane → Plane →L[ℝ] ℝ :=
  staticPullbackOneForm (hopfPrimitive c) (weightedRegularEndPhase D m ε)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι] [Nonempty ι]

 def reducedProbability (w : ι → MomentPlane) (D m : ι → ℕ) (p : MomentPlane)
    (x : BaseCurve) (i : ι) : ℝ := selected w (fun j => coefficientNorm (D j) (m j) x) p i

 def reducedPrimitive (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane) :
    ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i,reducedProbability w D m p x i • weightedFSPrimitive (D i) (m i) c x

 def reducedForm (w : ι → MomentPlane) (D m : ι → ℕ) (c : ℝ) (p : MomentPlane) :
    ManifoldTwoForm RealModel BaseCurve := manifoldExteriorOneForm (reducedPrimitive w D m c p)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicCoefficientDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold _root_.ContinuousLinearMap
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open Filter

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 def selectedProbability (w : ι → E) (D m : ι → ℕ) (p : E)
    (x : BaseCurve) (i : ι) : ℝ := selected w (fun j => coefficientNorm (D j) (m j) x) p i

 def selectedPrimitive (w : ι → E) (D m : ι → ℕ) (c : ℝ) (p : E) :
    ManifoldOneForm RealModel BaseCurve :=
  fun x => ∑ i,selectedProbability w D m p x i • weightedFSPrimitive (D i) (m i) c x

 def selectedForm (w : ι → E) (D m : ι → ℕ) (c : ℝ) (p : E) :
    ManifoldTwoForm RealModel BaseCurve := manifoldExteriorOneForm (selectedPrimitive w D m c p)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

def radialForm (k : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane) :
    ManifoldTwoForm RealModel BaseCurve := manifoldExteriorOneForm (radialPrimitive k D m c p)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_CubicRadialFamilyExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

local instance radialFamilySigmaCompact : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

variable {ι : Type*} [Fintype ι]

 def regularCoefficientNorm (D m : ℕ) (ε : EndIndex) (y : Plane) : ℝ :=
  phaseSq (weightedRegularEndPhase D m ε y)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold

variable {ι : Type*} [Fintype ι]

 def radialEndProbability (w : ι → ℕ × ℕ) (D m : ι → ℕ) (p : Radial.Plane)
    (ε : EndIndex) (y : Plane) (i : ι) : ℝ :=
  radialProbability w D m p (infinityDiffeomorph (parameters 0) ε y) i

 def radialEndRegularPrimitive (w : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (ε : EndIndex) (y : Plane) : Plane →L[ℝ] ℝ :=
  ∑ i,radialEndProbability w D m p ε y i • weightedRegularEndPrimitive (D i) (m i) ε c y

 def radialEndResidue (w : ι → ℕ × ℕ) (D m : ι → ℕ) (c : ℝ) (p : Radial.Plane)
    (ε : EndIndex) (y : Plane) : ℝ :=
  ∑ i,radialEndProbability w D m p ε y i*weightedEndResidue (D i) (m i) ε c

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndAnnuli
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open Hamiltonian
variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def curveEndAnnulus (ε : Fin m → Bool) (r R : ℝ) : Set (locus a) :=
  infinityDiffeomorph a ε '' radialAnnulus r R

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricEndResidueMass
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance quadricEndResidueMassSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

end

variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

namespace NormalChart
variable (e : NormalChart a) (x : locus a)

theorem realSliceChart_smooth :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (e.realSliceChart x) :=
  Complex.equivRealProdCLM.contDiff.contMDiff.comp
    (((e.coordinate |> curveCoordinate).restrictScalars ℝ).contDiff.contMDiff.comp
      (real_inclusion_contMDiff a))

theorem realSliceChart_symm_smooth :
    ContMDiffOn 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel) ∞ (e.realSliceChart x).symm
      (e.realSliceChart x).target := by
  intro y hy
  apply real_contMDiffWithinAt_of_ambient
  have hs := (e.sliceChart_inverse_smooth x).restrict_scalars ℝ
  have hc := hs.comp Complex.equivRealProdCLM.symm.contDiff.contDiffOn
    (mapsTo_preimage _ _)
  apply (hc _ hy.2).mono
  intro z hz
  exact hz.2

def realSliceDiffeomorph : PartialDiffeomorph 𝓘(ℝ,RealModel) 𝓘(ℝ,RealModel)
    (locus a) RealModel ∞ where
  __ := e.realSliceChart x
  contMDiffOn_toFun := (e.realSliceChart_smooth x).contMDiffOn
  contMDiffOn_invFun := e.realSliceChart_symm_smooth x

end NormalChart

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_BoundedPlanarResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance boundedPlanarResidueSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance boundedResidueLimitSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_QuadricSmoothExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter MeasureTheory
open Hamiltonian
section

variable {m : ℕ} {a : Fin m → ℂ}

 def signFlipOver (V : Set ℂ) (j : Fin m) (x : curveProjection a ⁻¹' V) :
    curveProjection a ⁻¹' V :=
  ⟨signFlip j x.val,x.property⟩

end
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance instSigmaCompactSpaceElemAffineLocus : SigmaCompactSpace (locus a) := curveSigmaCompact a

end

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CubicAreaExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

local instance radialCubicUniformAreaSigmaCompact : SigmaCompactSpace BaseCurve :=
  curveSigmaCompact (parameters 0)

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfacePathPositivity
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_source _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.transverseCylinder_symm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter

variable (m : ℕ)

theorem unitCircle_subset_transverseDomain {z : ℂ} (hz : ‖z‖=1) :
    z∈transverseAnnulusDomain m := by
  have hz0 : z≠0 := by intro h; simp [h] at hz
  have hp : plus z=(z.re : ℂ) := by
    rw [plus,Complex.inv_eq_conj hz,Complex.add_conj]
    push_cast
    ring
  have hn : z.re^2≤1 := by
    have he := Complex.normSq_eq_norm_sq z
    rw [hz,one_pow] at he
    simp only [Complex.normSq_apply] at he
    nlinarith [sq_nonneg z.im]
  refine ⟨hz0,?_⟩
  intro j hj
  have hjp : 0<(j.val : ℝ) := by exact_mod_cast Fin.pos_iff_ne_zero.mpr hj
  simp only [parameters,hp,← Complex.ofReal_pow,Complex.sub_re,
    Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.ofReal_re]
  linarith

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_QuadricCylinderChart
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplexEquiv_symm_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.densityChart_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.annularUnshearMap_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCoverLinearEquiv_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleAnnularCover_eq_densityChart _root_.OAI.PackingSufficiencySupport.Hamiltonian.handleDensityChart_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem transverseCylinder_core (u : Circle) : (0,u)∈(transverseCylinder m).source := by
  rw [transverseCylinder_source]
  exact unitCircle_subset_transverseDomain m (by simp)

theorem exists_transverseCylinderWidth : ∃ a : ℝ,0<a ∧
    Icc (-a) a ×ˢ (univ : Set Circle)⊆(transverseCylinder m).source := by
  have hc : ({0}:Set ℝ) ×ˢ (univ : Set Circle)⊆(transverseCylinder m).source := by
    rintro ⟨s,u⟩ ⟨hs,_⟩
    have hs' : s=0 := hs
    subst s
    exact transverseCylinder_core m u
  obtain ⟨U,V,hU,_,h0,hV,hUV⟩ := generalized_tube_lemma isCompact_singleton
    (isCompact_univ : IsCompact (univ : Set Circle)) (transverseCylinder m).open_source hc
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0 (mem_singleton 0)))
  refine ⟨ε/2,half_pos hε,?_⟩
  rintro ⟨s,u⟩ ⟨hs,_⟩
  apply hUV
  refine ⟨hball ?_,hV (mem_univ u)⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
  constructor <;> linarith [hs.1,hs.2]

def transverseCylinderWidth : ℝ := (exists_transverseCylinderWidth m).choose

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport
open scoped Topology
open Set Function

theorem complex_normalize_dist {z : ℂ} (hz : z≠0) :
    dist z (‖z‖⁻¹ • z)=|‖z‖-1| := by
  rw [dist_eq_norm,show z-‖z‖⁻¹ • z=(1-‖z‖⁻¹) • z by module,norm_smul,
    Real.norm_eq_abs]
  calc
    |1-‖z‖⁻¹| * ‖z‖ = |(1-‖z‖⁻¹)*‖z‖| := by
      rw [abs_mul,abs_of_nonneg (norm_nonneg z)]
    _ = |‖z‖-1| := by
      congr 1
      field_simp [norm_ne_zero_iff.mpr hz]

theorem exists_complexClosedAnnulus_subset {U : Set ℂ} (hU : IsOpen U)
    (hs : Metric.sphere (0:ℂ) 1⊆U) :
    ∃ ε : ℝ,0<ε ∧ ε<1/2 ∧ complexClosedAnnulus ε⊆U := by
  obtain ⟨δ,hδ,hδU⟩ := (isCompact_sphere (0:ℂ) 1).exists_cthickening_subset_open hU hs
  let ε := min (δ/2) (1/4)
  have hε : 0<ε := lt_min (half_pos hδ) (by norm_num)
  have hεδ : ε≤δ := (min_le_left _ _).trans (half_le_self hδ.le)
  have hεh : ε<1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨ε,hε,hεh,?_⟩
  intro z hz
  have hzn : 0<‖z‖ := by linarith [hz.1]
  have hz0 : z≠0 := norm_pos_iff.mp hzn
  have hyn : ‖‖z‖⁻¹ • z‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hzn),inv_mul_cancel₀ hzn.ne']
  have hyd : dist z (‖z‖⁻¹ • z)≤δ := by
    rw [complex_normalize_dist hz0]
    exact (abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩ : |‖z‖-1|≤ε).trans hεδ
  apply hδU
  apply Metric.mem_cthickening_of_dist_le z (‖z‖⁻¹ • z) δ (Metric.sphere (0:ℂ) 1)
  · simpa only [Metric.mem_sphere,dist_zero_right] using hyn
  · exact hyd

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian

variable (m : ℕ)

theorem exists_annulusWidth : ∃ ε : ℝ,0<ε ∧ ε<1/2 ∧
    planeClosedAnnulus ε⊆(annulusDiffeomorph m).source := by
  obtain ⟨ε,hε,hε1,hU⟩ := exists_complexClosedAnnulus_subset (annulusDomain_isOpen m)
    (fun z hz => unitCircle_subset_domain m (by simpa only [Metric.mem_sphere,dist_zero_right] using hz))
  refine ⟨ε,hε,hε1,?_⟩
  intro x hx
  rw [annulusDiffeomorph_source]
  exact hU hx

def annulusWidth : ℝ := (exists_annulusWidth m).choose

def compactDualForm : ManifoldOneForm RealModel (Surface m) :=
  handlePushforwardOneForm (annulusDiffeomorph m)
    (manifoldScalarDifferential (planeRadialStep (annulusWidth m)))

def transversePoint (θ : ℝ) : Affine (m+2) :=
  ((Real.cos θ : ℂ),fun j => if j=0 then Complex.I*(Real.sin θ : ℂ)
    else Complex.I*(Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ))

theorem transversePoint_mem (θ : ℝ) : transversePoint m θ∈locus (parameters m) := by
  rw [mem_locus]
  intro j
  have hc := Real.cos_sq_le_one θ
  by_cases hj : j=0
  · subst j
    simp only [transversePoint,↓reduceIte,parameters_zero,mul_pow,Complex.I_sq]
    have he := Real.sin_sq_add_cos_sq θ
    have heC : (Real.sin θ : ℂ)^2+(Real.cos θ : ℂ)^2=1 := by exact_mod_cast he
    linear_combination -heC
  · have hn : 0≤(j.val : ℝ)+1-Real.cos θ^2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) j.val]
    have he := Real.sq_sqrt hn
    have heC : (Real.sqrt ((j.val : ℝ)+1-Real.cos θ^2) : ℂ)^2=
        (j.val : ℂ)+1-(Real.cos θ : ℂ)^2 := by exact_mod_cast he
    simp only [transversePoint,ite_eq_right hj,mul_pow,Complex.I_sq,parameters]
    rw [heC]
    ring

def transverseCycle (θ : ℝ) : Surface m := ⟨transversePoint m θ,transversePoint_mem m θ⟩

@[simp] theorem transversePoint_first (θ : ℝ) : (transversePoint m θ).1=(Real.cos θ : ℂ) := rfl

@[simp] theorem transversePoint_zero (θ : ℝ) : (transversePoint m θ).2 0=Complex.I*(Real.sin θ : ℂ) := by
  simp [transversePoint]

@[simp] theorem transversePoint_one (θ : ℝ) : (transversePoint m θ).2 1=
    Complex.I*(Real.sqrt (1+Real.sin θ^2) : ℂ) := by
  have he : (2:ℝ)-Real.cos θ^2=1+Real.sin θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hj : (1 : Fin (m+2))≠0 := by simp
  simp only [transversePoint,ite_eq_right hj,Fin.val_one,Nat.cast_one,one_add_one_eq_two]
  rw [he]

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

def transverseRealCoordinate (θ : ℝ) : RealModel :=
  Complex.equivRealProdCLM (annulusCoordinate m (transverseCycle m θ).val)

def transverseStep (θ : ℝ) : ℝ := planeRadialStep (annulusWidth m) (transverseRealCoordinate m θ)

def dualAlongCycle (θ : ℝ) : ℝ := curveOneForm (compactDualForm m) (transverseCycle m) θ

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_QuadricNormalizedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

def cylinderDualForm : ℝ → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (fun _ : ℝ => compactDualForm m) (transverseCylinder m)

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularChartNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

def cylinderClockPrimitive (S : ℝ → ℝ) (f : Circle → ℝ) :
    ManifoldOneForm CylinderModel HandleCylinder :=
  weightedCylinderAngular (fun z => S z.1*f z.2)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open Hamiltonian

variable (m : ℕ)

instance surfaceSigmaCompact : SigmaCompactSpace (Surface m) := by
  exact IsClosed.sigmaCompactSpace (locus_isClosed (parameters m))

def restrictedTransverseCylinder (a : ℝ) :
    PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,RealModel) HandleCylinder (Surface m) ∞ :=
  restrictHandleDiffeomorph (transverseCylinder m) (Ioo (-a) a ×ˢ univ)
    (isOpen_Ioo.prod isOpen_univ)

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

namespace AnnularHandleData

def band (b : ℝ) : Set HandleCylinder := Icc (-b) b ×ˢ univ

def core (H : AnnularHandleData E M) (b : ℝ) : Set HandleCylinder :=
  Icc (-b) b ×ˢ tsupport H.clock

end AnnularHandleData
end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

def density (H : AnnularHandleData E M) (b : ℝ) : ManifoldTwoForm E M :=
  manifoldWedge (H.radial b) H.dual

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_SurfaceSuspensionCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {Ω : V →L[ℝ] V →L[ℝ] ℝ}

def annularCoverA
    (D : AnnularHandleData E M)
    (γ : ManifoldOneForm E M) (q : Plane) : ℝ :=
  euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,q) (1,0)

def annularCoverB
    (D : AnnularHandleData E M)
    (γ : ManifoldOneForm E M) (q : Plane) : ℝ :=
  euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,q) (0,1)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularHandleCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def annularCoverDomain
    (D : AnnularHandleData E M) : Set Plane :=
  cylinderCover ⁻¹' D.chart.source

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 def annularCoverTwoCoefficient
    (D : AnnularHandleData Plane M)
    (Λ : ManifoldTwoForm Plane M) (q : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Λ) (D.handleAnnularCover) (0,q) (1,0) (0,1)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def successorStandardForm (m : ℕ) : Ambient (m+1) →L[ℝ] Ambient (m+1) →L[ℝ] ℝ :=
  (productForm (phaseArea (ι := Fin m))).bilinearComp (complexSplitPhase m).toContinuousLinearMap (complexSplitPhase m).toContinuousLinearMap

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SmoothManifoldIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

def averageOneForm (α : ℝ → ManifoldOneForm E M) (t : ℝ) (x : M) : E →L[ℝ] ℝ :=
  ∫ s in (0:ℝ)..1, parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x

end SmoothCircleAction

end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]



structure ManifoldMoserData (Ω : ℝ → ManifoldTwoForm E M)
    (α : ℝ → ManifoldOneForm E M) : Prop where
  smooth_two : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)
  smooth_one : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)
  nondegenerate : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, (Ω t x).IsInvertible
  skew : ∀ t ∈ Icc (0:ℝ) 1, ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ u v,
    chartTwoForm (Ω t) c y u v = -chartTwoForm (Ω t) c y v u
  closed : ∀ t ∈ Icc (0:ℝ) 1, ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ u v w,
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,u) v w -
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,v) u w +
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,w) u v = 0
  exact_time : ∀ t ∈ Icc (0:ℝ) 1, ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ v w,
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w =
    fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,v) w -
    fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,w) v



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_RelativeJets_EmbeddingAdaptedNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold IsManifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} {N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def embeddedNormalJet (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    (e : N → M) (p : ℝ × M) : (ℝ × E) →L[ℝ] ℝ := by
  classical
  exact if h : ∃ b, e b = p.2 then
    (symplecticNormalJet (Ω p.1 p.2) (manifoldMapDifferential (E := E) (F := F) e h.choose) (α p.1 p.2)).comp
      (ContinuousLinearMap.snd ℝ ℝ E)
    else 0


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def correctedOneForm (α : ℝ → ManifoldOneForm E M) (f : ℝ × M → ℝ)
    (t : ℝ) (x : M) : E →L[ℝ] ℝ :=
  α t x + manifoldSpatialDifferential f t x


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_EqualNormalModelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance instSigmaCompactSpaceElemAffineLocus_2 : SigmaCompactSpace (locus a) := curveSigmaCompact a

 def normalHorizontalPrimitive (b : ℝ) (p : Fin q → ℝ) : ManifoldOneForm Plane (locus a) :=
  equalNormalCoefficient q b p • curveFSPrimitive a (1/Real.pi)

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def rectanglePolar (y : Plane) : Plane :=
  Complex.equivRealProdCLM (cylinderComplexMap (cylinderCover y))

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_StationaryManifoldPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Topology
open scoped Manifold
open Manifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

def toricChartA (Γ : (ι → ℝ) → ManifoldOneForm Plane M) (c : M) (q : Plane × (ι → ℝ)) :=
  chartOneForm (Γ q.2) c q.1 (1,0)
def toricChartB (Γ : (ι → ℝ) → ManifoldOneForm Plane M) (c : M) (q : Plane × (ι → ℝ)) :=
  chartOneForm (Γ q.2) c q.1 (0,1)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_ToricClosedShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def toricClosedShift (Γ : P → ManifoldOneForm E M) (J : P → ℝ)
    (β : ManifoldOneForm E M) (t : ℝ) (p : P) : ManifoldOneForm E M :=
  Γ p+(t*J p) • β

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_AnnularSecondPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

def cylinderAreaCoefficient (Λ : ManifoldTwoForm CylinderModel HandleCylinder) (q : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Λ) cylinderCover (0,q) (1,0) (0,1)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def clockPrimitive
    (H : AnnularHandleData E M) (b : ℝ) : ManifoldOneForm E M :=
  manifoldPullbackOneForm (E := CylinderModel) (F := E)
    (fun _ => cylinderClockPrimitive (intervalClock (-b) b) H.clock)
    H.chart.symm 0

end

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceInteriorBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SurfaceCoordinateBox

def Inside (U : Set M) := {B : SurfaceCoordinateBox M // B.compactCarrier ⊆ U}

end SurfaceCoordinateBox

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

def HasInteriorPrimitiveFamily (U : Set M) (Ω : P → ManifoldTwoForm Plane M) : Prop :=
  ∃ L : Set M, IsCompact L ∧ L ⊆ U ∧ ∃ α : P → ManifoldOneForm Plane M,
    IsPrimitiveFamily Ω α ∧ ∀ p x,x∉L→α p x=0

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K L : Set M}

def restrictSurfacePartition (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hLK : L⊆K) : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L where
  toFun := ρ.toFun
  locallyFinite' := ρ.locallyFinite'
  nonneg' := ρ.nonneg'
  sum_eq_one' := fun _ hx => ρ.sum_eq_one (hLK hx)
  sum_le_one' := ρ.sum_le_one'

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_SurfaceArea_SurfaceRedistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {I : Type*} [Fintype I] {K L T : Set M}

def redistributedDifference (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (D : P → ManifoldTwoForm Plane M) (χ : ManifoldTwoForm Plane M) :
    P → ManifoldTwoForm Plane M := fun p => partitionFormMass B ρ (D p) • χ-D p


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_AnnularDensityMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def HamiltonianDiskIsotopyFamily.motion {R : ℝ} (Ψ : HamiltonianDiskIsotopyFamily P R) :
    PlanarHamiltonianMotion P where
  hamiltonian := Ψ.hamiltonian
  smooth := Ψ.smooth
  compact := Ψ.compact
  trace := fun y t x => Ψ.isotopy.map y t x
  continuous := Ψ.isotopy.smooth.continuous
  zero := fun y x => by rw [Ψ.isotopy.zero]; rfl
  flow := Ψ.flow

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_ScaledPlanarMotion
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cartesianConjugate_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.cutoff_phaseSq_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_inner _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_moments _root_.OAI.PackingSufficiencySupport.Hamiltonian.liftedTrajectory_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseRotate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaled_planar_fderiv {H : Plane → ℝ} (hH : Differentiable ℝ H)
    {a : ℝ} (ha : a ≠ 0) (c : ℝ) (x : Plane) :
    fderiv ℝ (fun z => (c*a^2)*H (a⁻¹ • z)) x =
      (c*a) • fderiv ℝ H (a⁻¹ • x) := by
  have hd := ((hH (a⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul a⁻¹)).const_mul (c*a^2)
  change fderiv ℝ (fun z => (c*a^2)*(H ∘ HSMul.hSMul a⁻¹) z) x = _
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  field_simp [ha]

def scaledPlanarHamiltonian (Ψ : PlanarHamiltonianMotion P) (a χ : P → ℝ)
    (p : (P × ℝ) × Plane) : ℝ :=
  ((χ p.1.1 * deriv Real.smoothTransition p.1.2)*(a p.1.1)^2) *
    Ψ.hamiltonian ((p.1.1,χ p.1.1 * Real.smoothTransition p.1.2),(a p.1.1)⁻¹ • p.2)

def scaledPlanarTrace (Ψ : PlanarHamiltonianMotion P) (a χ : P → ℝ)
    (y : P) (t : ℝ) (x : Plane) : Plane :=
  a y • Ψ.trace y (χ y * Real.smoothTransition t) ((a y)⁻¹ • x)

theorem scaledPlanarHamiltonian_smooth (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : ContDiff ℝ ∞ a) (hn : ∀ y, a y ≠ 0) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (scaledPlanarHamiltonian Ψ a χ) := by
  have hai : ContDiff ℝ ∞ (fun y => (a y)⁻¹) := ha.inv hn
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  unfold scaledPlanarHamiltonian
  exact (((hχ.comp contDiff_fst.fst).mul (hβ.comp contDiff_fst.snd)).mul
    ((ha.comp contDiff_fst.fst).pow 2)).mul (Ψ.smooth.comp
      ((contDiff_fst.fst.prodMk ((hχ.comp contDiff_fst.fst).mul
        (Real.smoothTransition.contDiff.comp contDiff_fst.snd))).prodMk
          ((hai.comp contDiff_fst.fst).smul contDiff_snd)))

theorem scaledPlanarHamiltonian_compact (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : Continuous a) (hn : ∀ y, a y ≠ 0) (hχ : HasCompactSupport χ) :
    HasCompactSupport (scaledPlanarHamiltonian Ψ a χ) := by
  let K := (tsupport χ ×ˢ tsupport (deriv Real.smoothTransition)) ×ˢ (Prod.snd '' tsupport Ψ.hamiltonian)
  let f : (P × ℝ) × Plane → (P × ℝ) × Plane := fun p => (p.1,a p.1.1 • p.2)
  have hK : IsCompact K := (hχ.prod smoothTransition_deriv_compact).prod
    (Ψ.compact.image continuous_snd)
  have hf : Continuous f := continuous_fst.prodMk ((ha.comp continuous_fst.fst).smul continuous_snd)
  apply HasCompactSupport.intro (hK.image hf)
  intro p hp
  by_contra hne
  have hc : χ p.1.1 ≠ 0 := by intro hz; apply hne; simp [scaledPlanarHamiltonian,hz]
  have ht : deriv Real.smoothTransition p.1.2 ≠ 0 := by
    intro hz; apply hne; simp [scaledPlanarHamiltonian,hz]
  have hb : Ψ.hamiltonian ((p.1.1,χ p.1.1*Real.smoothTransition p.1.2),(a p.1.1)⁻¹ • p.2) ≠ 0 := by
    intro hz; apply hne; simp [scaledPlanarHamiltonian,hz]
  apply hp
  refine ⟨(p.1,(a p.1.1)⁻¹ • p.2),⟨⟨subset_closure hc,subset_closure ht⟩,?_⟩,?_⟩
  · exact ⟨_,subset_closure hb,rfl⟩
  · dsimp [f]
    rw [smul_inv_smul₀ (hn p.1.1)]

theorem scaledPlanarTrace_continuous (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : Continuous a) (hn : ∀ y, a y ≠ 0) (hχ : Continuous χ) :
    Continuous (fun p : (P × ℝ) × Plane => scaledPlanarTrace Ψ a χ p.1.1 p.1.2 p.2) := by
  unfold scaledPlanarTrace
  exact (ha.comp continuous_fst.fst).smul (Ψ.continuous.comp
    ((continuous_fst.fst.prodMk ((hχ.comp continuous_fst.fst).mul
      (Real.smoothTransition.continuous.comp continuous_fst.snd))).prodMk
        (((ha.inv₀ hn).comp continuous_fst.fst).smul continuous_snd)))

theorem scaledPlanarTrace_zero (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (hn : ∀ y, a y ≠ 0) (y : P) (x : Plane) :
    scaledPlanarTrace Ψ a χ y 0 x = x := by
  simp only [scaledPlanarTrace,Real.smoothTransition.zero_of_nonpos le_rfl,mul_zero,Ψ.zero]
  exact smul_inv_smul₀ (hn y) x

theorem scaledPlanarTrace_flow (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (hn : ∀ y, a y ≠ 0) (y : P) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => scaledPlanarTrace Ψ a χ y s x)
      (planarHamiltonianField (fderiv ℝ (fun z => scaledPlanarHamiltonian Ψ a χ ((y,t),z))
        (scaledPlanarTrace Ψ a χ y t x))) t := by
  have hβ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt
  have hd := ((Ψ.flow y (χ y*Real.smoothTransition t) ((a y)⁻¹ • x)).scomp t
    (hβ.const_mul (χ y))).const_smul (a y)
  have hs : Differentiable ℝ (fun z => Ψ.hamiltonian ((y,χ y*Real.smoothTransition t),z)) :=
    (Ψ.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  dsimp only [scaledPlanarHamiltonian]
  rw [scaled_planar_fderiv hs (hn y),planarHamiltonianField_smul]
  simp only [scaledPlanarTrace,inv_smul_smul₀ (hn y)]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [smul_smul]
  congr 1
  ring

def PlanarHamiltonianMotion.scaled (Ψ : PlanarHamiltonianMotion P)
    (a χ : P → ℝ) (ha : ContDiff ℝ ∞ a) (hn : ∀ y, a y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) : PlanarHamiltonianMotion P where
  hamiltonian := scaledPlanarHamiltonian Ψ a χ
  smooth := scaledPlanarHamiltonian_smooth Ψ ha hn hχ
  compact := scaledPlanarHamiltonian_compact Ψ ha.continuous hn hχc
  trace := scaledPlanarTrace Ψ a χ
  continuous := scaledPlanarTrace_continuous Ψ ha.continuous hn hχ.continuous
  zero := scaledPlanarTrace_zero Ψ hn
  flow := scaledPlanarTrace_flow Ψ hn

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_CartesianMomentSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian Comparison

variable {m N : ℕ}

def planeRegion (b : Fin N → Moments m) (c : Fin N → ℝ) : Set (PlanePhase (Fin m)) :=
  planeMoments ⁻¹' region b c

def globalSliceFamily (F : C(Moments m,ℝ)) (j : Fin m) : C(Moments m × ℝ,ℝ) where
  toFun p := F (assemble j (baseProjection j p.1) p.2)
  continuous_toFun := F.continuous.comp (by
    apply continuous_pi
    intro i
    by_cases hi : i=j
    · simp only [assemble,hi,dite_eq_left]; exact continuous_snd
    · simp only [assemble,dite_eq_right hi,baseProjection]
      exact (continuous_apply i).comp continuous_fst)

end PackingSufficiencySupport.MomentPolytope

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_DisjointClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : E →L[ℝ] E →L[ℝ] ℝ}
namespace CompactHamiltonianIsotopy

def concatMap (Φ Ψ : CompactHamiltonianIsotopy A) (t : ℝ) : E ≃ₜ E :=
  (Ψ.map (firstClock t)).trans (Φ.map (secondClock t))

def concatHamiltonian (Φ Ψ : CompactHamiltonianIsotopy A) : ℝ × E → ℝ :=
  reparamHamiltonian Ψ.hamiltonian firstClock + reparamHamiltonian Φ.hamiltonian secondClock

theorem concatHamiltonian_smooth (Φ Ψ : CompactHamiltonianIsotopy A) :
    ContDiff ℝ ∞ (concatHamiltonian Φ Ψ) :=
  (reparamHamiltonian_smooth Ψ.hamiltonian_smooth firstClock_smooth).add
    (reparamHamiltonian_smooth Φ.hamiltonian_smooth secondClock_smooth)

theorem concatHamiltonian_compact (Φ Ψ : CompactHamiltonianIsotopy A) :
    HasCompactSupport (concatHamiltonian Φ Ψ) :=
  (reparamHamiltonian_compact Ψ.compact firstClock firstClock_deriv_compact).add
    (reparamHamiltonian_compact Φ.compact secondClock secondClock_deriv_compact)

theorem concatMap_smooth (Φ Ψ : CompactHamiltonianIsotopy A) :
    ContDiff ℝ ∞ (fun p : ℝ × E => concatMap Φ Ψ p.1 p.2) :=
  Φ.smooth.comp ((secondClock_smooth.comp contDiff_fst).prodMk
    (Ψ.smooth.comp ((firstClock_smooth.comp contDiff_fst).prodMk contDiff_snd)))

theorem concatMap_inverse_smooth (Φ Ψ : CompactHamiltonianIsotopy A) :
    ContDiff ℝ ∞ (fun p : ℝ × E => (concatMap Φ Ψ p.1).symm p.2) :=
  Ψ.inverse_smooth.comp ((firstClock_smooth.comp contDiff_fst).prodMk
    (Φ.inverse_smooth.comp ((secondClock_smooth.comp contDiff_fst).prodMk contDiff_snd)))

@[simp] theorem concatMap_zero (Φ Ψ : CompactHamiltonianIsotopy A) :
    concatMap Φ Ψ 0 = Homeomorph.refl E := by
  simp only [concatMap,firstClock_zero,secondClock_zero,Φ.zero,Ψ.zero]
  rfl

@[simp] theorem concatMap_one (Φ Ψ : CompactHamiltonianIsotopy A) (x : E) :
    concatMap Φ Ψ 1 x = Φ.map 1 (Ψ.map 1 x) := by
  simp only [concatMap,firstClock_one,secondClock_one,Homeomorph.trans_apply]

theorem concatMap_flow (Φ Ψ : CompactHamiltonianIsotopy A) (t : ℝ) (x : E) :
    HasDerivAt (fun s => concatMap Φ Ψ s x)
      (hamiltonianField A (concatHamiltonian Φ Ψ) (t,concatMap Φ Ψ t x)) t := by
  rw [concatHamiltonian,hamiltonianField_add
    (A := A) (reparamHamiltonian_smooth Ψ.hamiltonian_smooth firstClock_smooth)
    (reparamHamiltonian_smooth Φ.hamiltonian_smooth secondClock_smooth),
    hamiltonianField_reparam A Ψ.hamiltonian_smooth firstClock_smooth,
    hamiltonianField_reparam A Φ.hamiltonian_smooth secondClock_smooth]
  by_cases ht : t ≤ 1/2
  · have ht' : t < 2/3 := by linarith
    have he : (fun s => concatMap Φ Ψ s x) =ᶠ[𝓝 t]
        (fun s => Ψ.map (firstClock s) x) := by
      filter_upwards [secondClock_locally_zero ht'] with s hs
      simp only [concatMap,Homeomorph.trans_apply,hs,Φ.zero,Homeomorph.refl_apply,id_eq]
    rw [secondClock_deriv_zero ht',zero_smul,add_zero,he.eq_of_nhds]
    exact ((Ψ.flow (firstClock t) x).scomp t
      ((firstClock_smooth.differentiable (by simp) t).hasDerivAt)).congr_of_eventuallyEq he
  · have ht' : 1/3 < t := by linarith
    have he : (fun s => concatMap Φ Ψ s x) =ᶠ[𝓝 t]
        (fun s => Φ.map (secondClock s) (Ψ.map 1 x)) := by
      filter_upwards [firstClock_locally_one ht'] with s hs
      simp only [concatMap,Homeomorph.trans_apply,hs]
    rw [firstClock_deriv_zero ht',zero_smul,zero_add,he.eq_of_nhds]
    exact ((Φ.flow (secondClock t) (Ψ.map 1 x)).scomp t
      ((secondClock_smooth.differentiable (by simp) t).hasDerivAt)).congr_of_eventuallyEq he

theorem concatMap_symplectic (Φ Ψ : CompactHamiltonianIsotopy A) (t : ℝ) (x v w : E) :
    A (fderiv ℝ (concatMap Φ Ψ t) x v) (fderiv ℝ (concatMap Φ Ψ t) x w) = A v w := by
  change A (fderiv ℝ ((Φ.map (secondClock t)) ∘ (Ψ.map (firstClock t))) x v)
    (fderiv ℝ ((Φ.map (secondClock t)) ∘ (Ψ.map (firstClock t))) x w) = _
  rw [fderiv_comp x ((Φ.map_smooth _).differentiable (by simp) _)
    ((Ψ.map_smooth _).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply,Φ.symplectic,Ψ.symplectic]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

def after (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    (Φ Ψ : CompactHamiltonianIsotopy A) : CompactHamiltonianIsotopy A where
  map := concatMap Φ Ψ
  smooth := concatMap_smooth Φ Ψ
  inverse_smooth := concatMap_inverse_smooth Φ Ψ
  zero := concatMap_zero Φ Ψ
  hamiltonian := concatHamiltonian Φ Ψ
  hamiltonian_smooth := concatHamiltonian_smooth Φ Ψ
  compact := concatHamiltonian_compact Φ Ψ
  flow := concatMap_flow Φ Ψ
  symplectic := concatMap_symplectic Φ Ψ
  fixed := by
    intro t x hx
    have hx' : concatMap Φ Ψ 0 x ∉ Prod.snd '' tsupport (concatHamiltonian Φ Ψ) := by
      simpa only [concatMap_zero,Homeomorph.refl_apply,id_eq] using hx
    have he := hamiltonian_trajectory_fixed hA hskew (concatHamiltonian_smooth Φ Ψ)
      (concatHamiltonian_compact Φ Ψ)
      ((concatMap_smooth Φ Ψ).continuous.comp (continuous_id.prodMk continuous_const))
      (fun t => concatMap_flow Φ Ψ t x) hx' t
    change concatMap Φ Ψ t x = concatMap Φ Ψ 0 x at he
    simpa only [concatMap_zero,Homeomorph.refl_apply,id_eq] using he

end CompactHamiltonianIsotopy

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy
open scoped ContDiff Topology BigOperators
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def refl (A : E →L[ℝ] E →L[ℝ] ℝ) : CompactHamiltonianIsotopy A where
  map := fun _ => Homeomorph.refl E
  smooth := contDiff_snd
  inverse_smooth := contDiff_snd
  zero := rfl
  hamiltonian := 0
  hamiltonian_smooth := contDiff_const
  compact := by simp [HasCompactSupport]
  flow := by
    intro t x
    simpa only [hamiltonianField,formMoserField,spatialDifferential,
      fderiv_zero,Pi.zero_apply,ContinuousLinearMap.zero_comp,map_zero,neg_zero,
      Homeomorph.refl_apply,id_eq] using hasDerivAt_const t x
  symplectic := by intro t x v w; simp
  fixed := fun _ _ _ => rfl

end PackingSufficiencySupport.Hamiltonian.CompactHamiltonianIsotopy

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_SurfaceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators Pointwise
open Set Function MeasureTheory
open Hamiltonian Comparison

def strictRegion {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ) : Set (Moments m) :=
  {p | (∀ j,0≤p j) ∧ ∀ ν,(∑ j,b ν j*p j) < c ν}

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def surfaceFormRatio (Λ Ω : ManifoldTwoForm Plane M) (x : M) : ℝ :=
  chartTwoForm Ω x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1) /
    chartTwoForm Λ x (extChartAt 𝓘(ℝ,Plane) x x) (1,0) (0,1)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_CubicPhysicalLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

def sixModelBounds : Fin 2 → Moments 2 := ![![1,0],![1,1]]

def sixModelDensity (s b : ℝ) (p : Moments 2) : ℝ :=
  9*(b-∑ j,p j)-2*max (s-∑ j,p j) 0

def sixModelGap {ι : Type*} [Fintype ι] (s b : ℝ) (r : ι → ℝ) (p : Moments 2) : ℝ :=
  sixModelDensity s b p-∑ i,max (r i-∑ j,p j) 0

end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RadialDiskSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment FiniteMoment.Radial

variable {ι κ X : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def coefficientSquares (G : ι → κ → ℂ) : ι → ℝ := fun i => phaseSq (complexCartesian (G i))

def normalizedToricLift (k : ι → ℕ × ℕ) (G : ι → κ → ℂ) (z : DiskPair) : ι × κ → ℂ :=
  toricLift k G (diskInverse k (coefficientSquares G) z)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff BigOperators
open Set Function
open Hamiltonian FiniteMoment FiniteMoment.Radial DiagonalQuadrics

def physicalDiskCoordinates (L : ℝ) : PlanePhase (Fin 2) →L[ℝ] DiskPair :=
  Real.sqrt (L*Real.pi) •
    (((ContinuousLinearMap.proj (0 : Fin 2)).comp (complexCartesian (ι := Fin 2)).symm.toContinuousLinearMap).prod
      ((ContinuousLinearMap.proj (1 : Fin 2)).comp (complexCartesian (ι := Fin 2)).symm.toContinuousLinearMap))

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def physicalPolynomialLift {A B : ℕ} (D S : ℕ) (L : ℝ)
    (x : BaseCurve × PlanePhase (Fin 2)) : TrapezoidWeight A B × WeightedHomogeneousIndex → ℂ :=
  normalizedToricLift latticeIndex (cubicCoefficients D S x.1) (physicalDiskCoordinates L x.2)

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CubicToricAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def physicalDiskRecovery (L : ℝ) (z : DiskPair) : PlanePhase (Fin 2) :=
  (Real.sqrt (L*Real.pi))⁻¹ • complexCartesian ![z.1,z.2]

end PackingSufficiencySupport.CubicModel

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Projective_SixLargeCubicPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 def outerConePrimitive {A B : ℕ} (L S : ℕ) (c t δ : ℝ) : CubicAmbient → CubicAmbient →L[ℝ] ℝ :=
  primitivePullback (hopfPrimitive c)
    (fun p => complexCartesian (outerConePolynomial (A := A) (B := B) L S t (δ,p)))

end PackingSufficiencySupport.CubicModel
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_SixLargeQuadricPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def radialSymplectization (z : PlanePhase ι) (α : PlanePhase ι →L[ℝ] ℝ)
    (C : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ) :=
  (2:ℝ) • ((phaseDot z).smulRight α-α.smulRight (phaseDot z))+(phaseSq z) • C

def mixedHopfPrimitive (F : PlanePhase ι → PlanePhase κ) (c d : ℝ) :
    PlanePhase ι → PlanePhase ι →L[ℝ] ℝ :=
  (1-2*d)•hopfPrimitive c+d•primitivePullback (hopfPrimitive c) F

def mixedHopfForm (F : PlanePhase ι → PlanePhase κ) (c d : ℝ) :=
  euclideanExteriorOneForm (mixedHopfPrimitive F c d)

def homogeneousConePrimitive (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  phaseSq z•mixedHopfPrimitive F c d z

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hopfCurvaturePullback (c : ℝ) (G : E → (ι → ℂ)) (x : E) (v w : E) : ℝ :=
  hopfForm c (complexCartesian (G x))
    (fderiv ℝ (fun y => complexCartesian (G y)) x v)
    (fderiv ℝ (fun y => complexCartesian (G y)) x w)

def mixedHopfCurvaturePullback (P : (ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (G : E → (ι → ℂ)) (x : E) (v w : E) : ℝ :=
  (1-2*d)*hopfCurvaturePullback c G x v w+
    d*hopfCurvaturePullback c (fun y => P (G y)) x v w

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeHopfDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def degreeHopfPrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    : PlanePhase ι → PlanePhase ι →L[ℝ] ℝ :=
  (1-q*d)•hopfPrimitive c+d•primitivePullback (hopfPrimitive c) F

 def degreeHopfForm (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ) :=
  euclideanExteriorOneForm (degreeHopfPrimitive q F c d)

 def degreeConePrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  phaseSq z•degreeHopfPrimitive q F c d z

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {q : ℝ} {ℓ : ℕ}

def degreeHopfCurvaturePullback (q : ℝ) (P : (ι → ℂ) → (κ → ℂ)) (c d : ℝ)
    (G : E → (ι → ℂ)) (x : E) (v w : E) : ℝ :=
  (1-q*d)*hopfCurvaturePullback c G x v w+
    d*hopfCurvaturePullback c (fun y => P (G y)) x v w

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

 def degreeAffineForm (q : ℝ) (P : (Option ι → ℂ) → (κ → ℂ)) (c d : ℝ) (x : ι → ℂ) :
    (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  (1-q*d)•(hopfForm c (complexCartesian (complexAffineLift x))).bilinearComp
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift y)) x)
    (fderiv ℝ (fun y => complexCartesian (complexAffineLift y)) x)+
  d•(hopfForm c (complexCartesian (P (complexAffineLift x)))).bilinearComp
    (fderiv ℝ (fun y => complexCartesian (P (complexAffineLift y))) x)
    (fderiv ℝ (fun y => complexCartesian (P (complexAffineLift y))) x)

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_CompactUniformCentral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

 def degreeHopfDifference (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c : ℝ) :=
  primitivePullback (hopfPrimitive c) F-q•hopfPrimitive c

 def radialDegreeConePrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c : ℝ)
    (d : ℝ → ℝ) (z : PlanePhase ι) := degreeConePrimitive q F c (d (phaseSq z)) z

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldExteriorNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory

variable {ι κ : Type} [Fintype ι] [Fintype κ]

 def cutoffDegreePrimitive (q : ℝ) (F : PlanePhase ι → PlanePhase κ) (c d : ℝ)
    (χ : ℝ → ℝ) (t : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  c•standardLiouville z+(t*d*χ (phaseSq z))•(phaseSq z•degreeHopfDifference q F c z)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeRadialMoser
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.affineComplex_cartesian _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_none _root_.OAI.PackingSufficiencySupport.Hamiltonian.phaseInfinityInclusion_some
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators
section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def phaseShell (a b : ℝ) : Set (PlanePhase ι) := phaseSq ⁻¹' Icc a b

def homogeneousConeField (F : PlanePhase ι → PlanePhase κ) (c d s : ℝ) (z : PlanePhase ι) :=
  -(euclideanExteriorOneForm (homogeneousConePrimitive F c (s*d)) z).inverse
    (homogeneousConePrimitive F c d z-homogeneousConePrimitive F c 0 z)

end

variable {ι : Type} [Fintype ι]

 omit [Fintype ι] in
 theorem phaseRotate_apply (s : ℝ) (z : PlanePhase ι) :
    phaseRotate s z=Real.cos s•z+Real.sin s•phaseJ z := rfl

 theorem phaseRotate_smooth : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => phaseRotate p.1 p.2) := by
  simp only [phaseRotate_apply]
  exact (Real.contDiff_cos.comp contDiff_fst).smul contDiff_snd |>.add
    ((Real.contDiff_sin.comp contDiff_fst).smul ((phaseJ (ι := ι)).contDiff.comp contDiff_snd))

 omit [Fintype ι] in
 theorem phaseRotate_add (s t : ℝ) (z : PlanePhase ι) :
    phaseRotate (s+t) z=phaseRotate s (phaseRotate t z) := by
  ext i <;> simp only [phaseRotate_apply,Pi.add_apply,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_add,Prod.snd_add,phaseJ_apply,smul_eq_mul,Real.cos_add,Real.sin_add] <;> ring

 omit [Fintype ι] in
 theorem phaseRotate_period (s : ℝ) (z : PlanePhase ι) :
    phaseRotate (s+2*Real.pi) z=phaseRotate s z := by
  simp only [phaseRotate_apply,Real.cos_add_two_pi,Real.sin_add_two_pi]

 theorem phaseCircle_smooth :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,PlanePhase ι)) 𝓘(ℝ,PlanePhase ι) ∞
      (fun p : ℝ × PlanePhase ι => phaseRotate (2*Real.pi*p.1) p.2) := by
  let L : ℝ × PlanePhase ι →L[ℝ] ℝ × PlanePhase ι :=
    ((2*Real.pi) • ContinuousLinearMap.fst ℝ ℝ (PlanePhase ι)).prod
      (ContinuousLinearMap.snd ℝ ℝ (PlanePhase ι))
  have hh0 : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => phaseRotate p.1 p.2) := phaseRotate_smooth
  have hh1 : ContDiff ℝ ∞ ((fun p : ℝ × PlanePhase ι => phaseRotate p.1 p.2) ∘ L) :=
    hh0.comp L.contDiff
  have hh : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => phaseRotate (2*Real.pi*p.1) p.2) := by
    simpa only [Function.comp_def,L,ContinuousLinearMap.prod_apply,smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul] using hh1
  rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
  exact hh.contMDiff

 def phaseCircleAction : SmoothCircleAction (PlanePhase ι) (PlanePhase ι) where
  toFun p := phaseRotate (2*Real.pi*p.1) p.2
  smooth := phaseCircle_smooth
  zero z := by simp
  add s t z := by rw [mul_add,phaseRotate_add]
  period s z := by rw [mul_add,mul_one,phaseRotate_period]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hopf_DegreeRelativeShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold
open scoped ContDiff Manifold Topology BigOperators

section

variable {ι : Type} [Fintype ι]

 def phaseInfinityProjection : PlanePhase (Option ι) →L[ℝ] PlanePhase ι :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (some i)

end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def complexConjugate (f : PlanePhase ι → PlanePhase κ) : (ι → ℂ) → (κ → ℂ) :=
  fun z => complexCartesian.symm (f (complexCartesian z))

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_SphereCartesianDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

@[simp] theorem affineComplexEquiv_toCLM (m : ℕ) :
    (affineComplexEquiv m).toContinuousLinearMap=(affineComplex m).restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro z
  exact affineComplexEquiv_apply m z

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
section

def optionPhaseAmbient (m : ℕ) : PlanePhase (Option (Fin m)) ≃L[ℝ] Ambient (m+1) :=
  complexCartesian.symm.trans (optionComplexAmbient m)

variable {ι : Type*} [Fintype ι]

def fsBallHomeomorph {a : ℝ} (ha : 0<a) : PlanePhase ι ≃ₜ phaseOpenBall (ι := ι) a where
  toEquiv :=
    { toFun := fun z => ⟨fsBallMap a z,fsBallMap_mem ha z⟩
      invFun := fun z => fsAffineMap a z.val
      left_inv := fsAffineMap_fsBallMap ha
      right_inv := by intro z; apply Subtype.ext; exact fsBallMap_fsAffineMap ha z.property }
  continuous_toFun := (fsBallMap_smooth a).continuous.subtype_mk _
  continuous_invFun := (fsAffineMap_smoothOn a).continuousOn.comp_continuous
    continuous_subtype_val (fun z => z.property)

end

 def complexFSAffine {n : ℕ} (a : ℝ) (x : Ambient n) : Ambient n :=
   complexCartesian.symm (fsAffineMap a (complexCartesian x))

 theorem complexCartesian_ball_into {n : ℕ} {a : ℝ}
     (x : openBall n (Real.pi*a)) : complexCartesian x.val∈phaseOpenBall a := by
   change phaseSq (complexCartesian x.val)<a
   rw [complexCartesian_sq]
   exact (mul_lt_mul_iff_right₀ Real.pi_pos).mp x.property

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_CubicBubbleSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open scoped Topology
open Set Function MeasureTheory
open scoped Manifold
open Manifold
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 def firstLinePrimitive (α : ManifoldOneForm E M) : ManifoldOneForm (E × Plane) (M × Plane) :=
  productCouplingPrimitive planarArea (fun z => (1-radialArea z) • α)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

 def firstLineLift (g : E → F) (f : E → ℝ) (x : E × Plane) : F × Plane :=
  (g x.1,planeRotate (2*Real.pi*f x.1) x.2)

end

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 def firstLineBaseMap (g : M → N) (x : M × Plane) : N × Plane := (g x.1,x.2)

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Models_LiouvilleRadialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

def largeModelBounds (q : ℕ) (h₂ : ℝ) : Fin 2 → Moments (q+1) :=
  ![Fin.cons 1 (fun _ => 0),Fin.cons h₂ (fun _ => 1)]

def largeModelDensity (q : ℕ) (p : Moments (q+1)) : ℝ :=
  (2:ℝ)^q*(1-p 0-2*∑ j : Fin q,p j.succ)

def largeModelGap {q : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ) (p : Moments (q+1)) : ℝ :=
  largeModelDensity q p-∑ i,max (r i-∑ j,p j) 0

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance liouvilleRadialSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

 def largeHorizontalPrimitive (p : Fin (q+1) → ℝ) : ManifoldOneForm Plane (locus a) :=
  largeNormalCoefficient q p • curveFSPrimitive a (1/Real.pi)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_TailLineCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold

 def normalTail (q : ℕ) : PlanePhase (Fin (q+1)) →L[ℝ] PlanePhase (Fin q) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.succ)
 def normalHead (q : ℕ) : PlanePhase (Fin (q+1)) →L[ℝ] Plane := ContinuousLinearMap.proj 0

 def normalSplit (q : ℕ) : PlanePhase (Fin (q+1)) ≃L[ℝ] PlanePhase (Fin q) × Plane :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun z => (normalTail q z,normalHead q z)
      invFun := fun x => Fin.cons x.2 x.1
      left_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
      right_inv := by intro x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] {q : ℕ}

 def firstTailMap (s : PlanePhase (Fin (q+1)) → ℝ) (x : M × PlanePhase (Fin (q+1))) :
    (M × PlanePhase (Fin q)) × Plane := ((x.1,s x.2 • normalTail q x.2),normalHead q x.2)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open NormalLift Hamiltonian
open scoped Manifold
open Manifold
section

variable {m : ℕ}

def regularLocus (m : ℕ) : Set (Affine m) := ⋃ c,regularCoordinate c

def realJacobian (z : Affine m) : Affine m →L[ℝ] (Fin m → ℂ) :=
  (jacobian z).restrictScalars ℝ

def normalLift (z : Affine m) : (Fin m → ℂ) →L[ℝ] Affine m :=
  finiteRightLift _ _ (realJacobian z)

end

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open scoped BigOperators
section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def normalRadial (a : ℝ) (p : PlanePhase ι × PlanePhase κ) : PlanePhase ι × PlanePhase κ :=
  (p.1,(1+phaseSq p.1) • fsAffineMap a p.2)

def conePrimitive (c d : ℝ) (p : PlanePhase ι × PlanePhase κ) :
    (PlanePhase ι × PlanePhase κ) →L[ℝ] ℝ :=
  ((1-2*d) • affineFSPrimitive c p.1).comp (ContinuousLinearMap.fst ℝ _ _)+
    (c*d/(2*coneDenominator p)) •
      ((2*(1+phaseSq p.1)) • (phaseArea p.1).comp (ContinuousLinearMap.fst ℝ _ _)+
        (phaseArea p.2).comp (ContinuousLinearMap.snd ℝ _ _))

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian

variable {m : ℕ}

 def normalGraph (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    (Option (Fin m) → ℂ) × (Fin m → ℂ) :=
  (affineComplex m z,fun j => (t:ℂ)⁻¹*equations a z j)

 def normalConeCoordinates (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    PlanePhase (Option (Fin m)) × PlanePhase (Fin m) :=
  (affinePhase m z,complexCartesian (normalGraph a t z).2)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Normal_QuadricMovingCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian
open scoped BigOperators
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

abbrev ConeModel (m : ℕ) := RealModel × (Fin m → ℂ)
abbrev ConeSpace := locus a × (Fin m → ℂ)
abbrev ConeTarget (m : ℕ) := PlanePhase (Option (Fin m)) × PlanePhase (Fin m)

 def movingConeCoordinates (Ψ : ℝ × ConeSpace a → Affine m) (p : ℝ × ConeSpace a) : ConeTarget m :=
  (affinePhase m (Ψ p),complexCartesian p.2.2)

 def centralConeCoordinates (p : ConeSpace a) : ConeTarget m :=
  (affinePhase m p.1.val,complexCartesian p.2)

 def centralConePrimitive (c d : ℝ) : ManifoldOneForm (ConeModel m) (ConeSpace a) :=
  manifoldPullbackOneForm (fun _ => conePrimitive c d) (centralConeCoordinates a) 0

abbrev NormalModel (m : ℕ) := RealModel × PlanePhase (Fin m)
abbrev NormalSpace := locus a × PlanePhase (Fin m)

def normalCouplingPrimitive : ManifoldOneForm (NormalModel m) (NormalSpace a) :=
  productHorizontalLift (normalHorizontalPrimitive (q := m) a 2 ∘ planeMoments)+verticalLiouville

def normalPhaseCoordinates (x : NormalSpace a) : ConeTarget m :=
  (phaseInclusion a x.1,x.2)

abbrev LargeNormalModel (m : ℕ) := RealModel × PlanePhase (Fin (m+1))
abbrev LargeNormalSpace := locus a × PlanePhase (Fin (m+1))

 def largeCouplingPrimitive : ManifoldOneForm (LargeNormalModel m) (LargeNormalSpace a) :=
  productCouplingPrimitive phaseArea (largeHorizontalPrimitive (q := m) a ∘ planeMoments)

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricLargeAmbientPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Function Filter
open Set
open Manifold
section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

 def firstDiskDomain : Set (V × Plane) := {x | radialArea x.2<1}

 def firstDiskScale (x : V × Plane) : V × Plane :=
  (Real.sqrt (1-radialArea x.2) • x.1,x.2)
 def firstDiskUnscale (x : V × Plane) : V × Plane :=
  ((Real.sqrt (1-radialArea x.2))⁻¹ • x.1,x.2)

 theorem firstDiskScale_smoothOn :
    ContDiffOn ℝ ∞ (firstDiskScale (V := V)) firstDiskDomain :=
  (((contDiffOn_const.sub (radialArea_smooth.comp contDiff_snd).contDiffOn).sqrt
    (fun _ hx => (sub_pos.mpr hx).ne')).smul contDiffOn_fst).prodMk contDiffOn_snd

 theorem firstDiskUnscale_smoothOn :
    ContDiffOn ℝ ∞ (firstDiskUnscale (V := V)) firstDiskDomain :=
  ((((contDiffOn_const.sub (radialArea_smooth.comp contDiff_snd).contDiffOn).sqrt
    (fun _ hx => (sub_pos.mpr hx).ne')).inv
      (fun _ hx => (Real.sqrt_pos.mpr (sub_pos.mpr hx)).ne')).smul contDiffOn_fst).prodMk contDiffOn_snd

 def firstDiskScaleHomeomorph : firstDiskDomain (V := V) ≃ₜ firstDiskDomain (V := V) where
  toEquiv :=
    { toFun := fun x => ⟨firstDiskScale x.val,x.property⟩
      invFun := fun x => ⟨firstDiskUnscale x.val,x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · change (Real.sqrt (1-radialArea x.val.2))⁻¹ •
            (Real.sqrt (1-radialArea x.val.2) • x.val.1)=x.val.1
          rw [smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr (sub_pos.mpr x.property)).ne',one_smul]
        · rfl
      right_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · change Real.sqrt (1-radialArea x.val.2) •
            ((Real.sqrt (1-radialArea x.val.2))⁻¹ • x.val.1)=x.val.1
          rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (sub_pos.mpr x.property)).ne',one_smul]
        · rfl }
  continuous_toFun := (firstDiskScale_smoothOn.continuousOn.comp_continuous
    continuous_subtype_val (fun x => x.property)).subtype_mk _
  continuous_invFun := (firstDiskUnscale_smoothOn.continuousOn.comp_continuous
    continuous_subtype_val (fun x => x.property)).subtype_mk _

variable {ι : Type} [Fintype ι]
 def phasePlusPlanePrimitive (x : PlanePhase ι × Plane) : (PlanePhase ι × Plane) →L[ℝ] ℝ :=
  (standardLiouville x.1).comp (ContinuousLinearMap.fst ℝ _ _)+
    (linearLiouville planarArea x.2).comp (ContinuousLinearMap.snd ℝ _ _)

 def firstDiskRadial (c : ℝ) (x : PlanePhase ι × Plane) : PlanePhase ι × Plane :=
  firstDiskScale (fsBallMap c x.1,x.2)

end

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

variable {m : ℕ}

def homogeneousCartesian (a : Fin m → ℂ) (t : ℝ) :
    PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (NormalPolynomialIndex m)) :=
  fun z => complexCartesian (homogeneousPolynomial a t (complexCartesian.symm z))

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_BallMaps_QuadricRelativeShellFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function
open Hamiltonian

 def affinePhaseEquiv (m : ℕ) : Affine m ≃L[ℝ] PlanePhase (Option (Fin m)) :=
  (affineComplexEquiv m).trans complexCartesian

@[simp] theorem affinePhaseEquiv_apply (m : ℕ) (z : Affine m) :
    affinePhaseEquiv m z=affinePhase m z := by
  simp only [affinePhaseEquiv,ContinuousLinearEquiv.trans_apply,
    affineComplexEquiv_apply,affineComplex_cartesian]

 def affineRadialTarget (m : ℕ) (c : ℝ) (z : Affine m) : Ambient (m+1) :=
  optionPhaseAmbient m (fsBallMap c (affinePhaseEquiv m z))

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators Manifold
open Set Function

 def headComplexAmbient (n : ℕ) : (Ambient n × Plane) ≃L[ℝ] Ambient (n+1) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => Fin.cons (⟨x.2.1,x.2.2⟩ : ℂ) x.1
      invFun := fun z => (fun j => z j.succ,((z 0).re,(z 0).im))
      left_inv := by intro x; rfl
      right_inv := by intro z; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_add' := by intros; funext j; exact Fin.cases rfl (fun _ => rfl) j
      map_smul' := by
        intro r x
        funext j
        refine Fin.cases ?_ (fun _ => rfl) j
        apply Complex.ext <;> simp }

@[simp] theorem headComplexAmbient_apply (n : ℕ) (x : Ambient n × Plane) :
    headComplexAmbient n x=Fin.cons (⟨x.2.1,x.2.2⟩ : ℂ) x.1 := rfl

 def phasePlusPlaneAmbient (m : ℕ) : (PlanePhase (Option (Fin m)) × Plane) ≃L[ℝ] Ambient (m+2) :=
  ((optionPhaseAmbient m).prodCongr (ContinuousLinearEquiv.refl ℝ Plane)).trans (headComplexAmbient (m+1))

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Function
open Hamiltonian
open scoped Manifold Topology
open Set

 def affineLinePhase (m : ℕ) : (Affine m × Plane) ≃L[ℝ] PlanePhase (Option (Fin m)) × Plane :=
  (affinePhaseEquiv m).prodCongr (ContinuousLinearEquiv.refl ℝ Plane)

 def affineLineRadial (m : ℕ) (x : Affine m × Plane) : PlanePhase (Option (Fin m)) × Plane :=
  firstDiskRadial (1/Real.pi) (affineLinePhase m x)

 def affineLineTarget (m : ℕ) : Affine m × Plane → Ambient (m+2) :=
  phasePlusPlaneAmbient m ∘ affineLineRadial m

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : Set ℂ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst4
local instance ptCRInst5_r9e4d86_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ptCRInst6_r9e4d86_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst11
def pointMarkedCRDeriv (J : E → E →L[ℝ] E) (p q : E) (u : COne ℂ E) (z : ℂ) :
    markedModel (E := E) K →L[ℝ] E :=
  markedDerivativeVariation z Complex.I -
    ((J (markedCurve p q u z)).comp (markedDerivativeVariation z 1) +
      ((fderiv ℝ J (markedCurve p q u z)).flip (fderiv ℝ (markedCurve p q u) z 1)).comp
        (markedVariation z))


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance testInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
local instance srInst1_r9e4d86_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance srInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}
local instance reInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance reInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

local instance caInst1_r9e4d86_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance caInst2_r9e4d86_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
def curveAreaDensity (u : ℂ → Phase n) (z : Plane) : ℝ :=
  stdOmega n (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1))



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_MeasureEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

def phaseAverage (μ : Measure X) (f : X → Phase n) : Phase n :=
  (μ.real univ)⁻¹ • (∫ x,f x ∂μ)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def horizontalEnergy (v : Plane → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ v z (1,0)) (fderiv ℝ v z (1,0))

def verticalEnergy (v : Plane → Phase n) (z : Plane) : ℝ :=
  stdDot n (fderiv ℝ v z (0,1)) (fderiv ℝ v z (0,1))


def horizontalSlice (v : Plane → Phase n) (a b y : ℝ) : ℝ :=
  ∫ x in Icc a b,horizontalEnergy v (x,y)
def verticalSlice (v : Plane → Phase n) (a b x : ℝ) : ℝ :=
  ∫ y in Icc a b,verticalEnergy v (x,y)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}


def dilatedCurve (u : ℂ → Phase n) (c : ℂ) : ℂ → Phase n := fun z => u (c*z)


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_FrozenCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open HolderCompletion
open scoped BoundedContinuousFunction
section
variable {n : ℕ}
local instance hcbInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance hcbInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

local instance hcbInst3_r9e4d86_1 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance hcbInst4_r9e4d86_1 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace
lemma lineHomotopy_slice_contDiff {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ContDiff ℝ ∞ (lineHomotopy J t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact contDiffAt_interpolateJ hJs.contDiffAt contDiffAt_const (hJ x) ht

end
section

variable {n : ℕ}
local instance fhcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fhcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

end

variable {n : ℕ}

local instance ecgInst1_r9e4d86_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ecgInst2_r9e4d86_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
def rescaledCurve (u : ℂ → Phase n) (y : ℂ) (r : ℝ) (z : ℂ) : Phase n := u (y+r • z)

lemma rescaledCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (y : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (rescaledCurve u y r) := hu.comp (contDiff_const.add (contDiff_id.const_smul r))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_MarkedCurves
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

local instance eljcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance eljcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

local instance eljcInst3_r9e4d86_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance eljcInst4_r9e4d86_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
def markedLocalCurve (u : ℂ → Phase n) (c : ℂ) (r : ℝ) (z : ℂ) : Phase n :=
  rescaledCurve u c r z-u c

lemma markedLocalCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (markedLocalCurve u c r) := (rescaledCurve_smooth hu c r).sub contDiff_const

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrK
local instance pfrC_r9e4d86_1 : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrX
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.pfrY
include hD in
lemma parametricSolution_zero_iff (hz : F (t,x)=0) :
    ∀ᶠ v in 𝓝 (t,((domCoords pkg) x).2),
      F (v.1,parametricSolution pkg hF hD v)=0 ↔ parametricObstruction pkg hF hD v=0 := by
  have hh := (parametricEssential_smooth pkg hF).contDiffAt.eventually_apply_implicitFunction
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (parametricEssential_invertible pkg hF hD)
  have hb : parametricEssential pkg F (parametricBase pkg t x)=0 := by
    change ((codCoords pkg) (F (t,(domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)))).1=0
    rw [(domCoords pkg).symm_apply_apply,hz,map_zero]; rfl
  filter_upwards [hh] with v hv
  have hfirst : ((codCoords pkg) (F (v.1,parametricSolution pkg hF hD v))).1=0 := hv.trans hb
  constructor
  · intro he
    change ((codCoords pkg) (F (v.1,parametricSolution pkg hF hD v))).2=0
    rw [he,map_zero]; rfl
  · intro he
    apply (codCoords pkg).injective
    rw [map_zero]
    exact Prod.ext hfirst he

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_SurjectiveParametricReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

include hD in
lemma surjective_parametricSolution_zero (hs : Surjective D) (hz : F (t,x)=0) :
    ∀ᶠ v in 𝓝 (t,((domCoords pkg) x).2),F (v.1,parametricSolution pkg hF hD v)=0 := by
  let := surjective_package_coker_subsingleton pkg hs
  filter_upwards [parametricSolution_zero_iff pkg hF hD hz] with v hv
  exact hv.mpr (Subsingleton.elim _ _)


end
open scoped Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_SmoothZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.SmoothZeroAtlas.prescribe_at _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

variable [CompleteSpace X] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
variable (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
    (hD : HasFDerivAt (fun y => F (t,y)) D x)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.szcK
local instance szcC_r9e4d86_1 : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.szcX
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.szcY
include hF hD in
lemma surjective_smooth_zero_chart (hs : Surjective D) (hz : F (t,x)=0) :
    ∃ c : ZeroGraphChart F pkg.decDom.X₀,c.base=(t,x) ∧ ContDiffOn ℝ ∞ c.reconstruct c.domain := by
  let P : X →L[ℝ] pkg.decDom.X₀ :=
    (ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp (domCoords pkg).toContinuousLinearMap
  let g : FiniteZeroGerm F t x (Module.finrank ℝ pkg.decDom.X₀) := {
    kernelSpace := pkg.decDom.X₀
    finite_kernel := inferInstance
    dimension := rfl
    coordinate := P
    reconstruct := parametricSolution pkg hF hD
    base := parametricSolution_base pkg hF hD
    smooth := parametricSolution_smooth pkg hF hD
    left_inv := parametricSolution_kernel_coordinate pkg hF hD
    zero := surjective_parametricSolution_zero pkg hF hD hs hz
    complete := parametric_zero_is_solution pkg hF hD hz }
  obtain ⟨c,hb,hp,hr⟩ := g.graphChart hz
  obtain ⟨S,hSo,hSa,hSs⟩ := parametricSolution_smooth_neighborhood pkg hF hD
  have hbase : (c.base.1,c.coordinate c.base.2)∈S := by
    rw [hb,hp]
    exact hSa
  let c' := c.restrict (c.domain∩S) (c.domain_open.inter hSo) inter_subset_left ⟨c.base_domain,hbase⟩
  refine ⟨c',hb,?_⟩
  change ContDiffOn ℝ ∞ c.reconstruct (c.domain∩S)
  rw [hr]
  exact hSs.mono inter_subset_right

include hF hD in
lemma smooth_common_zero_chart [FiniteDimensional ℝ E]
    (hFr : D.IsFredholm) (hs : Surjective D) (hz : F (t,x)=0)
    (hdim : Module.finrank ℝ D.ker=Module.finrank ℝ E) :
    ∃ c : ZeroGraphChart F E,c.base=(t,x) ∧ ContDiffOn ℝ ∞ c.reconstruct c.domain := by
  obtain ⟨pkg⟩ := hFr.nonempty_fredholmPackage
  let := pkg.decDom.finite_X₀
  let e : pkg.decDom.X₀ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by rwa [←pkg.ker_eq])
  obtain ⟨c,hb,hc⟩ := surjective_smooth_zero_chart pkg hF hD hs hz
  exact ⟨c.reparam e,hb,c.reparam_smooth hc e⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)

include fr in
lemma StabilizedKernelFrame.smooth_zero_chart (hF : ContDiff ℝ ∞ F)
    {t : ℝ} {x : X} {e : E} (hv : (t,x)∈V)
    (hs : Surjective ((pathSpatialDerivative F (t,x)).coprod E.subtypeL))
    (hz : finiteTargetAugment F E (t,(x,e))=0) :
    ∃ c : ZeroGraphChart (finiteTargetAugment F E) E,
      c.base=(t,(x,e)) ∧ ContDiffOn ℝ ∞ c.reconstruct c.domain := by
  let A := (pathSpatialDerivative F (t,x)).coprod E.subtypeL
  have hd : HasFDerivAt (fun w : X × E => finiteTargetAugment F E (t,w)) A (x,e) := by
    have hsl : ContDiff ℝ ∞ (fun w : X × E => finiteTargetAugment F E (t,w)) :=
      (finiteTargetAugment_smooth hF E).comp (contDiff_const.prodMk contDiff_id)
    have h := (hsl.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x,e)).hasFDerivAt
    rwa [finiteTargetAugment_spatial_derivative hF E t x e] at h
  exact smooth_common_zero_chart (finiteTargetAugment_smooth hF E) hd
    (fr.fredholm hv hs) hs hz (fr.kernelEquiv hv).finrank_eq.symm


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)}

def StabilizedKernelFrame.smoothZeroAtlas (fr : StabilizedKernelFrame F E V)
    (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
    (hs : ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) :
    SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV) := by
  classical
  have hc (v : framedZeroOpen F E V hV) :=
    fr.smooth_zero_chart hF v.property (hs _ v.property) v.val.property
  exact {
    chart := fun v => (hc v).choose
    base := fun v => (hc v).choose_spec.1
    smooth := fun v => (hc v).choose_spec.2 }


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Packings_ComplementPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

 def headPlanarMap (n : ℕ) (p : Plane → Plane) : Ambient (n+1) → Ambient (n+1) :=
  headComplexAmbient n ∘ (fun x => (x.1,p x.2)) ∘ (headComplexAmbient n).symm

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end


