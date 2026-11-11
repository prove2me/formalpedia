-- Prove2me | Definitions.Def_OAIQ240Bp020
-- name    : OAIQ240Bp020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:52:28.017731+00:00
-- url     : https://prove2.me/theorems/381879ad-c0c3-4055-94f8-11bf61646555
-- title:
--   Definitions bundle OAIQ240Bp020 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 48 definitions and 6 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedDerivative`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst15`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst16`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst17`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst18`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst20`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst21`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst22`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst11`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst12`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst13`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartNonlinearity`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.feInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTransInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle3`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle4`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle7` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Campanato_TranslatedSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Campanato/TranslatedSquare.lean), [`BallPacking_Continuation_ParameterizedImplicit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Continuation/ParameterizedImplicit.lean), [`BallPacking_Fredholm_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean), [`BallPacking_Fredholm_FreeLinearization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FreeLinearization.lean), [`BallPacking_Fredholm_PointwiseMarkedCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean), [`BallPacking_Fredholm_TranslationContinuity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean).
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp017`, `OAIQ240Bp018` and `OAIQ240Bp019` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp022`; the statements `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_contDiff_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_fderiv_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_value_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal_fredholm_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_elliptic_freeTranslation_continuous_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_observation_smoothAt_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_principal_tendsto_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_contDiff_bp240`, `OAI_PackingSufficiencySupport_CubicModel_actual_cubic_representative_packing`, `OAI_PackingSufficiencySupport_CubicModel_cubic_bubble_target_packing`, `OAI_PackingSufficiencySupport_CubicModel_cubic_radial_primitive`, `OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_exact_family_with_zero`, `OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_normal_transfer_into`, `OAI_PackingSufficiencySupport_CubicModel_exists_cubic_bubble_separated`, `OAI_PackingSufficiencySupport_CubicModel_exists_uniform_cubic_bubble_transfer`, `OAI_PackingSufficiencySupport_CubicModel_physicalArea_uniform`, `OAI_PackingSufficiencySupport_CubicModel_radialEndResidue_error`, `OAI_PackingSufficiencySupport_CubicModel_radialForm_positive`, `OAI_PackingSufficiencySupport_CubicModel_tendsto_radial_cubic_cutoff_mass`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_large_normal_packing`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_small_normal_packing`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_exists_actual_compact_normalized_dual_fixed`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_normal_exact_family`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_radial_primitive_family`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_relative_shell_map`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_largeCouplingPrimitive_invertible`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_largeHorizontalPrimitive_area_limit`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_normalCoupling_invertible`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_normalHorizontalPrimitive_area_limit`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_global_surface_final_packing`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_normal_form_packing`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_step_two`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceFirstPath_isInvertible_annular`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceFirstPath_moser_endpoint`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible_annular`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_normalize_primitive`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_circle_relative_radial_moser`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_exact_moser`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_relative_moser`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_degree_relative_shell_maps`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_final_surface_layer_packing`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_scaled_slice_rearrangement`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_surface_area_redistribution`, `OAI_PackingSufficiencySupport_Hamiltonian_horizontal_moser_endpoint`, `OAI_PackingSufficiencySupport_MomentPolytope_Annular_exhausted_surface_packing` and `OAI_PackingSufficiencySupport_MomentPolytope_finite_surface_comparison`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_contDiff_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_crSection_fderiv_eval_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualFreeChart_fderiv_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_contDiff_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_derivative_eq_linearized_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actualMarkedChart_value_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreeLinearized_fredholm_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFreePrincipal_fredholm_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_elliptic_freeTranslation_continuous_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_observation_smoothAt_bp240`, `OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_freeTranslation_principal_tendsto_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeTranslation_zero_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.fullLineEquation_contDiff_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.translationVariation_observation_smooth_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support_bp240`, `OAI_PackingSufficiencySupport_CubicModel_actual_cubic_representative_packing`, `OAI_PackingSufficiencySupport_CubicModel_cubic_bubble_target_packing`, `OAI_PackingSufficiencySupport_CubicModel_cubic_radial_primitive`, `OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_exact_family_with_zero`, `OAI_PackingSufficiencySupport_CubicModel_exists_actual_cubic_normal_transfer_into`, `OAI_PackingSufficiencySupport_CubicModel_exists_cubic_bubble_separated`, `OAI_PackingSufficiencySupport_CubicModel_exists_uniform_cubic_bubble_transfer`, `OAI_PackingSufficiencySupport_CubicModel_physicalArea_uniform`, `OAI_PackingSufficiencySupport_CubicModel_radialEndResidue_error`, `OAI_PackingSufficiencySupport_CubicModel_radialForm_positive`, `OAI_PackingSufficiencySupport_CubicModel_tendsto_radial_cubic_cutoff_mass`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_large_normal_packing`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_small_normal_packing`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_exists_actual_compact_normalized_dual_fixed`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_curveEndCutoff_partition_mass`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_normal_exact_family`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_actual_radial_primitive_family`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_polynomial_target_embedding`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_exact_affine_moser`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_relative_shell_map`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_largeCouplingPrimitive_invertible`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_largeHorizontalPrimitive_area_limit`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_normalCoupling_invertible`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_normalHorizontalPrimitive_area_limit`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_tendsto_curveCutoff_bounded_residue`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_global_surface_final_packing`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_normal_form_packing`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_exists_surface_step_two`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceFirstPath_isInvertible_annular`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceFirstPath_moser_endpoint`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_globalSurfaceSecondPath_isInvertible_annular`, `OAI_PackingSufficiencySupport_Hamiltonian_AnnularHandleData_normalize_primitive`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_circle_relative_radial_moser`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_exact_fibre_embedding`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_exact_fibre_embedding_into`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_exact_moser`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_relative_moser`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_degree_relative_shell_maps`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_final_surface_layer_packing`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_scaled_slice_rearrangement`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_surface_area_redistribution`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_uniform_compact_exact_fibre_embedding_central_into`, `OAI_PackingSufficiencySupport_Hamiltonian_horizontal_moser_endpoint`, `OAI_PackingSufficiencySupport_Hamiltonian_manifold_exact_sublevel_moser`, `OAI_PackingSufficiencySupport_MomentPolytope_Annular_exhausted_surface_packing`, `OAI_PackingSufficiencySupport_MomentPolytope_finite_surface_comparison`, `OAI_PackingSufficiencySupport_actual_complement_packing` and `OAI_PackingSufficiencySupport_hasPacking_six_large_normalized`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp017
import Definitions.Def_OAIQ240Bp018
import Definitions.Def_OAIQ240Bp019

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst8
local instance markedChartInst13_r554482_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst14_r554482_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
variable {P : E → E →L[ℝ] E} (hP : BoundedCThree P) (b : ContDiffBump (0:ℂ))

def chartNonlinearity (p q : E) (u h : COne ℂ E) : HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip
    (truncatedCoefficient hP b p q u h) (markedDX p q u h)

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst12
def markedChart (p q : E) (u h : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)) (u+h) - supportedSourceCutoff b (chartNonlinearity hP b p q u.val h.val)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.chartDerInst8
lemma compactJPerturbation_smooth {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (compactJPerturbation J) := hJ.sub contDiff_const

variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) {B : ℝ}
    (hstd : ∀ x, B < ‖x‖ → J x = standardJ n)

include hJ hstd in
theorem compactJPerturbationBound : BoundedCThree (compactJPerturbation J) :=
  boundedCThree_of_compactSupport (compactJPerturbation_smooth hJ) (compactJPerturbation_compact hstd)

variable (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance chartDerInst9 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance chartDerInst10 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance chartDerInst11 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (chartDerInst9 (n := n) b).toAddCommGroup
local instance chartDerInst12 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (chartDerInst10 (n := n) b).toModule
local instance chartDerInst13 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (chartDerInst9 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))

def actualMarkedChart := markedChart (compactJPerturbationBound hJ hstd) b p q u


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
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))
  {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst7
local instance afInst8 : NormedSpace ℝ (freeModel (E := Phase n) K) := inferInstance
local instance afInst9 : AddCommGroup (freeModel (E := Phase n) K) := (afInst7 (n := n) (K := K)).toAddCommGroup
local instance afInst10 : Module ℝ (freeModel (E := Phase n) K) := (afInst8 (n := n) (K := K)).toModule
local instance afInst11 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance afInst12_r554482_1 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance afInst13 : AddCommGroup (markedModel (E := Phase n) K) := (afInst11 (n := n) (K := K)).toAddCommGroup
local instance afInst15 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance afInst16 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
local instance afInst17 : AddCommGroup (supportedHolder (E := Phase n) K) := (afInst15 (n := n) (K := K)).toAddCommGroup
local instance afInst18 : Module ℝ (supportedHolder (E := Phase n) K) := (afInst16 (n := n) (K := K)).toModule

def completedFreePrincipal : freeModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  freePrincipal (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz))

def completedFreeLinearized : freeModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  freeLinearized (jetValueCLM _ (completedStructureJet hJ hstd p q u)) (completedQ hJ hstd p q u)
    (fun z hz => hstd _ (he z hz)) (completedQ_zero_outside hJ hstd p q u he)

variable (b : ContDiffBump (0:ℂ))
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst19
local instance afInst20 : NormedSpace ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance afInst21 : AddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst19 (n := n) b).toAddCommGroup
local instance afInst22 : Module ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst20 (n := n) b).toModule
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.afInst23
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope (markedSlope p q w.val)) (w.val+v.val) z‖)

def actualFreeChart := freeChart (actualStructureBound hJ hstd) b p (markedSlope p q w.val) w

include hesc in
lemma free_escape_base : ∀ z ∉ Metric.closedBall (0:ℂ) b.rOut, B < ‖markedCurve p q w.val z‖ := by
  intro z hz
  have hz' : b.rIn ≤ ‖z‖ := by
    have ht : b.rOut < ‖z‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact (b.rIn_lt_rOut.trans ht).le
  have hh := hesc.self_of_nhds z hz'
  simpa only [Submodule.coe_zero,add_zero,affineCurve,affine,complexSlope_apply,markedCurve] using hh

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance freeTransInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeTransInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

local instance freeTransInst3_r554482_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4_r554482_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
lemma translationVariation_CR (a : E) (u : COne ℂ E) (t z : ℂ) :
    valueCLM _ (standardJetCR (translationVariation a u t)) z =
      valueCLM _ (standardJetCR u) (z+t)-valueCLM _ (standardJetCR u) z := by
  simp only [standardJetCR_value,translationVariation_deriv,sub_apply,smul_sub]
  abel

lemma translationVariation_mem {R S : ℝ} (hRS : R+1 ≤ S)
    (a : E) (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))
    {t : ℂ} (ht : ‖t‖≤1) : translationVariation a u.val t∈freeModel (E := E) (Metric.closedBall (0:ℂ) S) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hzS : S < ‖z‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hzR : z∉Metric.closedBall (0:ℂ) R := by
    simp only [Metric.mem_closedBall,dist_zero_right,not_le]
    linarith
  have hztR : z+t∉Metric.closedBall (0:ℂ) R := by
    simp only [Metric.mem_closedBall,dist_zero_right,not_le]
    have hnorm : ‖z‖ ≤ ‖z+t‖+‖t‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (z+t) t
    linarith
  change valueCLM _ (standardJetCR (translationVariation a u.val t)) z = 0
  have h0 : valueCLM _ (standardJetCR u.val) z=0 := (mem_supportedHolder _ _).mp u.property z hzR
  have h1 : valueCLM _ (standardJetCR u.val) (z+t)=0 := (mem_supportedHolder _ _).mp u.property (z+t) hztR
  rw [translationVariation_CR,h1,h0,sub_self]

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))

local instance freeTransInst5_r554482_1 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance freeTransInst6_r554482_1 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
def freeTranslation (t : ℂ) : freeModel (E := E) (Metric.closedBall (0:ℂ) S) :=
  if ht : ‖t‖≤1 then ⟨translationVariation a u.val t,translationVariation_mem hRS a u ht⟩ else 0

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance feInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst6
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst8
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst9
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst10
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst11
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst13
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.actFredInst15
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

def actualMarkedDerivative := fderiv ℝ (actualMarkedChart hJ hstd b p q u) 0

end
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.azInst2
local instance azInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def curveSquareAverage (w : ℂ → Phase n) (c : ℂ) (r : ℝ) : Phase n :=
  phaseAverage (squareMeasure (-r) r) (realCurve (centeredCurve w c))


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ParameterizedImplicit
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section
variable {n : ℕ}
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle2
local instance gle3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gle4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gle5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gle6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gle1
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance gle7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle9 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle10 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

end
section

variable {n : ℕ}
local instance glf1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance glf2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance glf3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance glf4_r554482_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance glf5_r554482_1 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf6_r554482_1 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf7 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf8_r554482_1 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf11_r554482_1 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf7 (n := n) b).toAddCommGroup
local instance glf14_r554482_1 : TopologicalSpace (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (glf7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : MarkedEscapeNeighborhood b p q w.val B)

include hstd in
lemma fullTime_slice_outside : ∀ x,B<‖x‖ →lineHomotopy J (fullTime t) x=standardJ n := by
  intro x hx
  change interpolateJ (J x) (fullTime t)=standardJ n
  rw [hstd x hx]
  exact interpolateJ_standard (fullTime_range t)

end

variable {n : ℕ}
local instance gid1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gid2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
variable (b : ContDiffBump (0:ℂ))
local instance gid3 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid4 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid5 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid6 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end


