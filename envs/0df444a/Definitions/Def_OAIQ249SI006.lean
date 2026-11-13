-- Prove2me | Definitions.Def_OAIQ249SI006
-- name    : OAIQ249SI006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:46:33.766073+00:00
-- url     : https://prove2.me/theorems/17b5880c-96f2-4361-877a-a60d17f6bb41
-- title:
--   Definitions bundle OAIQ249SI006 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 27 definitions and 15 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialValue`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.centeredAtlasBasis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.centeredPhaseFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coefficientFrame`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coefficientFrameRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.curvedAtlasPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseCovectorRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoefficientField`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularManifoldBump`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDataFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDataFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familySectionNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.positiveTensorMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ptFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ptFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.shrinkingCircularWeight`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateAmplitude`, `OAI.ClosedSurfaceR4.JetVelocityCoordinates.toEuclidean`, `OAI.ClosedSurfaceR4.PhaseGeometry.circularFlatBump`, `OAI.ClosedSurfaceR4.RealModes.TangentPair`, `OAI.ClosedSurfaceR4.RealModes.firstJetPair`, `OAI.ClosedSurfaceR4.SmallModes.Scalar`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_OscillatoryModel`, `Immersion_ClosedSurface_ProjectionBounds`, `Immersion_ClosedSurface_ProjectionStability`, `SurfaceImmersion_Atlas_AtlasFiniteCancellation`, `SurfaceImmersion_Atlas_AtlasLinearMapBounds`, `SurfaceImmersion_Atlas_CoordinateQuadraticExpansion`, `SurfaceImmersion_Atlas_PhaseCovectorFamily`, `SurfaceImmersion_Correction_AdaptiveCorrectionStep`, `SurfaceImmersion_Correction_AtlasPolynomialMetric`, `SurfaceImmersion_Correction_CircularSmoothingAtlas`, `SurfaceImmersion_Correction_SmoothPrimitiveFamily`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_TensorOperatorSmooth`, `SurfaceImmersion_Geometry_InputSize`, `SurfaceImmersion_Geometry_PositiveTensorMetric`, `SurfaceImmersion_Geometry_TensorFrameAlgebra`, `SurfaceImmersion_Primitive_AtlasPrimitiveOperator`, `SurfaceImmersion_Primitive_CenteredAtlasPrimitives`, `SurfaceImmersion_Primitive_CircularFlatBump`, `SurfaceImmersion_Primitive_CurvedAtlasPrimitives`, `SurfaceImmersion_Primitive_JetVelocityCoordinates`, `SurfaceImmersion_Primitive_PrimitiveCoefficientCoordinates`, `SurfaceImmersion_Primitive_PrimitiveCoordinateData`, `SurfaceImmersion_Primitive_ShrinkingCircularWeight`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundle `OAIQ249SI013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI010` and `OAIQ249SI011`; the statements `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_supported_patch_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation_in_atlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing_pos_of_coordinate_crossings`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_directionIn_first_ne_of_covectors`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.reverse_crossing_in_chart`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_prepared_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_representation_on_support`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_phase_exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_cross_phase_exterior_control`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_exterior_crossing_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_cubic_remainder_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.metric_firstJet_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_gram_at_source`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_source_embedded_path_regular`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_crosscap_connecting_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_surface_pair_clean_relative`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_circular_direction_first`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_simple_prepared_crosscap_ordered_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_interior_double_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_surface_quadratic_crosscap_chart`, `OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases`, `OAI_ClosedSurfaceR4_PhaseGeometry_inverse_normal_nonlinear_chart_bound`, `OAI_ClosedSurfaceR4_RealModes_contDiffOn_displacement`, `OAI_ClosedSurfaceR4_RealModes_contDiffOn_realLinearizedTensor`, `OAI_ClosedSurfaceR4_RealModes_inverse_normal_phase_bound`, `OAI_ClosedSurfaceR4_RealModes_polynomial_nonlinear_phase_frame_bound` and `OAI_ClosedSurfaceR4_phaseTransition_refl_covector`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_supported_patch_geometry`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_directionIn_first_ne_of_covectors`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_phase_exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_small_metric_prepared_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_remainder_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_diagonal_mem_closure`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finite_surface_pair_clean_relative`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_circular_direction_first`, `OAI_ClosedSurfaceR4_PhaseGeometry_inverse_normal_nonlinear_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_inverse_chart_bound`, `OAI_ClosedSurfaceR4_RealModes_contDiffOn_displacement`, `OAI_ClosedSurfaceR4_RealModes_contDiffOn_realLinearizedTensor`, `OAI_ClosedSurfaceR4_RealModes_inverse_normal_phase_bound`, `OAI_ClosedSurfaceR4_RealModes_polynomial_nonlinear_phase_frame_bound`, `OAI_ClosedSurfaceR4_RealModes_realTwoJet_coordinate_prefix_bound` and `OAI_ClosedSurfaceR4_phaseTransition_refl_covector`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI013

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

abbrev Scalar := Base → ℂ

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes Set Metric

abbrev TangentPair := RVec 4 × RVec 4

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set

def firstJetPair (F : RField 4) (p : Base) : TangentPair :=
  (coordDeriv dx F p,coordDeriv dy F p)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encode global tensor sections by their finite atlas coordinates. This
retains the compact-surface partition identity while permitting the finite
mean iteration to run on a normed vector-valued function space. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.sectionTensorNormed
local instance sectionTensorSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorEncode_sub (u v : ∀ x : M, CovariantTwoTensor x) :
    A.tensorEncode (u - v) = A.tensorEncode u - A.tensorEncode v := by
  funext x i
  change A.bundleLocalize A.tensorTriv i (u - v) x =
    A.bundleLocalize A.tensorTriv i u x - A.bundleLocalize A.tensorTriv i v x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [bundleLocalize, localize, indicator_of_mem hx, bundleComponent,
      Pi.sub_apply, map_sub, smul_sub]
  · simp only [bundleLocalize, localize, indicator_of_notMem hx, sub_self]

variable [CompactSpace M]

lemma tensorEncode_smooth {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x))) : ContDiff ℝ ∞ (A.tensorEncode u) := by
  apply contDiff_pi.mpr
  intro i
  exact A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu

lemma tensorEncode_bound {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C) (hb : A.TensorWeightedBound s m C u) :
    _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (A.tensorEncode u) :=
  WeightedBound.pi uniqueDiffOn_univ hs hC
    (contDiffOn_pi.mp (A.tensorEncode_smooth hu).contDiffOn) hb

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateQuadraticExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the polynomial quadratic expansion into the same coordinates
and phase labels as the metric quadratic expansion. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ModulatedJets

abbrev coordinateAmplitude (H : Base → Fin 4 → ℂ) : SmallModes.Field 4 := H ∘ planeCoordinateIsometry.symm

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_ra72872_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_ra72872_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_ra72872_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_ra72872_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) : ContDiff ℝ ∞ (A.jetChartMap i F) :=
  spaceCoordinates.contDiff.comp (A.vectorChartRead_smooth i hF)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasLinearMapBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed linear coordinate changes preserve the actual atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V W : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_add {F G : M → V}
    (hF : ContMDiff planeModel 𝓘(ℝ,V) ∞ F) (hG : ContMDiff planeModel 𝓘(ℝ,V) ∞ G)
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbF : A.WeightedBound s m C F) (hbG : A.WeightedBound s m D G) :
    A.WeightedBound s m (C+D) (F+G) := by
  intro i
  have he : localize (i : M) (A.weight i) (F+G) =
      localize (i : M) (A.weight i) F + localize (i : M) (A.weight i) G := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx,smul_add]
  change WeightedEstimates.WeightedBound univ s m (C+D) (localize (i : M) (A.weight i) (F+G))
  rw [he]
  exact (hbF i).add uniqueDiffOn_univ hs
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hG).contDiffOn (hbG i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Euclidean coordinates for the geometric velocity and the actual ordered
jets used in the finite periodic expansion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetVelocityCoordinates
open RealModes JetPolynomial

def toEuclidean : RVec 4 ≃L[ℝ] Euclidean := spaceCoordinates.symm

end ClosedSurfaceR4.JetVelocityCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual globally restored polynomial perturbation of the metric,
with its exact first, second and higher-order variation decomposition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialMetricFiberNormed_ra72872_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialMetricFiberSpace_ra72872_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance polynomialMetricFiberNormed_ra72872_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialMetricFiberSpace_ra72872_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialMetricDualSmul_ra72872_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

local instance polynomialMetricSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def atlasPolynomialValue (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinatePolynomialValue (P i) ε (A.jetChartMap i G) 0)

def atlasPolynomialMetric (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  inducedTensor G+A.atlasPolynomialValue P ε G

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CurvedAtlasPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive primitive amplitudes for point-dependent phase bases.
The basis can be the actual nonlinear gradient basis constructed in
`SpatialPhaseBasis`; no constant-phase restriction enters the algebra. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance curvedPrimitiveFiberNormed_ra72872_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance curvedPrimitiveFiberSpace_ra72872_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance curvedPrimitiveDualAdd_ra72872_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveDualSmul_ra72872_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (P : A.centers → JetPolynomial.Base → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

local instance curvedPrimitiveSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance curvedPrimitiveSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def curvedAtlasPhase (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (a : A.centers × Fin 3) : M → ℝ :=
  restore (a.1 : M) (A.outer a.1) (phi a.1 a.2 ∘ JetPolynomial.planeCoordinateIsometry)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fiberwise correction operator for independently perturbed
primitive cutoffs. Its reference value is the identity, and its inverse
solves the finite rank-one equation on the original tensor bundle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_ra72872_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_ra72872_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionNormed
local instance atlasOperatorSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance atlasOperatorSectionGroup_ra72872_1 (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (atlasOperatorSectionNormed p).toAddCommGroup
def primitiveCoefficientField (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (a : A.centers × Fin 3) (p : M) : TensorFiber →L[ℝ] ℝ :=
  ((P a.1 (chart (a.1 : M) p)).Q a.2).comp
    (fiberToThree.comp (show TensorFiber →L[ℝ] TensorFiber from
      (A.tensorTriv a.1).continuousLinearMapAt ℝ p))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorOperatorSmooth
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the actual finite primitive operator, derived from its
supported coefficients and the smooth phase differentials. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance operatorSmoothFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorSmoothFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

local instance operatorSmoothFiberComplete_ra72872_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance operatorSmoothFiberComplete_ra72872_2 : CompleteSpace TensorFiber := inferInstance
local instance operatorSmoothDualAdd_ra72872_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul
variable (A : SmoothingAtlas M)

local instance operatorSmoothSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorSmoothSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
include A in
/-- The square of a smooth scalar differential is a smooth covariant tensor. -/
lemma phaseDifferentialSquare_smooth (phi : M → ℝ)
    (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (phaseDifferentialSquare phi p)) := by
  let v : Space := EuclideanSpace.single 0 1
  let e : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have he : ContMDiff 𝓘(ℝ) spaceModel ∞ e := e.contDiff.contMDiff
  have hF := he.comp hphi
  have hEq : inducedTensor (e ∘ phi) =
      fun p => phaseDifferentialSquare phi p := by
    funext p
    ext a b
    change inner ℝ (mfderiv planeModel spaceModel (e ∘ phi) p a)
      (mfderiv planeModel spaceModel (e ∘ phi) p b) = _
    rw [mfderiv_comp p (he.mdifferentiable (by simp)).mdifferentiableAt
      (hphi.mdifferentiable (by simp)).mdifferentiableAt,
      mfderiv_eq_fderiv,e.fderiv]
    change inner ℝ ((show ℝ from mfderiv planeModel 𝓘(ℝ) phi p a) • v)
      ((show ℝ from mfderiv planeModel 𝓘(ℝ) phi p b) • v) =
        (show ℝ from mfderiv planeModel 𝓘(ℝ) phi p a) *
          (show ℝ from mfderiv planeModel 𝓘(ℝ) phi p b)
    have hv : inner ℝ v v = 1 := by
      simp [v]
    have hinner (s t : ℝ) : inner ℝ (s • v) (t • v) = s*t := by
      rw [real_inner_smul_left,real_inner_smul_right,hv,mul_one]
    exact hinner _ _
  simpa only [hEq] using A.inducedTensor_smooth hF

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorFrameAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate conjugation of the actual primitive operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraFiberSpace
local instance frameAlgebraDualSmul_ra72872_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameAlgebraFiberNormed
local instance frameAlgebraSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameAlgebraSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def coefficientFrame (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) (p : M) : TensorFiber →L[ℝ] ℝ :=
  (B.primitiveCoefficientField P a p).comp ((B.tensorTriv i).symmL ℝ p)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoefficientCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-derivative bounds for coefficient functionals in each overlapping
primitive chart, fixed before choosing any independent phases or radii. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance coefficientReadFiberNormed_ra72872_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance coefficientReadFiberSpace_ra72872_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance coefficientReadDualNormed_ra72872_1 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDualSpace_ra72872_1 : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeNormed_ra72872_1 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_ra72872_1 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_ra72872_1 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualAdd_ra72872_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coefficientReadDualSmul_ra72872_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance coefficientReadSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coefficientReadSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def coefficientFrameRead (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) (y : JetPolynomial.Base) : TensorFiber →L[ℝ] ℝ :=
  B.coefficientFrame P i a ((chart (i : M)).symm y)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CenteredAtlasPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite primitive data from the centered convex phases. The
coefficient maps are the actual inverses of their three gradient squares. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance centeredPrimitiveFiberNormed_ra72872_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance centeredPrimitiveFiberSpace_ra72872_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance centeredPrimitiveDualAdd_ra72872_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance centeredPrimitiveDualSmul_ra72872_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance centeredPrimitiveSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance centeredPrimitiveSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def centeredPhaseFamily (ell : A.centers → Fin 3 → SmallModes.Base)
    (L : A.centers → ℝ) (i : A.centers) (j : Fin 3) : SmallModes.Base → ℝ :=
  centeredConvexPhase (ell i j) (L i) (coordinateChart (i : M) (i : M))

def centeredAtlasBasis (P : A.centers → PhaseBasis)
    (ell : A.centers → Fin 3 → SmallModes.Base) (L : A.centers → ℝ)
    (i : A.centers) (y : JetPolynomial.Base) : PhaseBasis :=
  centeredSpatialBasis (P i) (ell i) (L i) (coordinateChart (i : M) (i : M))
    (JetPolynomial.planeCoordinateIsometry y)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCovectorFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact parameter bounds for the actual circular phase differentials,
including their first spatial derivatives. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def phaseCovectorRead (i : B.centers) (phi : M → ℝ) (y : JetPolynomial.Base) : Plane →L[ℝ] ℝ :=
  (fderiv ℝ (phi ∘ (chart (i : M)).symm) y).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InputSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joint input norms for the adaptive correction iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberSpace
local instance inputSizeSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputSizeSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma inputBound_mono_const {t C D : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p} (hb : A.InputBound t m C G H)
    (hCD : C ≤ D) : A.InputBound t m D G H := by
  constructor
  · intro i j hj x
    exact (hb.1 i j hj x).trans hCD
  · intro i
    exact (hb.2 i).mono_const hCD

omit [CompactSpace M] in
lemma inputSize_nonneg {t : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hex : ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H) :
    0 ≤ A.inputSize t m G H := by
  apply le_csInf hex
  intro C hC
  exact hC.1

omit [CompactSpace M] in
lemma inputSize_bound {t : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hex : ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H) :
    A.InputBound t m (A.inputSize t m G H) G H := by
  constructor
  · intro i j hj x
    exact le_csInf hex (fun C hC => hC.2.1 i j hj x)
  · intro i j hj x hx
    exact le_csInf hex (fun C hC => hC.2.2 i j hj x hx)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveCorrectionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single adaptive transition, with all admissibility conditions preserved. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.adaptiveFiberNormed
local instance adaptiveFiberSpace_ra72872_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance adaptiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFlatBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat cutoffs for the actual circular disks in primitive preparation.
Their centers and radii are smooth parameters. -/
noncomputable section
open Set Function Filter
open scoped Topology
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def circularFlatBump (c : Base) (r : ℝ) (p : Base) : ℝ :=
  expNegInvGlue (r^2 - circularRadiusSquared c p)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CircularSmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smoothing atlas whose positive loci are actual coordinate disks.
The cutoffs are flat circular functions, not arbitrary subordinate bumps. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def circularManifoldBump (p : M) (r : ℝ) : M → ℝ :=
  (coordinateChart p).source.indicator
    (fun x => circularFlatBump (coordinateChart p p) r (coordinateChart p x))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveTensorMetric
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the two-dimensional tangent model, a smooth positive symmetric
bilinear tensor is an actual smooth Riemannian metric. -/
noncomputable section
open Set Metric Manifold Bundle Bornology
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma positive_bilinear_unitBall_bounded (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hB : ∀ v : Plane, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : Plane | B v v < 1} := by
  have hcpt : IsCompact (sphere (0 : Plane) 1) := isCompact_sphere _ _
  have hf : Continuous (fun v : Plane => B v v) := by fun_prop
  have hp : ∀ v ∈ sphere (0 : Plane) 1, 0 < B v v := by
    intro v hv
    apply hB
    intro hz
    rw [hz] at hv
    norm_num [mem_sphere] at hv
  obtain ⟨c,hc,hbound⟩ := hcpt.exists_forall_le' hf.continuousOn hp
  have hlower (v : Plane) : c*‖v‖^2 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hh := hbound (‖v‖⁻¹ • v) (by simpa only [mem_sphere,dist_zero_right] using hu)
    have he : B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v)*‖v‖^2 = B v v := by
      simp only [map_smul,smul_apply,smul_eq_mul]
      field_simp
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq he
  apply (NormedSpace.isVonNBounded_ball ℝ Plane (2+c⁻¹)).subset
  intro v hv
  rw [mem_ball,dist_zero_right]
  have hcv : c*‖v‖^2 < 1 := (hlower v).trans_lt hv
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  by_cases hn : ‖v‖ ≤ 1
  · linarith
  · have hn1 : 1 < ‖v‖ := lt_of_not_ge hn
    have hsq : ‖v‖ ≤ ‖v‖^2 := by nlinarith
    have hcn : c*‖v‖ < 1 := (mul_le_mul_of_nonneg_left hsq hc.le).trans_lt hcv
    have hnorm : ‖v‖ < c⁻¹ := by
      rw [← one_div]
      exact (lt_div_iff₀ hc).mpr (by simpa [mul_comm] using hcn)
    linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance ptFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance ptFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance ptDualAdd_ra72872_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance ptDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

local instance ptSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance ptSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def positiveTensorMetric (T : ∀ p : M, CovariantTwoTensor p)
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hsymm : ∀ p v w, T p v w = T p w v)
    (hpos : ∀ p v, v ≠ 0 → 0 < T p v v) : SmoothMetric M where
  inner := T
  symm := hsymm
  pos := hpos
  isVonNBounded p := positive_bilinear_unitBall_bounded (T p) (hpos p)
  contMDiff := hT

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPrimitiveFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite smooth primitive families and their partial-cycle metrics.
Different cycles may use different supports and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance familyFiberNormed_ra72872_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance familyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyDualAdd
local instance familyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance familySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed active-chart coordinate data represent the genuine inverse and
amplitude, while vanishing cutoff terms eliminate the other charts. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordinateDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordinateDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance coordinateDataDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
local instance coordinateDataDualSmul_ra72872_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance coordinateDataSectionNormed_ra72872_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordinateDataSectionSpace_ra72872_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def primitiveCoordinateData
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers)
    (S : Set (B.centers × Fin 3)) (y : JetPolynomial.Base) :
    PrimitiveAmplitudeData (B.centers × Fin 3) := by
  classical
  exact (((fun a => if a ∈ S then B.coefficientFrameRead P i a y else 0,
    fun a => psi a ((chart (i : M)).symm y)),
    fun a => if a ∈ S then B.phaseCovectorRead i (phi a) y else 0),
    (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm y)
      (u ((chart (i : M)).symm y)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ShrinkingCircularWeight
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-preserving independent disk shrinkage. The quotient is only
used where the original bump is positive; the smaller compact support
makes the resulting weight globally smooth. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

/-- The original weight is recovered at the original radius, even though
both circular bumps vanish on and outside its boundary. -/
def shrinkingCircularWeight (p : M) (w : M → ℝ) (r0 r : ℝ) (x : M) : ℝ :=
  w x * (circularManifoldBump p r x / circularManifoldBump p r0 x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


