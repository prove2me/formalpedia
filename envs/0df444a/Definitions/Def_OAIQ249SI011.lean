-- Prove2me | Definitions.Def_OAIQ249SI011
-- name    : OAIQ249SI011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:53:07.582327+00:00
-- url     : https://prove2.me/theorems/3b03cda1-332f-4ec1-b88e-e8ce787eece2
-- title:
--   Definitions bundle OAIQ249SI011 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 88 declarations of OpenAI's Lean: 65 definitions, 2 inductive types or structures, 3 instances and 18 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularCovectorJoint`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_tensorRestoreTransition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalPolynomialQuadraticMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalPolynomialQuadraticTarget`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalPolynomialQuadraticTargetRestricted`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalQuadraticTarget`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.globalQuadraticTargetRestricted`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.immersionMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.instDecidableEqSigmaSubtypeMemFinsetCentersProdIndexFinOfNatNat`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseMetricRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseNormalLift`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomialMeanTarget`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomialModeMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.realChartMap`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.shortPathMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.shortRemainderMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorMeanOperator`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorMeanTrial`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneEncode`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorProject`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorRestoreTransition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.curve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.innerCrossings`, `OAI.ClosedSurfaceR4.GeometryPreservation.collarInvariant`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.combinedQuadraticCoefficient`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.combinedQuadraticMean`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateMetricMap`, `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis.margin`, `OAI.ClosedSurfaceR4.PhaseGeometry.positivePhaseParameters`, `OAI.ClosedSurfaceR4.PhaseGrid.box`, `OAI.ClosedSurfaceR4.PhaseGrid.color`, `OAI.ClosedSurfaceR4.PhaseGrid.phaseLabel`, `OAI.ClosedSurfaceR4.PhaseGrid.quantize`, `OAI.ClosedSurfaceR4.PhasePatch`, `OAI.ClosedSurfaceR4.PhasePatch.phaseBasis`, `OAI.ClosedSurfaceR4.PreferredNormal.inPhase` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_AtlasLabels`, `Immersion_ClosedSurface_GridCover`, `Immersion_ClosedSurface_PhaseGrid`, `Immersion_ClosedSurface_PhasePatches`, `Immersion_ClosedSurface_PhaseStock`, `Immersion_ClosedSurface_ProjectionBounds`, `Immersion_ClosedSurface_QuadraticSupport`, `Immersion_ClosedSurface_RealBounds`, `Indexing`, `Local_AmpleRelation`, `Local_OneJet`, `Local_Relation`, `SurfaceImmersion_Atlas_AtlasQuadraticTargets`, `SurfaceImmersion_Atlas_AtlasTensorTransition`, `SurfaceImmersion_Atlas_BundleAtlasBounds`, `SurfaceImmersion_Atlas_BundleCutoffCoordinates`, `SurfaceImmersion_Atlas_CoordinateTaylorIdentity`, `SurfaceImmersion_Atlas_CrossAtlasTensorTransition`, `SurfaceImmersion_Atlas_GridAtlasMetric`, `SurfaceImmersion_Atlas_PhaseBasisPerturbation`, `SurfaceImmersion_Atlas_PhaseCovectorFamily`, `SurfaceImmersion_Atlas_PhaseMetricRead`, `SurfaceImmersion_Atlas_PhaseNormalLift`, `SurfaceImmersion_Atlas_PreferredNormalPhasePullback`, `SurfaceImmersion_Atlas_SurfacePhaseCharts`, `SurfaceImmersion_Atlas_TensorPlaneCoordinates`, `SurfaceImmersion_Atlas_WeightedInverseJacobian`, `SurfaceImmersion_Correction_AtlasCombinedModes`, `SurfaceImmersion_Correction_AtlasPolynomialModeMean`, `SurfaceImmersion_Correction_AtlasPolynomialOverlap`, `SurfaceImmersion_Correction_AtlasPrimitiveMean`, `SurfaceImmersion_Correction_BoundedSurfaceCorrection`, `SurfaceImmersion_Correction_BundleSmoothingIdentity`, `SurfaceImmersion_Correction_BundleSmoothingLinearity`, `SurfaceImmersion_Correction_BundleSmoothingTransition`, `SurfaceImmersion_Correction_GoodSmoothingAtlas`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_TensorMeanIteration`, `SurfaceImmersion_Correction_UniformRealModeCoefficients`, `SurfaceImmersion_Geometry_CombinedQuadraticExpansion`, `SurfaceImmersion_Geometry_CompactNormalTriple`, `SurfaceImmersion_Geometry_PositiveTensorMetric`, `SurfaceImmersion_Geometry_QuadraticOverlapSupports`, `SurfaceImmersion_Geometry_ShortMetricPath`, `SurfaceImmersion_Geometry_TensorDecodedBounds`, `SurfaceImmersion_Geometry_TensorPlaneReconstruction`, `SurfaceImmersion_Primitive_AtlasBoundaryProfile`, `SurfaceImmersion_Primitive_AtlasPrimitiveOperator`, `SurfaceImmersion_Primitive_FrozenCircularData`, `SurfaceImmersion_Primitive_LeadingProfileMap`, `SurfaceImmersion_Primitive_PrimitivePatchCurves`, `SurfaceImmersion_Primitive_SupportedPrimitivePatch`, `SurfaceImmersion_Primitive_SurfaceCircularThreshold`, `SurfaceImmersion_Primitive_VelocityNormalBounds`, `SurfaceImmersion_Whitney_ActualProfileCollar`, `SurfaceImmersion_Whitney_SurfaceBoundaryCollar`, `ToMathlib_Algebra_Ring_Periodic`, `ToMathlib_Analysis_Convex_Basic`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI000`, `OAIQ249SI006`, `OAIQ249SI007` and `OAIQ249SI009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI012`, `OAIQ249SI014` and `OAIQ249SI016`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_profiled_phase_primitive_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.circular_operator_metric_stability`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_linearized_residual_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_quadratic_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_global_polynomial_quadratic_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_metric_plane_read_bounds`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_primitive_boundary_crossing`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_atlas_seed_profile`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_spherical_immersion`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_frame`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_local_metric_defect`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_local_correction_assembly`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_small_scaled_metric`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_vectorPlaneRestore_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_circular_definers`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_current_second`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_old_boundary_crossing`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_metric_good_smoothingAtlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finiteSmooth_approximation`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_free_family`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_profiled_phase_primitive_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_finite_slow_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation_in_atlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.crossing_pos_of_coordinate_crossings`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.reverse_crossing_in_chart`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.second_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_nearby_cancellation_all_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_target_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_catalog_global_quadratic_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_circularPhase_frame_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude_smooth_of_data`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_transfer`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_geometric_metric_with_property_in_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exterior_projected_normal_close_closure`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_cubic_remainder_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_grid_free_quadratic_correction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_gram_at_source`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_frame`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_real_restored_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_local_metric_defect`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_convex_circular_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_scaled_path_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SupportedPrimitivePatch_circular_definers`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_metric_good_smoothingAtlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_finiteSmooth_approximation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_fixed_chart_nonlinear_solver`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_supported_linear_mean_data`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles`, `OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.uniform_polynomial_solvers_all_profiles`, `OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases`, `OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets`, `OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput`, `OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_supported_curve_crossing_loop` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI000
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007
import Definitions.Def_OAIQ249SI009

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseGrid
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set

def color (q : ℕ) (a : Index) : (ZMod q) × (ZMod q) :=
  ((a.1 : ZMod q), (a.2 : ZMod q))

def quantize (h : ℝ) (x : Base) : Index :=
  (⌊x.1/h⌋,⌊x.2/h⌋)

def box (N : ℕ) : Finset Index :=
  (Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

def complexifyLI (n : ℕ) : RVec n →ₗᵢ[ℝ] Ambient n where
  toLinearMap := (complexifyCLM n).toLinearMap
  norm_map' := norm_complexify

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhasePatches
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



structure PhasePatch (F : M → Space) (H : Base → PhaseMean.Tensor) (p : M) where
  G : RField 4
  ξ : Fin 3 → Base
  Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ
  O : Set Base
  V : Set M
  smooth : ContDiff ℝ ∞ G
  compact : HasCompactSupport G
  openO : IsOpen O
  centerO : coordinateCenter p ∈ O
  subdomain : O ⊆ coordinateDomain p
  agrees : EqOn G (coordinateMap F p) O
  openV : IsOpen V
  centerV : p ∈ V
  sourceV : V ⊆ (chartAt Plane p).source
  mapsV : ∀ q ∈ V, planeCoordinates (chartAt Plane p q) ∈ O
  decomposition : ∀ A, ∑ i, Q i A • covectorSquare (ξ i) = A
  admissible : ∀ x ∈ O, Function.Injective (fderiv ℝ (coordinateMap F p) x) ∧
    (∀ i, 0 < Q i (H x)) ∧ (∀ i, Good (realSecondTensor (coordinateMap F p) x) (ξ i)) ∧
    (∀ i j, i ≠ j → Good (realSecondTensor (coordinateMap F p) x) (ξ i + ξ j) ∧
      Good (realSecondTensor (coordinateMap F p) x) (ξ i - ξ j))



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseStock
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set



def PhaseBasis.margin {n : ℕ} (P : PhaseBasis) (z : PhaseInput n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 =>
    min (P.Q i z.2) ‖secondQuadratic z.1 (-(P.ξ i).2, (P.ξ i).1)‖)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridCover
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set
attribute [local instance] Classical.propDecidable

def phaseLabel (a : Index × Fin 3) : Fin (Fintype.card Label) :=
  Fintype.equivFin Label (color 6 a.1, a.2)

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasLabels
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]

def atlasPhaseLabel (a : ι × (Index × Fin 3)) : Fin (Fintype.card (AtlasPhaseLabel (ι := ι))) :=
  Fintype.equivFin (AtlasPhaseLabel (ι := ι)) (a.1,phaseLabel a.2)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionBounds
attribute [-instance] _root_.instVAddIntReal_solutions
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

def normalColumns (p : TangentPair) : Fin 4 → RVec 4 :=
  fun i => realNormalPart p.1 p.2 (Pi.single i 1)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate displacement sumDisplacement)



def quadraticAmplitude {n : ℕ} {ι : Type*} (τ : ℝ) (φ : ι → Base → ℝ)
    (Z : ι → Field n) : QuadraticLabel ι → SmallModes.Tensor
  | .inl i => phaseDoubleTensor τ (φ i) (Z i)
  | .inr ⟨i, j, b⟩ => if b then phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)
    else phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)

def quadraticSupport {ι : Type*} (S : ι → Set Base) : QuadraticLabel ι → Set Base
  | .inl i => S i
  | .inr ⟨i, j, _⟩ => S i ∩ S j

lemma quadraticAmplitude_tsupport {n : ℕ} {ι : Type*} (τ : ℝ) (φ : ι → Base → ℝ)
    (Z : ι → Field n) {S : ι → Set Base} (hZ : ∀ i, tsupport (Z i) ⊆ S i) :
    ∀ l : QuadraticLabel ι, tsupport (quadraticAmplitude τ φ Z l) ⊆ quadraticSupport S l := by
  intro l
  rcases l with i | ⟨i, j, b⟩
  · change tsupport (phasePlusTensor τ (φ i) (φ i) (Z i) (Z i)) ⊆ S i
    exact (phasePlusTensor_tsupport τ (φ i) (φ i) (Z i) (Z i)).trans
      (fun _ hh => hZ i hh.1)
  · cases b
    · exact (phasePlusTensor_tsupport τ (φ i) (φ j) (Z i) (Z j)).trans
        (inter_subset_inter (hZ i) (hZ j))
    · exact (phaseMinusTensor_tsupport τ (φ i) (φ j) (Z i) (Z j)).trans
        (inter_subset_inter (hZ i) (hZ j))

lemma quadraticAmplitude_smooth {n : ℕ} {ι : Type*} {φ : ι → Base → ℝ}
    {Z : ι → Field n} (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hZ : ∀ i, ContDiff ℝ ∞ (Z i))
    (τ : ℝ) : ∀ l : QuadraticLabel ι, ContDiff ℝ ∞ (quadraticAmplitude τ φ Z l) := by
  intro l
  apply contDiffOn_univ.mp
  rcases l with i | ⟨i, j, b⟩
  · exact contDiffOn_phasePlusTensor isOpen_univ (hφ i).contDiffOn (hφ i).contDiffOn
      (hZ i).contDiffOn (hZ i).contDiffOn τ
  · cases b
    · exact contDiffOn_phasePlusTensor isOpen_univ (hφ i).contDiffOn (hφ j).contDiffOn
        (hZ i).contDiffOn (hZ j).contDiffOn τ
    · exact contDiffOn_phaseMinusTensor isOpen_univ (hφ i).contDiffOn (hφ j).contDiffOn
        (hZ i).contDiffOn (hZ j).contDiffOn τ

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Indexing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
/-!
# Indexing types

This file introduces `IndexType : ℕ → Type` such that `IndexType 0 = ℕ` and
`IndexType (N+1) = Fin (N+1)`. Each `IndexType N` has a total order and and inductive principle
together with supporting lemmas.
-/

section


open Fin Set

instance instLocallyFiniteOrderIndexType : ∀ n, LocallyFiniteOrder (IndexType n)
  | 0 => inferInstanceAs (LocallyFiniteOrder ℕ)
  | (N + 1) => inferInstanceAs (LocallyFiniteOrder (Fin (N + 1)))
end
end

section
-- module Solutions.OAIQ249_SI.Local_OneJet
attribute [-instance] _root_.instVAddIntReal_solutions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Spaces of 1-jets and their sections

For real normed spaces `E` and `F`, this file defines the space `OneJetSec E F` of 1-jets
of maps from `E` to `F` as `E × F × (E →L[ℝ] F)`.

A section `𝓕 : JetSet E F` of this space is a map `(𝓕.f, 𝓕.φ) : E → F × (E →L[ℝ] F)`.

It is holonomic at `x`, spelled `𝓕.IsHolonomicAt x` if the differential of `𝓕.f` at `x`
is `𝓕.φ x`.

We then introduced parametrized families of sections, and especially homotopies of sections,
with type `HtpyJetSec E F` and their concatenation operation `HtpyJetSec.comp`.


Implementation note: the time parameter `t` for homotopies is any real number, but all the
homotopies we will construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes
more smoothness constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed
for smooth concatenations anyway.
 -/

section


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology ContDiff


variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

/-! ## Spaces of 1-jets -/


instance instMetricSpaceOneJet : MetricSpace (OneJet E F) := inferInstanceAs (MetricSpace (E × F × (E →L[ℝ] F)))

/-! ## Homotopies of sections -/
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_Relation
attribute [-instance] _root_.instVAddIntReal_solutions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Local partial differential relations and their formal solutions

This file defines `RelLoc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : RelLoc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `FormalSol R`.
(FIXME(grunweg): `sol` is never mentioned; is this docstring outdated?)

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `HtpyJetSet E F` (homotopies of 1-jet sections).
-/

section


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {E F}

namespace RelLoc

variable {R : RelLoc E F}

/-- A formal solution (f, φ) is holonomic at `x` if the differential of `f` at `x` is `φ x`. -/
def FormalSol.IsHolonomicAt (𝓕 : FormalSol R) (x : E) : Prop :=
  D 𝓕.f x = 𝓕.φ x

open RelLoc

instance instFunLikeFamilyFormalSolJetSec (R : RelLoc E F) : FunLike (FamilyFormalSol P R) P (JetSec E F) :=
  ⟨fun S ↦ S.toFamilyJetSec, by
      intros S S' h
      ext p x : 3 <;> replace h := congrFun h p
      exacts [congrFun (JetSec.ext_iff.1 h).1 x, congrFun (JetSec.ext_iff.1 h).2 x]⟩

end RelLoc
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_AmpleRelation
attribute [-instance] _root_.instVAddIntReal_solutions
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Slices of first order relations

Recal that a first order partial differential relation for maps between real normed vector spaces
`E` and `F` is a set `R` in `OneJet E F := E × F × (E →L[ℝ] F)`. In this file we study slices
of such relations. The word slice is meant to convey the idea of intersecting with an affine
subspace. Here we fix `(x, y, φ) : OneJet E F` and some hyperplane `H` in `E`. The points
`x` and `y` are fixed and we will take a slice in `E →L[ℝ] F` by intersecting `R` with the affine
subspace of linear maps that coincide with `φ` on `H`.

It will be convenient for convex integration purposes to identify this slice with `F`. There is
no natural identification but we can build one by fixing more data that a hyperplane in `E`.
Namely we fix `p : DualPair E` (where `ker p.π` is the relevant hyperplane) and reformulate
"linear map that coincides with `φ` on `H`" as `p.update φ w` for some `w : F`.

This `slice` definition allows to define `RelLoc.isAmple`, the ampleness condition for first
order relations: a relation is ample if all its slices are ample sets.

At the end of the file we consider 1-jet sections and slices corresponding to points in their image.
-/

section


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

variable {R : RelLoc E F}

open Set

/-! ## Slices and ampleness -/


namespace RelLoc

/-- A relation is ample if all its slices are ample. -/
def IsAmple (R : RelLoc E F) : Prop :=
  ∀ (p : DualPair E) (θ : E × F × (E →L[ℝ] F)), AmpleSet (R.slice p θ)

open scoped Pointwise

end RelLoc

open RelLoc

/-! ## Slices for 1-jet sections and formal solutions. -/

namespace RelLoc.FormalSol

/-- The slice associated to a formal solution and a dual pair at some point. -/
def sliceAt (𝓕 : FormalSol R) (p : DualPair E) (x : E) : Set F :=
  R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- A formal solution `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def IsShortAt (𝓕 : FormalSol R) (p : DualPair E) (x : E) : Prop :=
  D 𝓕.f x p.v ∈ hull (connectedComponentIn (𝓕.sliceAt p x) <| 𝓕.φ x p.v)

end RelLoc.FormalSol
end
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothingIdentity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction and error identities for bundle smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

lemma bundleRestore_localize (i : A.centers) (u : ∀ x, E x) (x : M) :
    A.bundleRestore e i (A.bundleLocalize e i u) x = (A.weight i x) ^ 2 • u x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [bundleRestore, bundleLocalize, localize_chart _ _ _ hx, bundleComponent, map_smul,
      (e i).symmL_continuousLinearMapAt (hdomain i hx)]
    by_cases hz : A.weight i x = 0
    · simp [hz]
    · rw [A.outer_one i x (subset_tsupport _ hz), one_smul]
  · have ho : A.outer i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.outer_support i h))
    have hw : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [bundleRestore, ho, hw, zero_smul, zero_pow (by decide : 2 ≠ 0)]

lemma bundle_sum_restore_localize (u : ∀ x, E x) (x : M) :
    (∑ i : A.centers, A.bundleRestore e i (A.bundleLocalize e i u) x) = u x := by
  simp_rw [A.bundleRestore_localize e hdomain]
  rw [← Finset.sum_smul, A.partition x, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart transitions for the actual bundle smoother. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

omit [ContMDiffVectorBundle ∞ F E planeModel] in
lemma bundleLocalize_restore (i j : A.centers) (h : Base → F) :
    A.bundleLocalize e i (A.bundleRestore e j h) =
      fun x => A.pairWeight i j x • A.bundleTransition e i j x
        (h (transition (i : M) (j : M) x)) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · have hbi := hdomain i ((chart (i : M)).map_target hi)
      have hbj := hdomain j hj
      simp only [bundleLocalize, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, map_smul, pairWeight, bundleTransition]
      rw [(e i).continuousLinearMapAt_apply_of_mem ℝ hbi,
        (e j).symmL_apply (R := ℝ) hbj, ← (e j).coordChangeL_apply (R := ℝ) (e i) ⟨hbj, hbi⟩, smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [bundleLocalize, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, hz, zero_smul, map_zero, smul_zero, pairWeight]
  · simp only [bundleLocalize, localize, pairWeight, indicator_of_notMem hi, zero_smul]

variable [CompactSpace M]

/-- Fiber transitions preserve each weighted derivative norm without a scale loss. -/
theorem bundle_pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → F) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (A.bundleLocalize e i (A.bundleRestore e j h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_clm_composition_bound
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (A.bundleTransition_smooth e hdomain i j) (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.bundleLocalize_restore e hdomain]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_BundleAtlasBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted atlas bounds for section restoration. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

lemma bundleLocalize_sum {ι : Type*} (b : Finset ι) (i : A.centers) (u : ι → ∀ x, E x) :
    A.bundleLocalize e i (fun x => ∑ k ∈ b, u k x) =
      fun x => ∑ k ∈ b, A.bundleLocalize e i (u k) x := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target <;>
    simp [bundleLocalize, localize, bundleComponent, hx, Finset.smul_sum]

variable [ContMDiffVectorBundle ∞ F E planeModel] [CompactSpace M]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- A finite family of local sections can be restored with fixed weighted
bounds at every order. -/
theorem bundle_restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → F) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (h i)) →
      A.BundleWeightedBound e s m (D * C)
        (fun x => ∑ i : A.centers, A.bundleRestore e i (h i) x) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.bundle_pair_weighted_bound e hdomain i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (A.bundleLocalize e i (A.bundleRestore e j (h j))) :=
    A.bundleLocalize_smooth e hdomain i (A.bundleRestore_smooth e hdomain j (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => A.bundleLocalize e i (A.bundleRestore e j (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [A.bundleLocalize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_BundleCutoffCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading a section with an arbitrary compact chart cutoff is bounded by
its atlas norm. This allows phase patches to use unweighted tensor values. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)

include hdomain
omit [ContMDiffVectorBundle ∞ F E planeModel] in
lemma bundleCutoff_restore (i j : A.centers) (ψ : M → ℝ) (h : Base → F) :
    A.bundleCutoff e i ψ (A.bundleRestore e j h) =
      fun x => localize (i : M) ψ (A.outer j) x • A.bundleTransition e i j x
        (h (transition (i : M) (j : M) x)) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · have hbi := hdomain i ((chart (i : M)).map_target hi)
      have hbj := hdomain j hj
      simp only [bundleCutoff, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, map_smul, bundleTransition]
      rw [(e i).continuousLinearMapAt_apply_of_mem ℝ hbi,
        (e j).symmL_apply (R := ℝ) hbj,
        ← (e j).coordChangeL_apply (R := ℝ) (e i) ⟨hbj,hbi⟩, smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [bundleCutoff, bundleComponent, localize, indicator_of_mem hi,
        bundleRestore, hz, zero_smul, map_zero, smul_zero]
  · simp only [bundleCutoff, localize, indicator_of_notMem hi, zero_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearity of the concrete finite-atlas bundle smoother. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

lemma bundleLocalize_smul (i : A.centers) (a : ℝ) (u : ∀ x, E x) :
    A.bundleLocalize e i (a • u) = a • A.bundleLocalize e i u := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target <;>
    simp [bundleLocalize, localize, bundleComponent, hx, smul_smul, mul_comm]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance sectionTensorSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorDecode_encode (u : ∀ x : M, CovariantTwoTensor x) :
    A.tensorDecode (A.tensorEncode u) = u := by
  funext x
  exact A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain u x

lemma tensorEncode_smul (a : ℝ) (u : ∀ x : M, CovariantTwoTensor x) :
    A.tensorEncode (a • u) = a • A.tensorEncode u := by
  funext x i
  exact congrFun (A.bundleLocalize_smul A.tensorTriv i a u) x

def tensorProject (f : Base → A.centers → TensorFiber) : Base → A.centers → TensorFiber :=
  A.tensorEncode (A.tensorDecode f)

variable [CompactSpace M]

lemma tensorDecode_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (f : Base → A.centers → TensorFiber) (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      ContDiff ℝ ∞ f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C f →
      A.TensorWeightedBound s m (D * C) (A.tensorDecode f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  exact hd (fun i x => f x i) s C hs hs1 hC (fun i => contDiff_pi.mp hf i)
    (fun i => hb.component uniqueDiffOn_univ hs.le hC hf.contDiffOn i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_sub (i : A.centers) (u v : ∀ x : M, CovariantTwoTensor x) :
    A.tensorPlaneRead i (u - v) = A.tensorPlaneRead i u - A.tensorPlaneRead i v := by
  funext x
  change fiberToThree (localize (i : M) (A.outer i) (A.bundleComponent A.tensorTriv i (u-v))
    (planeCoordinateIsometry.symm x)) = _
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [tensorPlaneRead, tensorChartRead, Function.comp_apply, bundleCutoff, localize,
      indicator_of_mem hx, bundleComponent, Pi.sub_apply, map_sub, smul_sub]
  · simp only [tensorPlaneRead, tensorChartRead, Function.comp_apply, bundleCutoff, localize,
      indicator_of_notMem hx, map_zero, Pi.sub_apply, sub_self]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPlaneReconstruction
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction from the three independent tensor coordinates. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.reconstructionDualAdd
local instance reconstructionFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance reconstructionSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorPlaneEncode (u : ∀ x : M, CovariantTwoTensor x) (i : A.centers) : SmallModes.Base → Tensor :=
  fun y => fiberToThree (A.tensorEncode u (planeCoordinateIsometry.symm y) i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CombinedQuadraticExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full quadratic expansion: the metric and polynomial remainders
share one finite family of doubled and mixed nonzero phases. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def combinedQuadraticMean {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) :
    SmallModes.Base → PhaseMean.Tensor :=
  RealModes.zeroPhaseSum τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude (H i)) + coordinateQuadraticMean P ε G φ H τ t

def combinedQuadraticCoefficient {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    (l : RealModes.QuadraticLabel ι) : SmallModes.Tensor :=
  RealModes.quadraticAmplitude τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude (H i)) l + coordinateQuadraticCoefficient P ε G φ H τ t l

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTaylorIdentity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Taylor identity for the metric plus its finite polynomial
perturbation, in the coordinates of the forced-mode construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def coordinateMetricMap {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) : SmallModes.Base → PhaseMean.Tensor :=
  RealModes.realMetricTensor (G ∘ planeCoordinateIsometry.symm) + coordinatePolynomialValue P ε G 0

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasQuadraticTargets
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported quadratic targets for the global phase expansion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasQuadraticTargetsFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasQuadraticTargetsFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasQuadraticTargetsDualAdd_r8dee02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasQuadraticTargetsDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance atlasQuadraticTargetsSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasQuadraticTargetsSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def globalQuadraticTarget (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.chartWeightCompact k)) where
  toFun := fun x => (A.planeWeight k x)^2 • RealModes.quadraticAmplitude τ
    (fun a => A.vectorPlaneRead k (φ a)) (fun a => A.vectorPlaneRead k (Z a)) l x
  contDiff' := ((A.planeWeight_smooth k).pow 2).smul
    (RealModes.quadraticAmplitude_smooth (fun a => A.vectorPlaneRead_smooth k (hφ a))
      (fun a => A.vectorPlaneRead_smooth k (hZ a)) τ l)
  zero_on_compl' := by
    intro x hx
    have hw := (A.supportedPlaneWeight k).zero_on_compl hx
    change A.planeWeight k x = 0 at hw
    simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.zero_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual change of tensor coordinates for a restored atlas term.
Bundle restoration uses one outer cutoff, whereas chart reading uses the
square of its own cutoff. On the nonzero partition locus the latter is one. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.transitionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.transitionFiberSpace
local instance transitionDualSmul_r8dee02_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.transitionFiberNormed
local instance transitionSectionNormed_r8dee02_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance transitionSectionSpace_r8dee02_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The three-coordinate form of the genuine tensor-bundle transition,
including the single cutoff used by restoration. -/
def tensorRestoreTransition (i j : A.centers) (x : Base) : Tensor →L[ℝ] Tensor :=
  A.outer j ((chart (i : M)).symm x) •
    fiberToThree.comp ((A.bundleTransition A.tensorTriv i j x).comp fiberFromThree)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tensor transitions between independent smoothing atlases. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberSpace
local instance crossTransitionDualSmul_r8dee02_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberNormed
local instance crossTransitionSectionNormed_r8dee02_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace_r8dee02_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def cross_tensorRestoreTransition (i : A.centers) (j : B.centers) (x : Base) : Tensor →L[ℝ] Tensor :=
  B.outer j ((chart (i : M)).symm x) •
    fiberToThree.comp ((((B.tensorTriv j).coordChangeL ℝ (A.tensorTriv i)
      ((chart (i : M)).symm x)) : TensorFiber →L[ℝ] TensorFiber).comp fiberFromThree)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformRealModeCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reconstruction estimates on a fixed compact set of real two-jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

def complexifyJetLI : RealTwoJet →ₗᵢ[ℝ] TwoJet 4 where
  toLinearMap := complexifyJetCLM.toLinearMap
  norm_map' J := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg J)).mpr
      intro i
      exact (norm_complexify (J i)).trans_le (norm_le_pi_norm J i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (complexifyJetCLM J))).mpr
      intro i
      exact (norm_complexify (J i)).symm.trans_le (norm_le_pi_norm (complexifyJetCLM J) i)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridAtlasMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric expansion for the variable grid of phases in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry
open PhaseGrid (Index coverRegion supportedCellCutoff)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasFiberNormed
local instance gridAtlasSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridAtlasSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqSigmaSubtypeMemFinsetCentersProdIndexFinOfNatNat {a : A.centers → Finset Index} : DecidableEq (Σ i, ((a i) × Fin 3)) :=
  Classical.decEq _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBasisPerturbation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coefficient forms for nearby phase covectors. The inverse
operator constructs the new decomposition and preserves compact positive
cone margins. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def positivePhaseParameters (P : PhaseBasis) : Set ((Fin 3 → Base) × PhaseMean.Tensor) :=
  {z | (perturbedPhaseOperator P z.1).IsInvertible ∧
    (∀ i, z.1 i ≠ 0) ∧ ∀ i, 0 < perturbedPhaseCoefficient P z.1 i z.2}

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and compact positive lower bounds for the limiting normal component. -/
noncomputable section
open Set
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def leadingNormal (X Y C V : Vec) : Vec :=
  realNormalPart (leadingTangent X Y C V) Y C

def normalSize (X Y C V : Vec) : ℝ :=
  Real.sqrt (leadingNormal X Y C V ⬝ᵥ leadingNormal X Y C V)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactNormalTriple
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normal nondegeneracy from the three bounded derivatives of a
primitive ansatz. No bound on its rapidly oscillating xx derivative is used. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def normalTripleNeighborhood (c : ℝ) : Set NormalTriple :=
  {J | gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖tripleNormal J‖}

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FrozenCircularData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal data as smooth functions of position and angular value.
The first mixed normal coefficient contains no derivative of the angle. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frozenNormal (X Y C : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (z : E × ℝ) : Vec :=
  normalize (leadingNormal (X z.1) (Y z.1) (C z.1)
    (R z.1 • direction (e₁ z.1) (e₂ z.1) z.2))

def frozenSize (X Y C : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec)
    (z : E × ℝ) : ℝ :=
  normalSize (X z.1) (Y z.1) (C z.1) (R z.1 • direction (e₁ z.1) (e₂ z.1) z.2)

def frozenFirst (Q X Y C : E → Vec) (R : E → ℝ) (e₁ e₂ : E → Vec) (d : E)
    (z : E × ℝ) : ℝ := frozenError Q R e₁ e₂ d z ⬝ᵥ frozenNormal X Y C R e₁ e₂ z

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BoundedSurfaceCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite periodic correction to the actual geometric second-jet
family, including global smooth extension and its uniform scale bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def yData (J : LowJet) : Euclidean := ι (slot 2 J)
def cData (J : LowJet) : Euclidean := ι (slot 6 J)
def xData (J : LowJet) : Euclidean := ι (tangent J)

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileMap
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five leading profiles depend smoothly on the second jet, its first
transverse derivative, and the periodic parameter. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def leadingVelocity (z : LowJet × ℝ) : RealModes.RVec 4 := tangent z.1+l.velocity z

def leadingProfileMap (z : LeadingProfileInput) : EuclideanBoundaryProfile :=
  ![JetVelocityCoordinates.toEuclidean (l.leadingVelocity z.1),
    JetVelocityCoordinates.toEuclidean (slot 2 z.1.1),
    JetVelocityCoordinates.toEuclidean (slot 6 z.1.1),
    JetVelocityCoordinates.toEuclidean (fderiv ℝ l.leadingVelocity z.1 (z.2,0)),
    JetVelocityCoordinates.toEuclidean (fderiv ℝ l.velocity z.1 (0,1))]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfacePhaseCharts
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual surface chart associated with a nonlinear phase. It is
independent of the correction atlas and supplies the chart transitions for later curves. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfacePhaseMap (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space) :
    SmallModes.Base → NormalFrame.Vec := spaceCoordinates ∘ F ∘ (surfacePhaseChart q e).symm

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticOverlapSupports
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance overlapTargetsFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance overlapTargetsFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance overlapTargetsDualAdd_r8dee02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance overlapTargetsDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance overlapTargetsSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance overlapTargetsSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
lemma globalQuadraticTarget_overlap (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    tsupport (A.globalQuadraticTarget τ φ Z hφ hZ k l) ⊆
      (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) := by
  intro x hx
  let Q := RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
    (fun a => A.vectorPlaneRead k (Z a)) l
  have hw : x ∈ tsupport (fun y => (A.planeWeight k y)^2) :=
    tsupport_smul_subset_left (fun y => (A.planeWeight k y)^2) Q hx
  have hw' : x ∈ tsupport (A.planeWeight k) := by
    have hs : tsupport (fun y => (A.planeWeight k y)^2) ⊆ tsupport (A.planeWeight k) := by
      simpa only [pow_two] using (tsupport_mul_subset_left (f := A.planeWeight k) (g := A.planeWeight k))
    exact hs hw
  have hkx : x ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) :=
    (A.supportedPlaneWeight k).tsupport_subset hw'
  have hq : x ∈ tsupport Q := tsupport_smul_subset_right (fun y => (A.planeWeight k y)^2) Q hx
  have hqq := RealModes.quadraticAmplitude_tsupport τ (fun a => A.vectorPlaneRead k (φ a))
    (fun a => A.vectorPlaneRead k (Z a)) (fun _ => Subset.rfl) l hq
  have hpx : (chart (k : M)).symm (planeCoordinateIsometry.symm x) ∈ globalQuadraticSupport S l := by
    rcases l with a | ⟨a,b,c⟩
    · exact hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq)
    · exact ⟨hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq.1),
        hSZ b (A.vectorPlaneRead_support_on_weight k (Z b) hkx hqq.2)⟩
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hkx
  have hpS : p ∈ globalQuadraticSupport S l := by
    simpa only [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv (A.weight_support k hp)] using hpx
  exact ⟨chart (k : M) p,⟨p,⟨hp,hpS⟩,rfl⟩,rfl⟩

def globalQuadraticTargetRestricted (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.quadraticOverlapCompact S hS k l)) :=
  ContDiffMapSupportedIn.of_support_subset (A.globalQuadraticTarget τ φ Z hφ hZ k l).contDiff
    (subset_closure.trans (A.globalQuadraticTarget_overlap τ φ Z hφ hZ S hS hSZ k l))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanIteration
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean substitution on actual global tensor sections, represented
by redundant atlas coordinates. Every iterate stays in the representation
range, so no leading-identity premise on arbitrary plane fields is needed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationModelNormed
local instance iterationModelSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance iterationDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance iterationSectionTensorNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance iterationSectionTensorSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorMeanOperator
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x)
    (f : Base → A.centers → TensorFiber) : Base → A.centers → TensorFiber :=
  A.tensorEncode (T (A.tensorDecode f))

def tensorMeanTrial (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    ∀ x : M, CovariantTwoTensor x :=
  A.tensorDecode (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorDecodedBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform chart-reading estimates for the redundant coordinates used by
finite mean substitution, including the radius of every local trial ball. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.decodedFiberSpace
local instance decodedDualAdd_r8dee02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.decodedDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.decodedFiberNormed
local instance decodedSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance decodedSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorPlaneRead_decode_sub (i : A.centers) (f g : Base → A.centers → TensorFiber) :
    A.tensorPlaneRead i (A.tensorDecode (f-g)) =
      A.tensorPlaneRead i (A.tensorDecode f) - A.tensorPlaneRead i (A.tensorDecode g) := by
  rw [A.tensorDecode_sub, A.tensorPlaneRead_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance atlasOperatorFiberComplete_r8dee02_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_r8dee02_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionNormed
local instance atlasOperatorSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionGroup
def primitiveFullOperator (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (p : M) : CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p :=
  completedPrimitiveOperator (fun a => A.primitiveCoefficientField P a p)
    (fun a => psi a p) (fun a => A.primitivePhaseCovector phi a p)

/-- The corrected tensor is obtained by actual pointwise inverse. -/
def correctedPrimitiveTensor (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) (p : M) : CovariantTwoTensor p :=
  (A.primitiveFullOperator P psi phi p).inverse (u p)

def correctedPrimitiveAmplitude (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) (a : A.centers × Fin 3) (p : M) : ℝ :=
  psi a p * Real.sqrt (A.primitiveCoefficientField P a p
    (A.correctedPrimitiveTensor P psi phi u p))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceCircularThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Freeze the circular coefficient bounds on the original surface before
choosing its supported angle and its smaller jet neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation

def surfaceCircularProfile (F : Base → Vec) (a : Base → ℝ)
    (e₁ e₂ : GeometricJet → Vec) (α : GeometricJet × ℝ → ℝ) : Base × ℝ → BoundaryProfile :=
  circularFamilyProfile
    (fun x => coordDeriv dx F x - jetNormal (CollarVelocity.jetSection F x))
    (coordDeriv dx F) (coordDeriv dy F) (coordDeriv dy (coordDeriv dy F))
    (fun x => velocityRadius (jetNormal (CollarVelocity.jetSection F x)) (a x))
    (e₁ ∘ CollarVelocity.jetSection F) (e₂ ∘ CollarVelocity.jetSection F)
    (fun z => α (CollarVelocity.jetSection F z.1,z.2)) dy

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceBoundaryCollar
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the zero-amplitude collar estimate to the actual immersion and
its preferred jet frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation CollarVelocity

def surfaceFrozenFirst (F : Base → Vec) (a : Base → ℝ) (e₁ e₂ : GeometricJet → Vec) : Base × ℝ → ℝ :=
  frozenFirst (fun x => coordDeriv dx F x-jetNormal (jetSection F x))
    (coordDeriv dx F) (coordDeriv dy F) (coordDeriv dy (coordDeriv dy F))
    (fun x => velocityRadius (jetNormal (jetSection F x)) (a x))
    (e₁ ∘ jetSection F) (e₂ ∘ jetSection F) dy

def surfaceFrozenSize (F : Base → Vec) (a : Base → ℝ) (e₁ e₂ : GeometricJet → Vec) : Base × ℝ → ℝ :=
  frozenSize (coordDeriv dx F) (coordDeriv dy F) (coordDeriv dy (coordDeriv dy F))
    (fun x => velocityRadius (jetNormal (jetSection F x)) (a x))
    (e₁ ∘ jetSection F) (e₂ ∘ jetSection F)

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCovectorFamily
attribute [-instance] _root_.instVAddIntReal_solutions
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

def circularCovectorJoint (i j : B.centers) (L : ℝ) (z : Base × JetPolynomial.Base) : Plane →L[ℝ] ℝ :=
  B.phaseCovectorRead j (B.circularPhase i 0 L) z.2+
    z.1.1 • B.phaseCovectorRead j (B.circularPhase i (1,0) 0) z.2+
    z.1.2 • B.phaseCovectorRead j (B.circularPhase i (0,1) 0) z.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRead
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric and intrinsic Gauss expression in phase coordinates are
fixed by the prescribed global metric, independently of its isometric
realization. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseMetricRead (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base)
    (g : SmoothMetric M) (x : SmallModes.Base) : PhaseMean.Tensor :=
  tensorCoordinatePullbackValue T (baseEquiv.symm x)
    (A.tensorChartRead i g.inner (T (baseEquiv.symm x)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseNormalLift
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull a local normal field in the phase coordinates back to the surface.
The result is smooth, unit length and normal on its actual chart domain. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseNormalLift (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (n : SmallModes.Base → NormalFrame.Vec) : M → Space :=
  fun p => spaceCoordinates.symm (n (baseEquiv (e (chart (i : M) p))))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GoodSmoothingAtlas
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing atlas subordinate to actual good-phase neighborhoods. -/
noncomputable section
open Set Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def PhasePatch.phaseBasis {F : M → Space} {H : Base → PhaseMean.Tensor} {p : M}
    (P : PhasePatch F H p) : PhaseBasis where
  ξ := P.ξ
  Q := P.Q
  decomposition := P.decomposition
  nonzero := fun j => ((P.admissible _ P.centerO).2.2.1 j).1

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PreferredNormalPhasePullback
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull the actual global preferred normal into the primitive's phase
coordinates, preserving smoothness, unit length and orthogonality. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace PreferredNormal
variable {F : M → Space} (n : PreferredNormal F)

def inPhase (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    Base → NormalFrame.Vec := spaceCoordinates ∘ n.vector ∘ (surfacePhaseChart q e).symm

end PreferredNormal
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedInverseJacobian
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the inverse Jacobian field in dimension two. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def inverseJacobianField (A : Base → Base →L[ℝ] Base) (x : Base) : Base →L[ℝ] Base :=
  (coordDet (A x))⁻¹ • planeAdjugate (A x)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCombinedModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.combinedModesDualAdd
local instance combinedModesFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance combinedModesFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance combinedModesDualSmul_r8dee02_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance combinedModesSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance combinedModesSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def globalPolynomialQuadraticMean {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression) (F : M → Space) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ) : ∀ p : M, CovariantTwoTensor p :=
  A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
    combinedQuadraticMean (Q i) ε (A.jetChartMap i F)
      (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x)

def globalPolynomialQuadraticTarget {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    (i : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.chartWeightCompact i)) where
  toFun := fun x => (A.planeWeight i x)^2 •
    combinedQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
      (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l x
  contDiff' := by
    apply ((A.planeWeight_smooth i).pow 2).smul
    apply ContDiff.add
    · exact RealModes.quadraticAmplitude_smooth
        (fun j => A.vectorPlaneRead_smooth i (hφ j))
        (fun j => A.vectorPlaneRead_smooth i (hZ j)) τ l
    · apply contDiff_pi.mpr
      intro k
      exact (contDiffOn_univ.mp (quadraticFamilyCoefficient_smooth isOpen_univ (hQ i k)
        (A.jetChartMap_smooth i hF) (fun j => A.vectorChartRead_smooth i (hφ j))
        (fun j => A.vectorChartRead_smooth i (hZ j)) (fun _ _ => mem_univ _) ε τ 0 l)).comp
          planeCoordinateIsometry.symm.contDiff
  zero_on_compl' := by
    intro x hx
    have hw := (A.supportedPlaneWeight i).zero_on_compl hx
    change A.planeWeight i x = 0 at hw
    simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.zero_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialModeMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modeMeanDualAdd
local instance modeMeanFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modeMeanFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modeMeanDualSmul_r8dee02_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)



local instance modeMeanSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modeMeanSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def polynomialModeMean {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression) (F : M → Space) (ε τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin 4 → ℂ) : ∀ p : M, CovariantTwoTensor p :=
  A.tensorPlaneRestore (fun i y => (A.planeWeight i y)^2 •
    (fun k => quadraticMeanCoefficient (Q i k) ε (A.jetChartMap i F)
      (A.vectorChartRead i φ) (A.vectorChartRead i Z) τ 0 (planeCoordinateIsometry.symm y)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialOverlap
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic targets retain the original support intersections on the surface. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]


namespace SmoothingAtlas
local instance polynomialOverlapFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialOverlapFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialOverlapDualAdd_r8dee02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialOverlapDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance polynomialOverlapSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialOverlapSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [Fintype ι] [DecidableEq ι] in
lemma globalPolynomialQuadraticTarget_overlap {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    tsupport (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l) ⊆
      (modeSupport (A.quadraticOverlapCompact S hS k l) : Set SmallModes.Base) := by
  intro x hx
  let V := combinedQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
    (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l
  have hw : x ∈ tsupport (fun y => (A.planeWeight k y)^2) :=
    tsupport_smul_subset_left (fun y => (A.planeWeight k y)^2) V hx
  have hw' : x ∈ tsupport (A.planeWeight k) := by
    have hs : tsupport (fun y => (A.planeWeight k y)^2) ⊆ tsupport (A.planeWeight k) := by
      simpa only [pow_two] using
        (tsupport_mul_subset_left (f := A.planeWeight k) (g := A.planeWeight k))
    exact hs hw
  have hkx := (A.supportedPlaneWeight k).tsupport_subset hw'
  have hv : x ∈ tsupport V := tsupport_smul_subset_right (fun y => (A.planeWeight k y)^2) V hx
  have hqq : x ∈ RealModes.quadraticSupport (fun a => tsupport (A.vectorPlaneRead k (Z a))) l := by
    have hadd := tsupport_add
      (RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
        (fun a => A.vectorPlaneRead k (Z a)) l)
      (coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
        (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l) hv
    rcases hadd with hm | hp
    · exact RealModes.quadraticAmplitude_tsupport τ _ _ (fun _ => Subset.rfl) l hm
    · have hc := tsupport_comp_preimage
        (quadraticFamilyTensor (Q k) ε (A.jetChartMap k F)
          (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l)
        planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous hp
      have hh := quadraticFamilyTensor_tsupport (Q k) ε (A.jetChartMap k F)
        (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0
        (fun a => isClosed_tsupport (A.vectorChartRead k (Z a))) (fun _ => Subset.rfl) l hc
      have hread (a) (ha : planeCoordinateIsometry.symm x ∈ tsupport (A.vectorChartRead k (Z a))) :
          x ∈ tsupport (A.vectorPlaneRead k (Z a)) := by
        have he : A.vectorPlaneRead k (Z a) ∘ planeCoordinateIsometry = A.vectorChartRead k (Z a) := by
          funext y
          simp only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
        rw [← he] at ha
        have hv := tsupport_comp_preimage (A.vectorPlaneRead k (Z a)) planeCoordinateIsometry
          planeCoordinateIsometry.continuous ha
        simpa only [Set.mem_preimage,planeCoordinateIsometry.apply_symm_apply] using hv
      rcases l with a | ⟨a,b,c⟩
      · exact hread a hh
      · exact ⟨hread a hh.1,hread b hh.2⟩
  have hpx : (chart (k : M)).symm (planeCoordinateIsometry.symm x) ∈ globalQuadraticSupport S l := by
    rcases l with a | ⟨a,b,c⟩
    · exact hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq)
    · exact ⟨hSZ a (A.vectorPlaneRead_support_on_weight k (Z a) hkx hqq.1),
        hSZ b (A.vectorPlaneRead_support_on_weight k (Z b) hkx hqq.2)⟩
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hkx
  have hpS : p ∈ globalQuadraticSupport S l := by
    simpa only [planeCoordinateIsometry.symm_apply_apply,
      (chart (k : M)).left_inv (A.weight_support k hp)] using hpx
  exact ⟨chart (k : M) p,⟨p,⟨hp,hpS⟩,rfl⟩,rfl⟩

def globalPolynomialQuadraticTargetRestricted {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a)) (hSZ : ∀ a, tsupport (Z a) ⊆ S a)
    (k : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.quadraticOverlapCompact S hS k l)) :=
  ContDiffMapSupportedIn.of_support_subset
    (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l).contDiff
    (subset_closure.trans
      (A.globalPolynomialQuadraticTarget_overlap Q hQ F hF ε τ φ Z hφ hZ S hS hSZ k l))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitiveMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized mean identities for the global primitive iteration.
The residual is always that of the actual restored polynomial metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveDualSmul
variable (A : SmoothingAtlas M) {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberNormed
local instance atlasPrimitiveSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasPrimitiveSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def polynomialMeanTarget
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ δ' : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  (δ^2)⁻¹ • (γ-A.atlasPolynomialMetric P ε G-δ'^2 • γ)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveTensorMetric
attribute [-instance] _root_.instVAddIntReal_solutions
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ptFiberSpace
local instance ptDualAdd_r8dee02_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ptDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ptFiberNormed
local instance ptSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance ptSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def immersionMetric {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) : SmoothMetric M :=
  positiveTensorMetric (inducedTensor F) (A.inducedTensor_smooth hF)
    (by
      intro p v w
      change inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel F p w) = _
      exact real_inner_comm _ _)
    (by
      intro p v hv
      change 0 < inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel F p v)
      apply real_inner_self_pos.mpr
      intro hz
      apply hv
      apply hI p
      rw [map_zero]
      exact hz)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShortMetricPath
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive metric remainder and the actual smooth metric path used
by the finite primitive preparation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathDualAdd
local instance pathFiberNormed_r8dee02_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance pathFiberSpace_r8dee02_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance pathDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (g : SmoothMetric M) {F : M → Space}
  (hF : ContMDiff planeModel spaceModel ∞ F)
  (hshort : ∀ p v, inducedForm F p v v ≤ (1/2 : ℝ)*g.inner p v v)

local instance pathSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def shortRemainderMetric : SmoothMetric M :=
  positiveTensorMetric (g.inner-inducedTensor F)
    (g.contMDiff.sub_section (A.inducedTensor_smooth hF))
    (by
      intro p v w
      change g.inner p v w-inducedTensor F p v w = g.inner p w v-inducedTensor F p w v
      rw [g.symm,inducedTensor_symmetric])
    (by
      intro p v hv
      change 0 < g.inner p v v-inducedForm F p v v
      have hp := g.pos p v hv
      have hs := hshort p v
      linarith)

def shortPathMetric (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (s : ℝ) (hs : 0 ≤ s) : SmoothMetric M :=
  positiveTensorMetric ((A.immersionMetric hF hI).inner+s • (A.shortRemainderMetric g hF hshort).inner)
    ((A.immersionMetric hF hI).contMDiff.add_section
      (A.shortRemainderMetric g hF hshort).contMDiff.const_smul_section)
    (by
      intro p v w
      change (A.immersionMetric hF hI).inner p v w+s*(A.shortRemainderMetric g hF hshort).inner p v w =
        (A.immersionMetric hF hI).inner p w v+s*(A.shortRemainderMetric g hF hshort).inner p w v
      rw [(A.immersionMetric hF hI).symm,(A.shortRemainderMetric g hF hshort).symm])
    (by
      intro p v hv
      have h₀ := (A.immersionMetric hF hI).pos p v hv
      have h₁ := (A.shortRemainderMetric g hF hshort).pos p v hv
      change 0 < (A.immersionMetric hF hI).inner p v v+s*(A.shortRemainderMetric g hF hshort).inner p v v
      exact add_pos_of_pos_of_nonneg h₀ (mul_nonneg hs h₁.le))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasBoundaryProfile
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def realChartMap (i : A.centers) (F : M → Space) : RField 4 :=
  A.jetChartMap i F ∘ baseEquiv.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SupportedPrimitivePatch
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed support and geometric domain of one actual primitive.
Every field is data or a local identity needed by the analytic realization. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchDualAdd
local instance patchDualSmul_r8dee02_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance patchSectionNormed_r8dee02_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchSectionSpace_r8dee02_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
structure SupportedPrimitivePatch (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (F : M → Space) (amp phi : M → ℝ) (D : Set M) where
  phase_smooth : ContDiff ℝ ∞ e
  inverse_smooth : ContDiff ℝ ∞ e.symm
  outer : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)
  cover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source
  cutoff : JetPolynomial.Base → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_source : tsupport cutoff ⊆ e.source
  amplitude : SmallModes.Base → ℝ
  amplitude_smooth : ContDiff ℝ ∞ amplitude
  amplitude_nonneg : ∀ x, 0 ≤ amplitude x
  amplitude_surface : ∀ p ∈ (surfacePhaseChart (i : M) e).source,
    amplitude (surfacePhaseChart (i : M) e p) = amp p
  amplitude_positive : ∀ x, 0 < amplitude x ↔ x ∈ (surfacePhaseChart (i : M) e) '' D
  compactSet : Set JetPolynomial.Base
  compact : IsCompact compactSet
  target : compactSet ⊆ e.target
  support : A.phaseSurfaceSupport i e compactSet = closure D
  inverse_support : e.symm '' compactSet ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base)
  cutoff_one : ∀ x ∈ e.symm '' compactSet, cutoff x = 1
  amplitude_off : ∀ x ∉ compactSet, amplitude (baseEquiv x) = 0
  compact_active : ∀ x ∈ compactSet, A.chartWeight i (e.symm x) ≠ 0
  closed_coordinates : ∀ p ∈ closure D, e (chart (i : M) p) ∈ compactSet
  source_closed : closure D ⊆ (surfacePhaseChart (i : M) e).source
  active_closed : ∀ p ∈ closure D, A.weight i p ≠ 0
  window : TopologicalSpace.Opens JetPolynomial.Base
  window_compact : IsCompact (closure (window : Set JetPolynomial.Base))
  phase_window : MapsTo e e.source window
  support_window : compactSet ⊆ window
  region : Set SmallModes.Base
  region_compact : IsCompact region
  window_region : baseEquiv '' closure (window : Set JetPolynomial.Base) ⊆ region
  openRegion : Set SmallModes.Base
  open_region : IsOpen openRegion
  region_open : region ⊆ openRegion
  normal : SmallModes.Base → NormalFrame.Vec
  normal_smooth : ContDiffOn ℝ ∞ normal openRegion
  immersion : ∀ x ∈ openRegion, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x)
  normal_properties : ∀ x ∈ openRegion,
    coordDeriv dx (A.phaseRealChartMap i e.symm F) x ⬝ᵥ normal x = 0 ∧
    coordDeriv dy (A.phaseRealChartMap i e.symm F) x ⬝ᵥ normal x = 0 ∧ normal x ⬝ᵥ normal x = 1
  convexity : ∀ x ∈ openRegion, 0 < coordinateMetricHessian
    (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F)) Prod.fst x dy dy
  boundary : ∀ x ∈ region, amplitude x = 0 →
    realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x ≠ 0 ∧
    normalize (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy x) ≠ -normal x
  tensor : A.bundleRestore A.tensorTriv i
    (fun y => fiberFromThree (localizedTensorPullback e cutoff (fun q => ![(amplitude (baseEquiv q))^2,0,0]) y)) =
      fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitivePatchCurves
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual remaining boundary curves and finite crossing points inside a
constructed primitive patch. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch
variable (d : SupportedPrimitivePatch A i e F amp phi D)

def curve (_d : SupportedPrimitivePatch A i e F amp phi D) (c : PhaseBoundaryCurve B) : Set Base := c.inPhase (i : M) e (closure D)

def innerCrossings (_d : SupportedPrimitivePatch A i e F amp phi D) (E : Set M) : Set Base := (surfacePhaseChart (i : M) e) '' (E ∩ D)

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ActualProfileCollar
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive boundary invariant on the zero-amplitude collar survives
small errors in the five profiles. No large angular derivative is needed there. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def collarInvariant (J : BoundaryProfile) (v : ℝ × ℝ × ℝ) : ℝ :=
  (profileCoefficients J 1 * v.1 + profileCoefficients J 0 * v.2.1)^2 + v.2.2 * v.1^2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Algebra_Ring_Periodic
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

-- TODO: the file this references doesn't exist in mathlib any more; rename this one appropriately!

/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma Continuous.bounded_of_onePeriodic_of_isCompact {f : X → ℝ → E} (cont : Continuous ↿f)
  (hper : ∀ x, OnePeriodic (f x)) {K : Set X} (hK : IsCompact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C
```

This is done by introducing the quotient 𝕊₁ = ℝ/ℤ as a compact topological space.
Patrick is not sure this is the optimal version.

In the first part, generalize many lemmas to any period and add to `Algebra.Ring.Periodic.lean`?
-/

section


noncomputable section

open Set Function Filter TopologicalSpace Int

open scoped Topology

section OnePeriodic

variable {α : Type*}

section

attribute [local instance] transOne

/-- A one-periodic function on `ℝ` descends to a function on the circle `ℝ ⧸ ℤ`. -/
def OnePeriodic.lift {f : ℝ → α} (h : OnePeriodic f) : 𝕊₁ → α :=
  Quotient.lift f (by intro a b hab; rcases transOne_rel_iff.mp hab with ⟨k, rfl⟩; rw [h.add_int])

end

end OnePeriodic
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_Convex_Basic
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open Function Set

section

variable {𝕜 𝕜' E E₂ E' : Type*} [Semiring 𝕜] [PartialOrder 𝕜] --[IsOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid E₂] [Module 𝕜 E₂] [AddCommMonoid E']
  [Semiring 𝕜'] [PartialOrder 𝕜'] [IsOrderedRing 𝕜'] [Module 𝕜' E'] (σ : 𝕜 →+*o 𝕜')

-- rename: `mul_support_finite_of_finprod_ne_one`?
@[to_additive]
theorem finite_of_finprod_ne_one {M : Type*} {ι : Sort _} [CommMonoid M] {f : ι → M}
    (h : ∏ᶠ i, f i ≠ 1) : (mulSupport f).Finite := by
  classical
  rw [finprod_def] at h
  contrapose h
  rw [dite_eq_right (by exact h)]

end
end
end


