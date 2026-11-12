-- Prove2me | Definitions.Def_OAIQ249SI008
-- name    : OAIQ249SI008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:12:27.286429+00:00
-- url     : https://prove2.me/theorems/486cff04-66cb-449e-99ae-fd5222a5ce6b
-- title:
--   Definitions bundle OAIQ249SI008 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 237 declarations of OpenAI's Lean: 154 definitions and 83 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestoreLM`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampReadPolynomialFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ampReadPolynomialFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionGroup`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.axisNormalizedDefect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundaryGaussReadFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedDataSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedPrimitiveReference`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularArc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularArcCompact`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularArcDomain`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularCrossingSet`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.circularNormalCovector`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactPolynomialSmallFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactPolynomialSmallFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.compactifiedDoubleCurve`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.constructedSupportFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.constructedSupportFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordToleranceFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordToleranceFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossPolyRepFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossPolyRepFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredPolyFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredPolyFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredReadFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredReadFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.cycleBoundFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.doubleCurveBoundary` and 114 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SurfaceImmersion_Atlas_AtlasCatalogCancellation`, `SurfaceImmersion_Atlas_AtlasMetricBounds`, `SurfaceImmersion_Atlas_AtlasMetricLimit`, `SurfaceImmersion_Atlas_AtlasMetricRead`, `SurfaceImmersion_Atlas_AtlasMetricReadGerms`, `SurfaceImmersion_Atlas_AtlasTensorTransition`, `SurfaceImmersion_Atlas_CrossAtlasTensorBounds`, `SurfaceImmersion_Atlas_FiniteAtlasIncrement`, `SurfaceImmersion_Atlas_GridAtlasMetric`, `SurfaceImmersion_Atlas_IndependentTensorReadTolerance`, `SurfaceImmersion_Atlas_LinearMetricChartReconstruction`, `SurfaceImmersion_Atlas_MetricAtlasReference`, `SurfaceImmersion_Atlas_MetricReadBounds`, `SurfaceImmersion_Atlas_NonlinearAtlasErrorBound`, `SurfaceImmersion_Atlas_NonlinearAtlasMetric`, `SurfaceImmersion_Atlas_PhaseExteriorDomain`, `SurfaceImmersion_Atlas_TransverseCompactCurveCharts`, `SurfaceImmersion_Correction_AtlasCombinedModes`, `SurfaceImmersion_Correction_AtlasCorrectionAssembly`, `SurfaceImmersion_Correction_AtlasGlobalPolynomialMean`, `SurfaceImmersion_Correction_AtlasLinearizedMetric`, `SurfaceImmersion_Correction_AtlasMetricLocalModel`, `SurfaceImmersion_Correction_AtlasModePolynomialQuadratic`, `SurfaceImmersion_Correction_AtlasPolynomialAmplitudeBounds`, `SurfaceImmersion_Correction_AtlasPolynomialCalculus`, `SurfaceImmersion_Correction_AtlasPolynomialFreeResidual`, `SurfaceImmersion_Correction_AtlasPolynomialIncrementBound`, `SurfaceImmersion_Correction_AtlasPolynomialInputCancellation`, `SurfaceImmersion_Correction_AtlasPolynomialLinearity`, `SurfaceImmersion_Correction_AtlasPolynomialLinearized`, `SurfaceImmersion_Correction_AtlasPolynomialMetric`, `SurfaceImmersion_Correction_AtlasPolynomialModeMean`, `SurfaceImmersion_Correction_AtlasPolynomialNearbyCancellation`, `SurfaceImmersion_Correction_AtlasPolynomialRepresentation`, `SurfaceImmersion_Correction_AtlasPolynomialSmooth`, `SurfaceImmersion_Correction_AtlasPolynomialValueBounds`, `SurfaceImmersion_Correction_AtlasPrimitiveMean`, `SurfaceImmersion_Correction_AtlasPrimitivePolynomial`, `SurfaceImmersion_Correction_AtlasRestoredPolynomialDirection`, `SurfaceImmersion_Correction_AtlasSupportedPolynomialQuadratic`, `SurfaceImmersion_Correction_CatalogGlobalQuadraticCorrection`, `SurfaceImmersion_Correction_CompactGeometryPolynomialIncrement`, `SurfaceImmersion_Correction_CrossAtlasPolynomialRepresentation`, `SurfaceImmersion_Correction_CrossAtlasRestoredPolynomial`, `SurfaceImmersion_Correction_CrossAtlasRestoredPolynomialRead`, `SurfaceImmersion_Correction_FiniteAtlasFreeMetric`, `SurfaceImmersion_Correction_FiniteSmootherBounds`, `SurfaceImmersion_Correction_FiniteSmootherWeighted`, `SurfaceImmersion_Correction_GlobalQuadraticModes`, `SurfaceImmersion_Correction_GlobalSmoothedMetricStep`, `SurfaceImmersion_Correction_GridFreeMeanIdentity`, `SurfaceImmersion_Correction_GridGlobalQuadraticCorrection`, `SurfaceImmersion_Correction_InitialCorrectionStage`, `SurfaceImmersion_Correction_InputPolynomialFreeCorrection`, `SurfaceImmersion_Correction_InputPolynomialQuadraticCancellation`, `SurfaceImmersion_Correction_InputPolynomialSmallIncrement`, `SurfaceImmersion_Correction_MetricPolynomialIncrement`, `SurfaceImmersion_Correction_NormalizedLinearModel`, `SurfaceImmersion_Correction_PolynomialAtlasFree`, `SurfaceImmersion_Correction_PolynomialAtlasFreeProfile`, `SurfaceImmersion_Correction_PolynomialAtlasSeed`, `SurfaceImmersion_Correction_PolynomialAtlasSeedProfile`, `SurfaceImmersion_Correction_PolynomialCubicRemainder`, `SurfaceImmersion_Correction_PolynomialMeanApproximation`, `SurfaceImmersion_Correction_ProfiledPolynomialSmallIncrement`, `SurfaceImmersion_Correction_TensorOperatorSmooth`, `SurfaceImmersion_Geometry_ActualOperatorTolerance`, `SurfaceImmersion_Geometry_AxisNormalizedDefect`, `SurfaceImmersion_Geometry_GlobalCubicRemainder`, `SurfaceImmersion_Geometry_GlobalInputRecurrence`, `SurfaceImmersion_Geometry_GlobalMetricStep`, `SurfaceImmersion_Geometry_NormalFrameTransport`, `SurfaceImmersion_Geometry_RealRestoredMetric`, `SurfaceImmersion_Geometry_ResolvedPrefixImage`, `SurfaceImmersion_Geometry_ScaledInitialMap`, `SurfaceImmersion_Geometry_TensorPlaneReconstruction`, `SurfaceImmersion_Geometry_TensorRestoreFinite`, `SurfaceImmersion_Geometry_UniformMetricPathBounds`, `SurfaceImmersion_Primitive_AtlasPeriodicMetric`, `SurfaceImmersion_Primitive_AtlasPrimitiveOperator`, `SurfaceImmersion_Primitive_BoundaryProfileGeometry`, `SurfaceImmersion_Primitive_BoundedPrimitiveAmplitude`, `SurfaceImmersion_Primitive_CircularRadiusCovectors`, `SurfaceImmersion_Primitive_ConstructedPrimitiveSupport`, `SurfaceImmersion_Primitive_IndependentProfiledPhase`, `SurfaceImmersion_Primitive_NonlinearPrimitiveExpansion`, `SurfaceImmersion_Primitive_PhasePrimitiveBoundaryGauss`, `SurfaceImmersion_Primitive_PhasePrimitiveGlobalTensor`, `SurfaceImmersion_Primitive_PhasePrimitiveMetricRead`, `SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds`, `SurfaceImmersion_Primitive_PrimitiveCoefficientCoordinates`, `SurfaceImmersion_Primitive_PrimitiveCoordinateTolerance`, `SurfaceImmersion_Primitive_PrimitiveCycleBounds`, `SurfaceImmersion_Primitive_PrimitiveDataC1`, `SurfaceImmersion_Primitive_PrimitiveDomainWindow`, `SurfaceImmersion_Primitive_PrimitiveFrameBounds`, `SurfaceImmersion_Primitive_PrimitiveOperatorStability`, `SurfaceImmersion_Primitive_SupportedPrimitivePatch`, `SurfaceImmersion_Primitive_TransverseCircularRadii`, `SurfaceImmersion_Whitney_CircularBoundaryArcs`, `SurfaceImmersion_Whitney_CompactifiedDoubleCurve`, `SurfaceImmersion_Whitney_EqualIndexFrameFilling`, `SurfaceImmersion_Whitney_NormalLinearizationHomotopy`, `SurfaceImmersion_Whitney_OppositeIndexFrameFilling`, `SurfaceImmersion_Whitney_QuadraticDoubleTransverse`, `SurfaceImmersion_Whitney_SmoothDoubleAtlas`, `SurfaceImmersion_Whitney_SmoothSurfaceDoubleChart`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI003`, `OAIQ249SI004` and `OAIQ249SI005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI011` and `OAIQ249SI014`; the statements `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CircularPrimitiveFamily_realize_total`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_crossing_transition`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_exterior_preservation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_second_transition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_identity`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_fixed_order_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nearby_cancellation_all_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coefficientFrameRead_C1_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_geometry_polynomial_increment`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_phase_exterior_crossing_preservation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_surface_boundary_matching`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_surface_phase_exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exists_transverse_circular_radii`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_increment_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_metric_split`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_induced_metric_read_tolerance`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_nonlinear_jet_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_nonlinear_lowJet_neighborhood_of_C2`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_intrinsic_crossing_transition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_atlas_free_profile`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_point_crossings`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_germ`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_circular_starting_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_polynomial_representation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_zeroPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_crosscap_connecting_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_metric_good_smoothingAtlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_metricPhaseData_of_whitney`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_circular_direction_first`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_crossings` and `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_curve_cover`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation_in_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_crossing_transition`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.finite_copy_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_circularPhase_frame_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coefficientFrameRead_C1_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exists_transverse_circular_radii`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_metric_split`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_surface_correction_budgets`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_normal_margin`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_point_crossings`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_germ`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator_smooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitive_term_background_C1_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_small_metric_prepared_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_remainder_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_crosscap_connecting_arc`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_metric_good_smoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_circular_direction_first`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_crosscap_ordered_arc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_finite_regular_path`, `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_crossings` and `OAI_ClosedSurfaceR4_GeometryPreservation_compact_actual_profile_curve_cover`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI003
import Definitions.Def_OAIQ249SI004
import Definitions.Def_OAIQ249SI005

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds and derivative gain for the same finite-order smoother. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def gainConstant (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (∫ y, ‖iteratedFDeriv ℝ m (kernel 0) y‖) *
    (1 + ∫ y, ‖kernel 0 y‖) ^ i

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted bounds for finite-order smoothing in the chart norms used by
the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedGainConstant (n m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), gainConstant n j

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPlaneReconstruction
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
local instance reconstructionFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualSmul_r201a37_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance reconstructionSectionNormed_r201a37_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace_r201a37_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_add (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f+g) = A.tensorPlaneRestore f + A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.add_apply, map_add, bundleRestore, smul_add,
    Finset.sum_add_distrib]

lemma tensorPlaneRestore_smul (a : ℝ) (f : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (a • f) = a • A.tensorPlaneRestore f := by
  funext p
  simp only [tensorPlaneRestore, Pi.smul_apply, map_smul, bundleRestore, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasLinearizedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual local linear residuals to the global metric tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasLinearFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasLinearDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCorrectionAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble actual local supported corrections. Atlas constants are chosen before the phase family and its cardinality. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance localCorrectionAssemblyFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance localCorrectionAssemblyFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance localCorrectionAssemblyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasCatalogCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble actual local supported corrections. Atlas constants are chosen before the phase family and its cardinality. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance catalogAtlasCancellationFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance catalogAtlasCancellationFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance catalogAtlasCancellationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearMetricChartReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed metric is reconstructed from the genuine chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance linearReadFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance linearReadFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance linearReadDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearReadDualSmul_r201a37_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance linearReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalCubicRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform atlas estimate for the actual mixed metric and quadratic correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance cubicFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance cubicFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance cubicDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
local instance metricBoundFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalQuadraticModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global quadratic phase expansion, retaining all cross-chart interactions. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance globalModeMetricFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance globalModeMetricFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance globalModeMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealRestoredMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-coordinate version of the supported metric restoration identity. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance realRestoredMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance realRestoredMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance realRestoredMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRestoreFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-sum linearity of the actual tensor restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorRestoreFiniteDualAdd
local instance tensorRestoreFiniteFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorRestoreFiniteFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorRestoreFiniteDualSmul_r201a37_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance tensorRestoreFiniteSectionNormed_r201a37_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorRestoreFiniteSectionSpace_r201a37_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def tensorPlaneRestoreLM : (A.centers → SmallModes.Base → PhaseMean.Tensor) →ₗ[ℝ]
    ((p : M) → CovariantTwoTensor p) where
  toFun := A.tensorPlaneRestore
  map_add' := A.tensorPlaneRestore_add
  map_smul' := A.tensorPlaneRestore_smul

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized-defect identity for the unsmoothed global map update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance metricStepFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricStepFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricStepDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricStepDualSmul_r201a37_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricStepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)

local instance metricStepSectionSpace_r201a37_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def realizedTensorError (target Hs : ∀ p : M, CovariantTwoTensor p)
    (δ δ' : ℝ) (G U : M → Space) : ∀ p : M, CovariantTwoTensor p :=
  inducedTensor (G+U)-inducedTensor G-(δ^2 • Hs-δ'^2 • target)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized atlas defect controls the actual metric of the limit. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection

local instance metricLimitFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLimitFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance metricLimitDualAdd_r201a37_1 :
    ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricLimitDualSmul_r201a37_1 :
    ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricLimitSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the active chart locus the local metric is exactly the chart read
of the induced global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance metricReadExactFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadExactFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricReadExactDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricAtlasReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth metric section gives the reference tensor used by
the compact good-phase construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean
open JetPolynomial (planeCoordinateIsometry)
open JetPolynomial.Perturbation (modeSupport)

local instance metricReferenceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReferenceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance metricReferenceDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricReferenceDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricReadGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A metric atlas reading agrees as a germ with the actual coordinate
metric when the outer cutoff is locally one. This also identifies its
first derivative, as required by the connection estimates. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseMean
local instance metricReadGermFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadGermFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorTransition
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

local instance transitionFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance transitionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance transitionDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tensor bounds persist when the finite correction atlas changes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance crossTensorBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossTensorBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance crossTensorBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossTensorBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteAtlasFreeMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global free-mode identities for an arbitrary finite family in
each fixed atlas chart. This accommodates the variable number of grid cells. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance finiteAtlasFreeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteAtlasFreeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance finiteAtlasFreeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCubicRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed atlas constant gives polynomial dependence of the actual cubic
metric remainder on the free and forced displacement budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialCubicFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialCubicFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialCubicDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FiniteAtlasIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free/forced metric step for an arbitrary finite family of local phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance finiteIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance finiteIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance finiteIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance finiteIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance finiteIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridAtlasMetric
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
local instance gridAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal frames and scaled second-form coefficients are smooth functions of
exactly the five derivative components retained by the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

def profileNormalPart (J : BoundaryProfile) : Vec :=
  realNormalPart (J 0) (J 1) (J 2)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_IndependentTensorReadTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small background-atlas norm gives small tensor readings in each
fixed primitive chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance readToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance readToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance readToleranceDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance readToleranceDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricReadBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact positive metric range and global first-order bounds for atlas readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates
local instance metricReadBoundsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

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
local instance polynomialMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialMetricDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First and second derivatives of the globally restored polynomial
are the operators used in its exact Taylor identity. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialDerivativeFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialDerivativeFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialDerivativeDualAdd_r201a37_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialDerivativeDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance polyRepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polyRepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polyRepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalSmoothedMetricStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed update has a defect bound linear in higher input norms. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance smoothStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalInputRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both components of the actual next input admit a common recurrence bound. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates JetPolynomial
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance inputRecurrenceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputRecurrenceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledInitialMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial contraction of an approximate immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance initialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance initialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance initialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasRestoredPolynomialDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported Euclidean field is restored with exactly its original
localized jet, so the local polynomial solver acts on the actual direction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredDirectionFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredDirectionFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance restoredDirectionDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitivePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embed the three mean-polynomial coefficients of one primitive in the
actual global atlas operator, with zero contribution from every other chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
local instance primitivePolyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitivePolyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance primitivePolyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialValueBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance polynomialValueFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialValueFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPeriodicMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric of the supported global periodic map is exactly the
restoration of the metric of its local periodic ansatz. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance periodicMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance periodicMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance periodicMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance nonlinearMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance nonlinearMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance nonlinearMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasErrorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance nonlinearErrorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance nonlinearErrorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance nonlinearErrorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance nonlinearErrorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasMetricLocalModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local coordinate models of the complete perturbed global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricLocalFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLocalFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricLocalDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseExteriorDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior comparison regions in the actual phase chart, including their
boundary points. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def phaseExteriorDomain (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (O : Set M) :
    Set JetPolynomial.Base :=
  ((chart q).trans e) '' (O ∩ ((chart q).trans e).source)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticDoubleTransverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from its endpoint the double curve of a quadratic crosscap is
transverse: the difference map on the two source sheets is a submersion. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def quadraticDoubleDifference (f : Base → ProjectionTarget 3) (a : Base)
    (z : Base × Base) : ProjectionTarget 3 :=
  centeredSurfaceTaylor f a z.1-centeredSurfaceTaylor f a z.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactifiedDoubleCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactifying distinct unordered double pairs retains precisely the
prepared crosscaps on the diagonal. -/
noncomputable section
open Set Topology Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]

def compactifiedDoubleCurve (f : M → ProjectionTarget 3) : Set (UnorderedSurfacePairs M) :=
  unorderedPair '' closure (surfaceDoublePairs f)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TransverseCompactCurveCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An unconditional compact double curve with genuine line charts in
its interior and half-line charts at precisely its finite diagonal set. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

def doubleCurveBoundary (f : M → ProjectionTarget 3) : Set (compactifiedDoubleCurve f) :=
  {z | ∃ p, unorderedPair (p,p) = z.val}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasModePolynomialQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial part of the quadratic global mode interaction splits
into its zero-phase mean and all nonzero quadratic phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance modePolynomialFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modePolynomialFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modePolynomialDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCombinedModes
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
local instance combinedModesFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance combinedModesFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance combinedModesDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasSupportedPolynomialQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance quadraticSupportFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance quadraticSupportFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance quadraticSupportDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialModeMean
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
local instance modeMeanFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modeMeanFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modeMeanDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalPolynomialMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global finite phase expansion has the prescribed quadratic mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance globalPolynomialMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalPolynomialMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialAmplitudeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on every chart reading of the actual complex amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance ampReadPolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance ampReadPolynomialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance ampReadPolynomialDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance ampReadPolynomialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linearity in the direction of the actual global polynomial. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialLinearFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialLinearFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialLinearDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLinearized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global polynomial linearization is assembled from the
constructed local representatives, for every supported family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialAssemblyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAssemblyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialFreeResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform global metric-linear residual of the actual free oscillation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance polynomialFreeResidualFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFreeResidualFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFreeResidualDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFreeResidualDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance polynomialSmoothFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSmoothFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSmoothDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSmoothDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialIncrementBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance polynomialIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialNearbyCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Atlas cancellation uniform over a neighborhood of a fixed immersion.
The reference geometry, per-chart shifted profiles and finite phase family
determine all constants before the varying map, target or scale is chosen.
-/

noncomputable section

open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing

open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance nearbyPhasePolynomialFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance nearbyPhasePolynomialFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance nearbyPhasePolynomialDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialInputCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform atlas cancellation from the global norms used in the iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputPhasePolynomialFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPhasePolynomialFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance inputPhasePolynomialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitiveMean
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
local instance atlasPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance atlasPrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasPrimitiveDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CatalogGlobalQuadraticCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual global quadratic correction with explicit polynomial budgets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance catalogGlobalQuadraticFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance catalogGlobalQuadraticFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance catalogGlobalQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InputPolynomialQuadraticCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform cancellation of the actual quadratic oscillations at a nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputPolynomialQuadFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPolynomialQuadFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance inputPolynomialQuadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputPolynomialQuadDualSmul_r201a37_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputPolynomialQuadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InputPolynomialFreeCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct a forced correction uniformly for nearby maps from their input norms. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance inputPolynomialFreeQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputPolynomialFreeQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputPolynomialFreeQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputPolynomialFreeQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InputPolynomialSmallIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble a uniform nearby-map increment from fixed profiles and an adjusted mean. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
local instance polynomialSmallAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSmallAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialSmallAtlasDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSmallAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ProfiledPolynomialSmallIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance profiledPolynomialSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledPolynomialSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance profiledPolynomialSmallDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledPolynomialSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CompactGeometryPolynomialIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance compactPolynomialSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance compactPolynomialSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance compactPolynomialSmallDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance compactPolynomialSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasRestoredPolynomialRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A restored polynomial tensor has a constructed finite jet expression
in every overlapping correction chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance crossRestoredReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossRestoredReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance crossRestoredReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasRestoredPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global coefficient extensions for one restored polynomial tensor.
The representation holds on the open nonzero partition-weight locus,
including chart points outside the support of the restored term. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance crossRestoredPolyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossRestoredPolyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance crossRestoredPolyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasPolynomialRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance crossPolyRepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossPolyRepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridFreeMeanIdentity
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
local instance gridFreeMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridFreeMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridFreeMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridFreeMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridFreeMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridGlobalQuadraticCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual correction for the variable grid with a fixed polynomial budget. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridGlobalQuadraticFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGlobalQuadraticFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance gridGlobalQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InitialCorrectionStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Build the first actual correction stage from finite metric accuracy. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance initialStageFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MetricPolynomialIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual metric-adapted immersion supplies all the small-increment geometry. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance metricPolynomialSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricPolynomialSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricPolynomialSmallDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricPolynomialSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothSurfaceDoubleChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-line charts of the actual double locus have smooth regular inverses. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem smooth_surface_double_pair_chart_data {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ,
      (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ c.source ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.1) c.target ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.2) c.target ∧
      (∀ t ∈ c.target, Function.Injective
        ((mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.1) t).prod
          (mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.2) t))) ∧
      ∃ C : Base × Base → ℝ, ContDiff ℝ ∞ C ∧
        ∀ z ∈ c.source, z.val.1 ∈ (chart x).source ∧ z.val.2 ∈ (chart y).source ∧
          c z = C (chart x z.val.1,chart y z.val.2) := by
  obtain ⟨U,F,hU,hxU,hUs,hF,heF⟩ := surface_chart_representative hf x
  obtain ⟨V,G,hV,hyV,hVs,hG,heG⟩ := surface_chart_representative hf y
  let H : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hD : Function.Surjective (fderiv ℝ H (chart x x,chart y y)) :=
    (surface_pair_coordinate_regular_iff x y (hUs hxU) (hVs hyV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hyV))).mp hreg
  obtain ⟨b,hb,hbf,hbSmooth,hbInv⟩ := double_locus_submersion_chart hH (chart x x,chart y y) hD
  let R : Set (M × M) := (U ×ˢ V) ∩ {z | z.1 ≠ z.2}
  have hR : IsOpen R := (hU.prod hV).inter isClosed_diagonal.isOpen_compl
  let a := ((chart x).prod (chart y)).restrOpen R hR
  let e := a.trans b
  have hp : (x,y) ∈ e.source := by
    exact ⟨⟨⟨hUs hxU,hVs hyV⟩,⟨⟨hxU,hyV⟩,hxy⟩⟩,hb⟩
  have hmatch : ∀ z ∈ e.source, z ∈ surfaceDoublePairs f ↔ (e z).1 = 0 := by
    intro z hz
    have hsrc : z ∈ (U ×ˢ V) ∩ {z | z.1 ≠ z.2} := hz.1.2
    have hfirst : (e z).1 = f z.1-f z.2 := by
      change (b (chart x z.1,chart y z.2)).1 = _
      rw [hbf]
      change F (chart x z.1)-G (chart y z.2) = _
      change (F ∘ chart x) z.1-(G ∘ chart y) z.2 = _
      rw [← heF hsrc.1.1,← heG hsrc.1.2]
    rw [hfirst,sub_eq_zero]
    exact and_iff_right hsrc.2

  obtain ⟨c,hpc,hcs,hct,hcf,hci⟩ :=
    matched_zero_subset_line_chart_data e (surfaceDoublePairs f) (x,y) hp ⟨hxy,heq⟩ hmatch
  let θ : ℝ → Base × Base := fun t => b.symm (0,t)
  let A : ℝ → M := fun t => (chart x).symm (θ t).1
  let B : ℝ → M := fun t => (chart y).symm (θ t).2
  have htE (t : ℝ) (ht : t ∈ c.target) : (0,t) ∈ e.target := by
    rw [hct] at ht
    exact ht
  have htB (t : ℝ) (ht : t ∈ c.target) : (0,t) ∈ b.target := (htE t ht).1
  have htA (t : ℝ) (ht : t ∈ c.target) : θ t ∈ a.target := (htE t ht).2
  have hmapA : MapsTo (fun t => (θ t).1) c.target (chart x).target := by
    intro t ht
    exact (htA t ht).1.1
  have hmapB : MapsTo (fun t => (θ t).2) c.target (chart y).target := by
    intro t ht
    exact (htA t ht).1.2
  have hθ : ContDiffOn ℝ ∞ θ c.target :=
    hbInv.comp (contDiff_const.prodMk contDiff_id).contDiffOn htB
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞ A c.target :=
    (chart_symm_smooth x).comp hθ.fst.contMDiffOn hmapA
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞ B c.target :=
    (chart_symm_smooth y).comp hθ.snd.contMDiffOn hmapB
  have hAB (t : ℝ) (ht : t ∈ c.target) : (c.symm t).val = (A t,B t) := hci t ht
  have hAeq : EqOn (fun t => (c.symm t).val.1) A c.target :=
    fun t ht => congrArg Prod.fst (hAB t ht)
  have hBeq : EqOn (fun t => (c.symm t).val.2) B c.target :=
    fun t ht => congrArg Prod.snd (hAB t ht)
  refine ⟨c,hpc,hA.congr hAeq,hB.congr hBeq,?_⟩
  constructor
  · intro t ht
    have hEA : (fun s => (c.symm s).val.1) =ᶠ[𝓝 t] A :=
      hAeq.eventuallyEq_of_mem (c.open_target.mem_nhds ht)
    have hEB : (fun s => (c.symm s).val.2) =ᶠ[𝓝 t] B :=
      hBeq.eventuallyEq_of_mem (c.open_target.mem_nhds ht)
    rw [hEA.mfderiv_eq,hEB.mfderiv_eq]
    apply paired_curve_derivative_injective x y t
      (hA.contMDiffAt (c.open_target.mem_nhds ht))
      (hB.contMDiffAt (c.open_target.mem_nhds ht))
      ((chart x).map_target (hmapA ht)) ((chart y).map_target (hmapB ht))
      (hθ.contDiffAt (c.open_target.mem_nhds ht))
    · filter_upwards [c.open_target.mem_nhds ht] with s hs
      apply Prod.ext
      · exact ((chart x).right_inv (hmapA hs)).symm
      · exact ((chart y).right_inv (hmapB hs)).symm
    · let g : Base × Base → ℝ := fun z => (b z).2
      have hg : ContDiff ℝ ∞ g := hbSmooth.snd
      have heqθ : g ∘ θ =ᶠ[𝓝 t] id := by
        filter_upwards [c.open_target.mem_nhds ht] with s hs
        exact congrArg Prod.snd (b.right_inv (htB s hs))
      have hθt := hθ.differentiableOn (by simp) t ht
      have hd : (fderiv ℝ g (θ t)).comp (fderiv ℝ θ t) = ContinuousLinearMap.id ℝ ℝ := by
        rw [← fderiv_comp t (hg.differentiable (by simp) _)
          (hθt.differentiableAt (c.open_target.mem_nhds ht)),heqθ.fderiv_eq,fderiv_id]
      intro u v huv
      have hh := congrArg (fderiv ℝ g (θ t)) huv
      change ((fderiv ℝ g (θ t)).comp (fderiv ℝ θ t)) u =
        ((fderiv ℝ g (θ t)).comp (fderiv ℝ θ t)) v at hh
      simpa only [hd,ContinuousLinearMap.id_apply] using hh
  · refine ⟨(fun z => (b z).2),hbSmooth.snd,?_⟩
    intro z hz
    have hzs : z.val ∈ e.source := by rw [hcs] at hz; exact hz
    exact ⟨hzs.1.1.1,hzs.1.1.2,hcf z hz⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothDoubleAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual double-locus charts retain smooth coordinate expressions in
both directions. Their overlap maps are ordinary smooth real functions. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem exists_smooth_double_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p : surfaceDoublePairs f)
    (hreg : Function.Surjective (surfacePairDerivative f p.val.1 p.val.2)) :
    ∃ c : SmoothDoubleChart f, p ∈ c.coord.source := by
  obtain ⟨c,hp,hA,hB,hpair,C,hC,hform⟩ := smooth_surface_double_pair_chart_data hf
    p.val.1 p.val.2 p.property.1 p.property.2 hreg
  exact ⟨⟨p.val.1,p.val.2,c,C,hC,hform,hA,hB,hpair⟩,hp⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ResolvedPrefixImage
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete trace invariant used while joining the ordered smooth
bridges: old path points plus only the bridges already inserted. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} (γ : Path p q) {T : ι → ℝ} {O : Set M}

def resolvedPrefixImage (B : ∀ i, LocalCornerBridge γ (T i) O) (J : Set ι) (a : ℝ) : Set M :=
  γ.extend '' Icc 0 a ∪ ⋃ i ∈ J, (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisNormalizedDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal coordinates adapted to the two simple zeros on the axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def axisNormalizedDefect (d : ℝ → Base) (N : Base → Base) (x : Base) : Base :=
  (planeComplexFrame (d (x 1))).inverse (N x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedLinearModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first-order transverse model in normalized coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalTransverse (G : Base → Base) (t : ℝ) : Base :=
  fderiv ℝ G (crosscapAxis t) (![1,0] : Base)
def normalizedLinearModel (G : Base → Base) (p q : ℝ) (x : Base) : Base :=
  normalizedAxisPolynomial p q x+x 0 • normalTransverse G (x 1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas polynomial free bounds for variable finite phase families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialAtlasFreeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAtlasFreeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAtlasFreeDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAtlasFreeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasFreeProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialFreeProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialFreeProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialFreeProfileDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialFreeProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex amplitude bounds for arbitrary finite phase families. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialAtlasSeedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAtlasSeedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAtlasSeedDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAtlasSeedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAtlasSeedProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
local instance polynomialSeedProfileFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSeedProfileFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialSeedProfileDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSeedProfileDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slow iteration solves the actual restored polynomial mean
metric to any prescribed finite unweighted order. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization WeightedEstimates
local instance meanApproxFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance meanApproxFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance meanApproxDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance meanApproxDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
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
local instance atlasOperatorFiberComplete_r201a37_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionNormed
local instance atlasOperatorSectionSpace_r201a37_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance atlasOperatorSectionGroup (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (atlasOperatorSectionNormed p).toAddCommGroup

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorOperatorSmooth
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

local instance operatorSmoothFiberNormed_r201a37_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorSmoothFiberSpace_r201a37_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance operatorSmoothFiberComplete_r201a37_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance operatorSmoothDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.operatorSmoothDualSmul
local instance operatorSmoothSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorSmoothSectionSpace_r201a37_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance operatorSmoothSectionGroup (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (operatorSmoothSectionNormed p).toAddCommGroup

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOperatorStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform stability of the finite primitive inverse when its coefficient
functionals, cutoffs and phase covectors all vary independently. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberSpace
local instance dataFiberComplete_r201a37_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd
local instance dataDualSmul_r201a37_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataFiberGroup
def primitiveDataOperator (z : PrimitiveOperatorData ι) : TensorFiber →L[ℝ] TensorFiber :=
  completedPrimitiveOperator z.1.1 z.1.2 z.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFrameBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact bounds for actual coefficient and differential fields in the
fixed tensor frames, including overlapping phase charts. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance frameBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance frameBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance frameBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance frameBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ActualOperatorTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent cutoff and phase perturbations give uniform control of
the actual operator in every chart of the fixed primitive atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance actualToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_NormalLinearizationHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearizing only the transverse coordinate preserves exactly the two zeros
on a common thin rectangle throughout the homotopy. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def linearDefectHomotopy (G : Base → Base) (p q s : ℝ) (x : Base) : Base :=
  (1-s) • G x+s • normalizedLinearModel G p q x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EqualIndexFrameFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The equal-index polynomial pair has a genuine compact relative frame filling. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def equalIndexFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 ((x 0)^2-(x 1)^2-1) (2*x 0*x 1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalFrameTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact algebra transporting a filled normalized frame to the derivative
of the original surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def normalOutput (d : Base) : FrameTarget →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.proj 0).smulRight ((0:Base),1)+
    (ContinuousLinearMap.proj 1).smulRight (planeComplexFrame d (![1,0] : Base),0)+
    (ContinuousLinearMap.proj 2).smulRight (planeComplexFrame d (![0,1] : Base),0)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformMetricPathBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-order metric bounds fixed before finite spherical modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance pathBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance pathBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance pathBoundDualAdd_r201a37_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance pathBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeParameterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 control of the actual inverse and square-root amplitude map.
The parameter bounds are fixed before a later family is composed with it. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberSpace
local instance amplitudeFiberComplete_r201a37_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeDualAdd
local instance amplitudeDualSmul_r201a37_1 : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeFiberGroup
def primitiveParameterInverse (z : PrimitiveAmplitudeData ι) : TensorFiber →L[ℝ] TensorFiber :=
  (primitiveDataOperator z.1).inverse

def primitiveParameterCoefficient (i : ι) (z : PrimitiveAmplitudeData ι) : ℝ :=
  z.1.1.1 i (primitiveParameterInverse z z.2)

def primitiveParameterAmplitude (i : ι) (z : PrimitiveAmplitudeData ι) : ℝ :=
  z.1.1.2 i * Real.sqrt (primitiveParameterCoefficient i z)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundedPrimitiveAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform inverse and amplitude bounds from the fixed reference size and
positive coefficient margin. Inactive chart coefficients need not vary continuously. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeGroup
local instance boundedAmplitudeComplete_r201a37_1 : CompleteSpace TensorFiber := inferInstance
local instance boundedFiberFinite_r201a37_1 : FiniteDimensional ℝ TensorFiber := inferInstance
local instance boundedDualFinite_r201a37_1 : FiniteDimensional ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFinite_r201a37_1 : FiniteDimensional ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance boundedDualFamilyFinite_r201a37_1 : FiniteDimensional ℝ (ι → TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFamilyFinite_r201a37_1 : FiniteDimensional ℝ (ι → Plane →L[ℝ] ℝ) := inferInstance
local instance boundedOperatorDataFinite_r201a37_1 : FiniteDimensional ℝ (PrimitiveOperatorData ι) := inferInstance
local instance boundedDataFinite_r201a37_1 : FiniteDimensional ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance boundedDataProper_r201a37_1 : ProperSpace (PrimitiveAmplitudeData ι) :=
  FiniteDimensional.proper ℝ (PrimitiveAmplitudeData ι)
local instance boundedDataNormed_r201a37_1 : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance boundedDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance

def boundedPrimitiveReference (i : ι) (D k : ℝ) : Set (PrimitiveAmplitudeData ι) :=
  {z | ‖z‖ ≤ D ∧ primitiveDataOperator z.1 = ContinuousLinearMap.id ℝ TensorFiber ∧
      k ≤ z.1.1.1 i z.2}

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularRadiusCovectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth radius fields used for Sard have exactly the true circle
normal covectors on the new boundaries. Their regular pairs are transverse. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularNormalCovector (center base p : M) : CurvePlane :=
  phaseDerivative ((fun x => circularRadiusSquared (coordinateChart center center)
    (coordinateChart center x)) ∘ (coordinateChart base).symm) (coordinateChart base p)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveGlobalTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of a supported analytic primitive with the square of its
actual global surface phase differential. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates PhaseGeometry
local instance globalPrimitiveFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance globalPrimitiveFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance globalPrimitiveDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ConstructedPrimitiveSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the smooth amplitude and the exact localized tensor of an
actual surface primitive, retaining its precise geometric support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates PhaseGeometry
local instance constructedSupportFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance constructedSupportFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance constructedSupportDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_NonlinearPrimitiveExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
local instance phaseExpansionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseExpansionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance phaseExpansionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseExpansionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentProfiledPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual globally supported primitive from the finite recursion
and its extended polynomial mean operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
local instance independentProfiledPhaseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance independentProfiledPhaseFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance independentProfiledPhaseDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveMetricRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
local instance primitiveReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance primitiveReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveBoundaryGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A tensor restored in a chart reads back exactly where its outer cutoff is one. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
local instance boundaryGaussReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance boundaryGaussReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance boundaryGaussReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
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
local instance coefficientReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coefficientReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coefficientReadDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoordinateTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise perturbations bound the actual finite coordinate data. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance coordToleranceDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCycleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed cycle count controls all partial metrics. The estimates allow
a different exact primitive decomposition in every cycle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance cycleBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveDataC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First derivatives of finite primitive data are bounded componentwise. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteDataCovectorSpace
local instance finiteDataFiberT2_r201a37_1 : T2Space TensorFiber := inferInstance
local instance finiteDataDualT2_r201a37_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance finiteDataCovectorT2_r201a37_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]
local instance finiteDataNormed_r201a37_1 : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance finiteDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveDomainWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact coordinate window and exact support location used by the
analytic primitive theorem. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates

 def phaseWindow {V : Set SmallModes.Base} (hV : IsOpen V) : TopologicalSpace.Opens JetPolynomial.Base :=
  ⟨baseEquiv ⁻¹' V,hV.preimage baseEquiv.continuous⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SupportedPrimitivePatch
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
local instance patchFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance patchFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance patchDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_TransverseCircularRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic radii give transverse actual coordinate circles, not merely
regular levels of their auxiliary global extensions. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def circularCrossingSet (center : ι → M) (r : ι → ℝ) : Set M :=
  ⋃ a : DistinctRadiusPairs ι, circularBoundary (center a.1.1) (r a.1.1) ∩
    circularBoundary (center a.1.2) (r a.1.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CircularBoundaryArcs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact boundary portions in another phase chart have actual smooth
regular coordinate arcs, extended later only for parameter selection. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

def circularArcDomain (q p : M) (r : ℝ) : Set ℝ :=
  circularBoundaryParam p r ⁻¹' (coordinateChart q).source

def circularArc (q p : M) (r : ℝ) : ℝ → CurvePlane :=
  coordinateChart q ∘ circularBoundaryParam p r

variable [T2Space M]

def circularArcCompact (q p : M) (r R : ℝ) : Set ℝ :=
  Icc (-Real.pi) Real.pi ∩ circularBoundaryParam p r ⁻¹' circularDiskClosure q R

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OppositeIndexFrameFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite-index pair can be filled while keeping its first column fixed. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def oppositeIndexFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 ((x 0)^2-1) (x 1)

def filledOppositeIndex (χ : ℝ → ℝ) (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 ((x 0)^2-1+2*χ (x 0)*χ (x 1)) (x 1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


