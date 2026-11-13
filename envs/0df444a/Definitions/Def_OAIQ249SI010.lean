-- Prove2me | Definitions.Def_OAIQ249SI010
-- name    : OAIQ249SI010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:52:32.451742+00:00
-- url     : https://prove2.me/theorems/cd8dda23-562e-47d6-bde9-f98ba43e210f
-- title:
--   Definitions bundle OAIQ249SI010 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 251 declarations of OpenAI's Lean: 88 definitions, 8 inductive types or structures and 155 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularFamilyGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularFamilyGeometry.copiedPhases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularFamilyGeometry.withAmplitudes`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.ConvexMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.prefixMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.restrict`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.smoothFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.totalTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge.localizedImmersionRel`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.chosenTransition`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.sequence`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.basis`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.chartCoefficient`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.chartReference`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.cycleLinearParts`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.cycleWeights`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.globalPhases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.localPhases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.perturbedPhases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.cycleMetric`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothPrimitiveFamily.reindex`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.GeometricFastFamilyWithProperty`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.GridPhaseIndex`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.HasPolynomialSlowFamily`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PhaseMeanDomains`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PhasePrimitiveProfileNear`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialLinearRepresentation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialQuadraticRepresentation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ReadJetBall`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.SelectedGridPointMargins`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasMean`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialQuadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialRemainder`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialVariation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.bundleSmooth`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.normalizedPolynomialDefect` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_ModeBounds`, `Immersion_ClosedSurface_ModeDifferences`, `Immersion_ClosedSurface_ModeScaling`, `Immersion_ClosedSurface_OscillatoryModel`, `Immersion_ClosedSurface_RealModes`, `Immersion_ClosedSurface_SupportedCancellation`, `InductiveConstructions`, `Local_Corrugation`, `Local_HPrinciple`, `Loops_Basic`, `Loops_Exists`, `Loops_Surrounding`, `SurfaceImmersion_Atlas_AnchoredAtlasPhases`, `SurfaceImmersion_Atlas_BundleCutoffCoordinates`, `SurfaceImmersion_Atlas_GridCutoffSupport`, `SurfaceImmersion_Atlas_GridRestoredGeometry`, `SurfaceImmersion_Atlas_ReferenceCoordinateData`, `SurfaceImmersion_Atlas_SelectedGridGeometry`, `SurfaceImmersion_Correction_AdaptiveCorrectionSequence`, `SurfaceImmersion_Correction_AdaptiveCorrectionStep`, `SurfaceImmersion_Correction_AtlasPhaseMeanDomains`, `SurfaceImmersion_Correction_AtlasPolynomialLinearized`, `SurfaceImmersion_Correction_AtlasPolynomialLocalModel`, `SurfaceImmersion_Correction_AtlasPolynomialMetric`, `SurfaceImmersion_Correction_AtlasPrimitiveMean`, `SurfaceImmersion_Correction_BundleSmoothing`, `SurfaceImmersion_Correction_BundleSmoothingLinearity`, `SurfaceImmersion_Correction_LocalPeriodicPolynomialExpansion`, `SurfaceImmersion_Correction_PolynomialSlowFamily`, `SurfaceImmersion_Correction_SmoothPrimitiveFamily`, `SurfaceImmersion_Correction_SupportedInitialMode`, `SurfaceImmersion_Correction_SupportedModeOperators`, `SurfaceImmersion_Correction_TensorAtlasMean`, `SurfaceImmersion_Geometry_CycleCorrectedGeometry`, `SurfaceImmersion_Geometry_ExactFastFamily`, `SurfaceImmersion_Geometry_ReferencePerturbationStability`, `SurfaceImmersion_Geometry_SupportedNormalSeed`, `SurfaceImmersion_Primitive_CircularFamilyGeometry`, `SurfaceImmersion_Primitive_CircularMetricSequence`, `SurfaceImmersion_Primitive_CircularPrefixMetrics`, `SurfaceImmersion_Primitive_CircularPrimitiveFamily`, `SurfaceImmersion_Primitive_JetVelocityCoordinates`, `SurfaceImmersion_Primitive_LocalPeriodicCalculus`, `SurfaceImmersion_Primitive_LocalPeriodicExpansionStep`, `SurfaceImmersion_Primitive_LocalPeriodicFamilies`, `SurfaceImmersion_Primitive_LocalPeriodicFamilyAlgebra`, `SurfaceImmersion_Primitive_LocalPeriodicGlobalization`, `SurfaceImmersion_Primitive_LocalPeriodicMetricCoefficients`, `SurfaceImmersion_Primitive_ProfiledPhaseFastFamily`, `SurfaceImmersion_Primitive_ReferenceCircularMargins`, `SurfaceImmersion_Primitive_ReferenceCircularOperator`, `SurfaceImmersion_Primitive_SurfaceVelocityFamily`, `SurfaceImmersion_Whitney_RelativeImmersionHPrinciple`, `ToMathlib_Analysis_Calculus`, `ToMathlib_Equivariant`, `ToMathlib_ExistsOfConvex`, `ToMathlib_Topology_Misc`, `ToMathlib_Topology_Path`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundles `OAIQ249SI000`, `OAIQ249SI006` and `OAIQ249SI007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI012`, `OAIQ249SI014` and `OAIQ249SI016`; the statements `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.circular_operator_metric_stability`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference_identity`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_finite_copy_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_atlas_phases`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_nearby_cancellation_all_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_coefficientFrameRead_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_geometry_polynomial_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_geometric_metric_with_property_in_atlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_metric_with_property`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exists_reference_circular_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_surface_correction_budgets`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_jetChartMap_plane`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_atlas_free_profile`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveCoordinateData_germ`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_zeroPhase`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_half_arc_neighborhood`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_charted_free_family`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_charted_seed_bounds`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_mean_family_from_budgets`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_quadraticFamilyTensor_bound`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_free_family` and `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_uniform_charted_polynomial_mean`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.realize_sequence`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_cycles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_finite_copy_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_nearby_cancellation_all_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_nonlinear_profiles`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_remainder_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_coefficientFrameRead_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_cross_phase_exterior_control`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_geometric_metric_with_property_in_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_surface_correction_budgets`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.independent_circular_realization`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_jetChartMap_plane`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phaseAtlasAnsatz_jetProfile`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_point_crossings`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveCoordinateData_germ`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_direction`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_convex_circular_atlas`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_vectorPlaneRestore_smooth`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_cancel_crosscap_pair`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_half_arc_neighborhood`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_crosscap_connecting_arc`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_join_time_charts`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_remove_finite_quadratic_crosscaps`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_fixed_chart_nonlinear_solver`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_normalizedPolynomialMean_bounds`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_phaseCoordinatePolynomialOperator_bounds`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_supported_linear_mean_data`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_coordinate_taylor_bound`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_scaled_quadraticFamilyTensor_bound`, `OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets`, `OAI.ClosedSurfaceR4.PublishedInputs.whitneySurfaceInput` and `OAI_ClosedSurfaceR4_RealModes_polynomial_frame_envelope`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.AddTorsor.Coord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.AffineSpace.Matrix
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.Filter.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Germ
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI000
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_smul {n : ℕ} {a : Scalar} {F : Field n} {p : Base}
    (ha : DifferentiableAt ℝ a p) (hF : DifferentiableAt ℝ F p) (v : Base) :
    coordDeriv v (fun q => a q • F q) p = a p • coordDeriv v F p + coordDeriv v a p • F p := by
  have hs := (ha.hasFDerivAt.fun_smul hF.hasFDerivAt).fderiv
  simp only [coordDeriv, hs, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]



section Elimination
variable {n : ℕ}


def reconstruct (G : Field n) (ux uy : Scalar) (V : Field n) : Field n :=
  fun p => tangentLift (coordDeriv dx G p) (coordDeriv dy G p) (ux p) (uy p) + V p

def connectionTerm (G : Field n) (ux uy : Scalar) (v w : Base) (p : Base) : ℂ :=
  connectionX G v w p * ux p + connectionY G v w p * uy p


def normalElimination (G V₀ : Field n) (ux uy hyy : Scalar) : Field n := fun p =>
  V₀ p + ((coordDeriv dy uy p - connectionTerm G ux uy dy dy p - hyy p / 2) /
    (goodSecond G p ⬝ᵥ goodSecond G p)) • goodSecond G p


def reducedKx (G V₀ : Field n) (hxx hyy : Scalar) (p : Base) : ℂ :=
  hxx p / 2 + secondForm G dx dx p ⬝ᵥ V₀ p - secondRatio G dx dx p * hyy p / 2

def reducedKy (G V₀ : Field n) (hxy hyy : Scalar) (p : Base) : ℂ :=
  hxy p + 2 * (secondForm G dx dy p ⬝ᵥ V₀ p) - secondRatio G dx dy p * hyy p



end Elimination

section Parametrix
variable {n : ℕ}


def firstCovectorX (τ : ℝ) (G V₀ : Field n) (hxx hyy : Scalar) : Scalar :=
  fun p => ((τ : ℂ) / Complex.I) * reducedKx G V₀ hxx hyy p

def firstCovectorY (τ : ℝ) (G V₀ : Field n) (hxy hyy : Scalar) : Scalar :=
  fun p => ((τ : ℂ) / Complex.I) * reducedKy G V₀ hxy hyy p

def firstParametrix (τ : ℝ) (G V₀ : Field n) (hxx hxy hyy : Scalar) : Field n :=
  let ux := firstCovectorX τ G V₀ hxx hyy
  let uy := firstCovectorY τ G V₀ hxy hyy
  reconstruct G ux uy (normalElimination G V₀ ux uy hyy)

end Parametrix

section SmoothFormulas
variable {n : ℕ}

lemma contDiffAt_cdiv {a b : Scalar} {p : Base}
    (ha : ContDiffAt ℝ ∞ a p) (hb : ContDiffAt ℝ ∞ b p) (hne : b p ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => a q / b q) p := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.fun_inv hne)

lemma contDiffAt_liftX {X Y : Field n} {ux uy : Scalar} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftX (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hY hY).mul hx).sub ((contDiffAt_dot hX hY).mul hy))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_liftY {X Y : Field n} {ux uy : Scalar} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftY (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hX hX).mul hy).sub ((contDiffAt_dot hX hY).mul hx))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_tangentLift {X Y : Field n} {ux uy : Scalar} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => tangentLift (X q) (Y q) (ux q) (uy q)) p :=
  ((contDiffAt_liftX hX hY hx hy hD).smul hX).add ((contDiffAt_liftY hX hY hx hy hD).smul hY)

lemma contDiffAt_normalPart {X Y W : Field n} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) (hW : ContDiffAt ℝ ∞ W p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => normalPart (X q) (Y q) (W q)) p :=
  hW.sub (contDiffAt_tangentLift hX hY (contDiffAt_dot hX hW) (contDiffAt_dot hY hW) hD)

lemma contDiffAt_secondForm {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (secondForm G v w) p :=
  contDiffAt_normalPart (contDiffAt_coordDeriv hG dx) (contDiffAt_coordDeriv hG dy)
    (contDiffAt_coordDeriv (contDiffAt_coordDeriv hG w) v) hD

lemma contDiffAt_connectionX {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (connectionX G v w) p := by
  have hX := contDiffAt_coordDeriv hG dx
  have hY := contDiffAt_coordDeriv hG dy
  have hSec := contDiffAt_coordDeriv (contDiffAt_coordDeriv hG w) v
  exact contDiffAt_liftX hX hY (contDiffAt_dot hX hSec) (contDiffAt_dot hY hSec) hD

lemma contDiffAt_connectionY {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (connectionY G v w) p := by
  have hX := contDiffAt_coordDeriv hG dx
  have hY := contDiffAt_coordDeriv hG dy
  have hSec := contDiffAt_coordDeriv (contDiffAt_coordDeriv hG w) v
  exact contDiffAt_liftY hX hY (contDiffAt_dot hX hSec) (contDiffAt_dot hY hSec) hD

lemma contDiffAt_connectionTerm {G : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (connectionTerm G ux uy v w) p :=
  ((contDiffAt_connectionX hG hD v w).mul hx).add ((contDiffAt_connectionY hG hD v w).mul hy)

lemma contDiffAt_secondRatio {G : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (v w : Base) :
    ContDiffAt ℝ ∞ (secondRatio G v w) p :=
  contDiffAt_cdiv (contDiffAt_dot (contDiffAt_secondForm hG hD v w)
    (contDiffAt_secondForm hG hD dy dy))
    (contDiffAt_dot (contDiffAt_secondForm hG hD dy dy) (contDiffAt_secondForm hG hD dy dy)) hb

lemma contDiffAt_reconstruct {G V : Field n} {ux uy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0) :
    ContDiffAt ℝ ∞ (reconstruct G ux uy V) p :=
  (contDiffAt_tangentLift (contDiffAt_coordDeriv hG dx) (contDiffAt_coordDeriv hG dy) hx hy hD).add hV

lemma contDiffAt_normalElimination {G V : Field n} {ux uy hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p) (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (normalElimination G V ux uy hyy) p := by
  have hB := contDiffAt_secondForm hG hD dy dy
  exact hV.add ((contDiffAt_cdiv
    (((contDiffAt_coordDeriv hy dy).sub (contDiffAt_connectionTerm hG hx hy hD dy dy)).sub
      (hyy'.div_const 2)) (contDiffAt_dot hB hB) hb).smul hB)

lemma contDiffAt_reducedKx {G V : Field n} {hxx hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hxx' : ContDiffAt ℝ ∞ hxx p) (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedKx G V hxx hyy) p :=
  ((hxx'.div_const 2).add (contDiffAt_dot (contDiffAt_secondForm hG hD dx dx) hV)).sub
    (((contDiffAt_secondRatio hG hD hb dx dx).mul hyy').div_const 2)

lemma contDiffAt_reducedKy {G V : Field n} {hxy hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hxy' : ContDiffAt ℝ ∞ hxy p) (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (reducedKy G V hxy hyy) p :=
  (hxy'.add (contDiffAt_const.mul (contDiffAt_dot (contDiffAt_secondForm hG hD dx dy) hV))).sub
    ((contDiffAt_secondRatio hG hD hb dx dy).mul hyy')

lemma contDiffAt_firstParametrix (τ : ℝ) {G V : Field n} {hxx hxy hyy : Scalar} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p)
    (hxx' : ContDiffAt ℝ ∞ hxx p) (hxy' : ContDiffAt ℝ ∞ hxy p)
    (hyy' : ContDiffAt ℝ ∞ hyy p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (firstParametrix τ G V hxx hxy hyy) p := by
  have hx : ContDiffAt ℝ ∞ (firstCovectorX τ G V hxx hyy) p :=
    contDiffAt_const.mul (contDiffAt_reducedKx hG hV hxx' hyy' hD hb)
  have hy : ContDiffAt ℝ ∞ (firstCovectorY τ G V hxy hyy) p :=
    contDiffAt_const.mul (contDiffAt_reducedKy hG hV hxy' hyy' hD hb)
  exact contDiffAt_reconstruct hG
    (contDiffAt_normalElimination hG hV hx hy hyy' hD hb) hx hy hD

end SmoothFormulas

section LinearStructure
variable {n : ℕ}

lemma partial_const_mul {a : ℂ} {f : Scalar} {p : Base}
    (hf : DifferentiableAt ℝ f p) (v : Base) :
    coordDeriv v (fun q => a * f q) p = a * coordDeriv v f p := by
  have hh := (hf.hasFDerivAt.const_mul a).fderiv
  simp only [coordDeriv, hh, smul_apply, smul_eq_mul]

lemma connectionTerm_mul (G : Field n) (ux uy : Scalar) (p v w : Base) (a : ℂ) :
    connectionTerm G (fun q => a * ux q) (fun q => a * uy q) v w p =
      a * connectionTerm G ux uy v w p := by
  unfold connectionTerm
  ring

def tensorOf (hxx hxy hyy : Scalar) : Tensor := fun p => ![hxx p, hxy p, hyy p]

def component (h : Tensor) (i : Fin 3) : Scalar := fun p => h p i

def conjugatedD (τ : ℝ) (G Z : Field n) : Tensor :=
  tensorOf (conjugatedMetric τ G Z dx dx) (conjugatedMetric τ G Z dx dy)
    (conjugatedMetric τ G Z dy dy)

def initialAmplitude (τ : ℝ) (G V : Field n) (h : Tensor) : Field n :=
  firstParametrix τ G V (component h 0) (component h 1) (component h 2)

def zeroParametrix (τ : ℝ) (G : Field n) (h : Tensor) : Field n :=
  initialAmplitude τ G (fun _ => 0) h

def residual (τ : ℝ) (G : Field n) (h : Tensor) (Z : Field n) : Tensor :=
  fun p => conjugatedD τ G Z p - h p



def modeApprox (τ : ℝ) (G V : Field n) (h : Tensor) : ℕ → Field n
  | 0 => initialAmplitude τ G V h
  | j + 1 => fun p => modeApprox τ G V h j p -
      zeroParametrix τ G (residual τ G h (modeApprox τ G V h j)) p

lemma contDiffAt_initialAmplitude (τ : ℝ) {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (initialAmplitude τ G V h) p :=
  contDiffAt_firstParametrix τ hG hV (contDiffAt_pi.mp hh 0) (contDiffAt_pi.mp hh 1)
    (contDiffAt_pi.mp hh 2) hD hb

lemma contDiffAt_zeroParametrix (τ : ℝ) {G : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    ContDiffAt ℝ ∞ (zeroParametrix τ G h) p :=
  contDiffAt_initialAmplitude τ hG contDiffAt_const hh hD hb

lemma contDiffAt_conjugatedD (τ : ℝ) {G Z : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hZ : ContDiffAt ℝ ∞ Z p) :
    ContDiffAt ℝ ∞ (conjugatedD τ G Z) p := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_conjugatedMetric τ hG hZ dx dx
  · exact contDiffAt_conjugatedMetric τ hG hZ dx dy
  · exact contDiffAt_conjugatedMetric τ hG hZ dy dy

lemma contDiffAt_residual (τ : ℝ) {G Z : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hZ : ContDiffAt ℝ ∞ Z p) (hh : ContDiffAt ℝ ∞ h p) :
    ContDiffAt ℝ ∞ (residual τ G h Z) p :=
  (contDiffAt_conjugatedD τ hG hZ).sub hh

lemma contDiffAt_modeApprox (τ : ℝ) {G V : Field n} {h : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hh : ContDiffAt ℝ ∞ h p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) (j : ℕ) :
    ContDiffAt ℝ ∞ (modeApprox τ G V h j) p := by
  induction j with
  | zero => exact contDiffAt_initialAmplitude τ hG hV hh hD hb
  | succ j ih => exact ih.sub (contDiffAt_zeroParametrix τ hG (contDiffAt_residual τ hG ih hh) hD hb)

lemma conjugatedD_sub (τ : ℝ) (G : Field n) {Z W : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) :
    conjugatedD τ G (fun q => Z q - W q) p = conjugatedD τ G Z p - conjugatedD τ G W p := by
  ext i
  fin_cases i <;> simp [conjugatedD, tensorOf, conjugatedMetric_sub τ G hZ hW]


lemma initialAmplitude_congr (τ : ℝ) (G : Field n) {V W : Field n} {h k : Tensor} {p : Base}
    (hv : V =ᶠ[nhds p] W) (hh : h =ᶠ[nhds p] k) :
    initialAmplitude τ G V h p = initialAmplitude τ G W k p := by
  have hx : firstCovectorX τ G V (component h 0) (component h 2) =ᶠ[nhds p]
      firstCovectorX τ G W (component k 0) (component k 2) := by
    filter_upwards [hv, hh] with q hvq hhq
    simp only [firstCovectorX, reducedKx, component, hvq, hhq]
  have hy : firstCovectorY τ G V (component h 1) (component h 2) =ᶠ[nhds p]
      firstCovectorY τ G W (component k 1) (component k 2) := by
    filter_upwards [hv, hh] with q hvq hhq
    simp only [firstCovectorY, reducedKy, component, hvq, hhq]
  unfold initialAmplitude firstParametrix reconstruct normalElimination
  simp only [coordDeriv, hx.self_of_nhds, hy.self_of_nhds, hy.fderiv_eq,
    connectionTerm, hv.self_of_nhds, component, hh.self_of_nhds]

lemma initialAmplitude_zero (τ : ℝ) (G : Field n) :
    initialAmplitude τ G (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  unfold initialAmplitude firstParametrix reconstruct normalElimination
    firstCovectorX firstCovectorY reducedKx reducedKy connectionTerm
    tangentLift liftX liftY component coordDeriv
  simp

lemma conjugatedD_congr (τ : ℝ) (G : Field n) {Z W : Field n} {p : Base}
    (he : Z =ᶠ[nhds p] W) : conjugatedD τ G Z p = conjugatedD τ G W p := by
  unfold conjugatedD tensorOf conjugatedMetric linearizedMetric covector
  simp only [coordDeriv, he.fderiv_eq, he.self_of_nhds]

lemma conjugatedD_zero (τ : ℝ) (G : Field n) :
    conjugatedD τ G (fun _ => 0) = fun _ => 0 := by
  unfold conjugatedD tensorOf conjugatedMetric linearizedMetric covector coordDeriv
  simp
  ext p i
  fin_cases i <;> simp




theorem modeApprox_vanishes (τ : ℝ) (G V : Field n) (h : Tensor)
    {U : Set Base} (hU : IsOpen U) (hV : ∀ p ∈ U, V p = 0) (hh : ∀ p ∈ U, h p = 0)
    (j : ℕ) : ∀ p ∈ U, modeApprox τ G V h j p = 0 := by
  have hVe (p : Base) (hp : p ∈ U) : V =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hV q hq
  have hhe (p : Base) (hp : p ∈ U) : h =ᶠ[nhds p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hh q hq
  induction j with
  | zero =>
    intro p hp
    change initialAmplitude τ G V h p = 0
    rw [initialAmplitude_congr τ G (hVe p hp) (hhe p hp), initialAmplitude_zero]
  | succ j ih =>
    have hr : ∀ p ∈ U, residual τ G h (modeApprox τ G V h j) p = 0 := by
      intro p hp
      have he : modeApprox τ G V h j =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih q hq
      rw [residual, conjugatedD_congr τ G he, conjugatedD_zero, hh p hp, sub_self]
    intro p hp
    have hre : residual τ G h (modeApprox τ G V h j) =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hr q hq
    change modeApprox τ G V h j p - zeroParametrix τ G (residual τ G h (modeApprox τ G V h j)) p = 0
    rw [ih p hp, zeroParametrix,
      initialAmplitude_congr τ G (Filter.Eventually.of_forall fun _ => rfl) hre, initialAmplitude_zero, sub_self]

end LinearStructure

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

section Quantitative
variable {n : ℕ}



lemma ModeDomain.secondForm {G : Field n} {U : Set Base} (h : ModeDomain G U) (v w : Base) :
    ContDiffOn ℝ ∞ (secondForm G v w) U := by
  intro p hp
  exact (contDiffAt_secondForm (h.smoothAt hp) (h.determinant p hp) v w).contDiffWithinAt



def amplitudeCorrection (G V : Field n) (f : Tensor) : Field n :=
  let kx := reducedKx G V (component f 0) (component f 2)
  let ky := reducedKy G V (component f 1) (component f 2)
  fun p => kx p • tangentDualX G p + ky p • tangentDualY G p +
    (coordDeriv dy ky p - connectionTerm G kx ky dy dy p) • normalDual G p

lemma initialAmplitude_expansion (τ : ℝ) {G V : Field n} {f : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hf : ContDiffAt ℝ ∞ f p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G V f p = V p - (f p 2 / 2) • normalDual G p +
      ((τ : ℂ) / Complex.I) • amplitudeCorrection G V f p := by
  have hy := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hf 1) (contDiffAt_pi.mp hf 2) hD hb
  unfold initialAmplitude firstParametrix firstCovectorX firstCovectorY reconstruct normalElimination
  simp only [component]
  rw [partial_const_mul (a := (τ : ℂ) / Complex.I)
    (f := reducedKy G V (component f 1) (component f 2))
    (hy.differentiableAt (by simp)) dy, connectionTerm_mul, tangentLift_mul, tangentLift_columns]
  ext i
  simp only [amplitudeCorrection, normalDual, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

lemma contDiffOn_initialAmplitude (τ : ℝ) {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (initialAmplitude τ G V f) U := by
  intro p hp
  exact (contDiffAt_initialAmplitude τ (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp)).contDiffWithinAt

lemma contDiffOn_modeApprox (τ : ℝ) {G V : Field n} {U : Set Base} (h : ModeDomain G U)
    {f : Tensor} (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    ContDiffOn ℝ ∞ (modeApprox τ G V f q) U := by
  intro p hp
  exact (contDiffAt_modeApprox τ (h.smoothAt hp)
    ((hV p hp).contDiffAt (h.isOpen.mem_nhds hp))
    ((hf p hp).contDiffAt (h.isOpen.mem_nhds hp))
    (h.determinant p hp) (h.good p hp) q).contDiffWithinAt

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeDifferences
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma component_sub (f g : Tensor) (i : Fin 3) :
    component (fun p => f p - g p) i = fun p => component f i p - component g i p := rfl

lemma reducedKx_sub {n : ℕ} (G V W : Field n) (a b c d : Scalar) :
    reducedKx G (fun p => V p - W p) (fun p => a p - c p) (fun p => b p - d p) =
      fun p => reducedKx G V a b p - reducedKx G W c d p := by
  funext p
  simp only [reducedKx, dotProduct_sub]
  ring

lemma reducedKy_sub {n : ℕ} (G V W : Field n) (a b c d : Scalar) :
    reducedKy G (fun p => V p - W p) (fun p => a p - c p) (fun p => b p - d p) =
      fun p => reducedKy G V a b p - reducedKy G W c d p := by
  funext p
  simp only [reducedKy, dotProduct_sub]
  ring

lemma connectionTerm_sub {n : ℕ} (G : Field n) (a b c d : Scalar) (p v w : Base) :
    connectionTerm G (fun q => a q - c q) (fun q => b q - d q) v w p =
      connectionTerm G a b v w p - connectionTerm G c d v w p := by
  unfold connectionTerm
  ring

lemma amplitudeCorrection_sub {n : ℕ} {G V W : Field n} {f g : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hW : ContDiffAt ℝ ∞ W p)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    amplitudeCorrection G (fun q => V q - W q) (fun q => f q - g q) p =
      amplitudeCorrection G V f p - amplitudeCorrection G W g p := by
  have hyf := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hf 1) (contDiffAt_pi.mp hf 2) hD hb
  have hyg := contDiffAt_reducedKy hG hW (contDiffAt_pi.mp hg 1) (contDiffAt_pi.mp hg 2) hD hb
  simp only [amplitudeCorrection, component_sub]
  rw [reducedKx_sub, reducedKy_sub]
  unfold component
  rw [partial_sub (hyf.differentiableAt (by simp)) (hyg.differentiableAt (by simp)), connectionTerm_sub]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma initialAmplitude_sub {n : ℕ} (τ : ℝ) {G V W : Field n} {f g : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hW : ContDiffAt ℝ ∞ W p)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G (fun q => V q - W q) (fun q => f q - g q) p =
      initialAmplitude τ G V f p - initialAmplitude τ G W g p := by
  rw [initialAmplitude_expansion τ hG (hV.sub hW) (hf.sub hg) hD hb,
    initialAmplitude_expansion τ hG hV hf hD hb,
    initialAmplitude_expansion τ hG hW hg hD hb,
    amplitudeCorrection_sub hG hV hW hf hg hD hb]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma zeroParametrix_sub {n : ℕ} (τ : ℝ) {G : Field n} {f g : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    zeroParametrix τ G (fun q => f q - g q) p =
      zeroParametrix τ G f p - zeroParametrix τ G g p := by
  simpa only [zeroParametrix, sub_self] using
    initialAmplitude_sub τ hG (contDiffAt_const (c := (0 : Ambient n)))
      (contDiffAt_const (c := (0 : Ambient n))) hf hg hD hb




theorem modeApprox_sub {n : ℕ} (τ : ℝ) {G V W : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U)
    {f g : Tensor} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (q : ℕ) :
    EqOn (modeApprox τ G (fun p => V p - W p) (fun p => f p - g p) q)
      (fun p => modeApprox τ G V f q p - modeApprox τ G W g q p) U := by
  have atU {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {a : Base → E} (ha : ContDiffOn ℝ ∞ a U) {p : Base} (hp : p ∈ U) :
      ContDiffAt ℝ ∞ a p := (ha p hp).contDiffAt (h.isOpen.mem_nhds hp)
  induction q with
  | zero =>
    intro p hp
    exact initialAmplitude_sub τ hG.contDiffAt (atU hV hp) (atU hW hp)
      (atU hf hp) (atU hg hp) (h.determinant p hp) (h.good p hp)
  | succ q ih =>
    have hZ := contDiffOn_modeApprox τ h hV hf q
    have hY := contDiffOn_modeApprox τ h hW hg q
    have he : EqOn
        (residual τ G (fun p => f p - g p)
          (modeApprox τ G (fun p => V p - W p) (fun p => f p - g p) q))
        (fun p => residual τ G f (modeApprox τ G V f q) p -
          residual τ G g (modeApprox τ G W g q) p) U := by
      intro p hp
      have hei : modeApprox τ G (fun p => V p - W p) (fun p => f p - g p) q =ᶠ[nhds p]
          (fun p => modeApprox τ G V f q p - modeApprox τ G W g q p) :=
        Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => ih hz)
      unfold residual
      rw [conjugatedD_congr τ G hei,
        conjugatedD_sub τ G ((atU hZ hp).differentiableAt (by simp))
          ((atU hY hp).differentiableAt (by simp))]
      ext i
      simp only [Pi.sub_apply]
      ring
    intro p hp
    have hee := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => he hz)
    change modeApprox τ G _ _ q p - initialAmplitude τ G (fun _ => 0) _ p = _
    rw [ih hp, initialAmplitude_congr τ G (Filter.EventuallyEq.refl _ _) hee]
    have hs := zeroParametrix_sub τ hG.contDiffAt
      (contDiffAt_residual τ hG.contDiffAt (atU hZ hp) (atU hf hp))
      (contDiffAt_residual τ hG.contDiffAt (atU hY hp) (atU hg hp))
      (h.determinant p hp) (h.good p hp)
    change initialAmplitude τ G (fun _ => 0) _ p = _ at hs
    rw [hs]
    simp only [modeApprox]
    ext i
    simp only [Pi.sub_apply]
    ring

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma contDiffOn_realSecond {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) : ContDiffOn ℝ ∞ (realSecond F) U := by
  have hb := (h.complexDomain hF).secondForm dy dy
  apply contDiffOn_pi.mpr
  intro i
  have hi := Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hb i)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact congrArg Complex.re (congrFun (complexify_realSecond hF p) i)

lemma contDiffOn_freeNormal {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) : ContDiffOn ℝ ∞ (freeNormal F) U := by
  intro p hp
  have hn := realNormalPart_perp (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dy (coordDeriv dy F) p) (h.determinant p hp)
  have hb := ((contDiffOn_realSecond hF h) p hp).contDiffAt (h.isOpen.mem_nhds hp)
  exact (NormalFrame.contDiffAt_unitPerp (contDiff_real_coordDeriv hF dx).contDiffAt
    (contDiff_real_coordDeriv hF dy).contDiffAt hb (h.determinant p hp) (h.good p hp)
    hn.1 hn.2).contDiffWithinAt


lemma freeSeed_isFree {F : RField 4} {U : Set Base} (hF : ContDiff ℝ ∞ F)
    (h : RealModeDomain F U) (δ τ : ℝ) {b : Base → ℝ} (hb : ContDiffOn ℝ ∞ b U) :
    FreeCoefficient (fun p => complexify (F p)) U (freeSeed δ τ b F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha := Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_const (c := Real.sqrt 2 * δ * τ)).mul hb)
    have hn := (complexifyCLM 4).contDiff.comp_contDiffOn (contDiffOn_freeNormal hF h)
    exact ha.smul hn
  · intro p hp
    rw [coordDeriv_complexify (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
    simp only [freeSeed, dotProduct_smul, smul_eq_mul, complexify_dot, (freeNormal_perp F p).1,
      Complex.ofReal_zero, mul_zero]
  · intro p hp
    rw [coordDeriv_complexify (hF.differentiable (by simp) p)]
    simp only [freeSeed, dotProduct_smul, smul_eq_mul, complexify_dot, (freeNormal_perp F p).2.1,
      Complex.ofReal_zero, mul_zero]
  · intro p hp
    rw [← complexify_realSecond hF]
    simp only [freeSeed, dotProduct_smul, smul_eq_mul, complexify_dot, (freeNormal_perp F p).2.2,
      Complex.ofReal_zero, mul_zero]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SupportedCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open Set

lemma modeApprox_tsupport {n : ℕ} (τ : ℝ) (G V : Field n) (f : Tensor) (q : ℕ) :
    tsupport (modeApprox τ G V f q) ⊆ tsupport V ∪ tsupport f := by
  apply closure_minimal _ ((isClosed_tsupport V).union (isClosed_tsupport f))
  intro p hp
  by_contra hn
  let W := (tsupport V ∪ tsupport f)ᶜ
  have hW : IsOpen W := ((isClosed_tsupport V).union (isClosed_tsupport f)).isOpen_compl
  have hzV : ∀ x ∈ W, V x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inl hh))
  have hzf : ∀ x ∈ W, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inr hh))
  exact hp (modeApprox_vanishes τ G V f hW hzV hzf q p hn)

lemma forcedMode_tsupport {n : ℕ} (τ : ℝ) (G : Field n) (f : Tensor) (q : ℕ) :
    tsupport (modeApprox τ G (fun _ => 0) f q) ⊆ tsupport f := by
  simpa only [← Pi.zero_def, tsupport_zero, empty_union] using modeApprox_tsupport τ G (fun _ => 0) f q

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeScaling
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_const_smul {n : ℕ} (a : ℂ) {Z : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (v : Base) :
    coordDeriv v (fun q => a • Z q) p = a • coordDeriv v Z p := by
  rw [partial_smul (differentiableAt_const a) hZ]
  simp [coordDeriv]

lemma reducedKx_smul {n : ℕ} (a : ℂ) (G V : Field n) (f g : Scalar) :
    reducedKx G (fun p => a • V p) (fun p => a * f p) (fun p => a * g p) =
      fun p => a * reducedKx G V f g p := by
  funext p
  simp only [reducedKx, dotProduct_smul, smul_eq_mul]
  ring

lemma reducedKy_smul {n : ℕ} (a : ℂ) (G V : Field n) (f g : Scalar) :
    reducedKy G (fun p => a • V p) (fun p => a * f p) (fun p => a * g p) =
      fun p => a * reducedKy G V f g p := by
  funext p
  simp only [reducedKy, dotProduct_smul, smul_eq_mul]
  ring

lemma component_const_smul (a : ℂ) (f : Tensor) (i : Fin 3) :
    component (fun p => a • f p) i = fun p => a * component f i p := rfl

lemma amplitudeCorrection_smul {n : ℕ} (a : ℂ) {G V : Field n} {f : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hf : ContDiffAt ℝ ∞ f p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    amplitudeCorrection G (fun q => a • V q) (fun q => a • f q) p =
      a • amplitudeCorrection G V f p := by
  have hy := contDiffAt_reducedKy hG hV (contDiffAt_pi.mp hf 1) (contDiffAt_pi.mp hf 2) hD hb
  change ContDiffAt ℝ ∞ (reducedKy G V (component f 1) (component f 2)) p at hy
  simp only [amplitudeCorrection, component_const_smul]
  rw [reducedKx_smul, reducedKy_smul, partial_const_mul (a := a) (hy.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) dy,
    connectionTerm_mul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma initialAmplitude_smul {n : ℕ} (τ : ℝ) (a : ℂ) {G V : Field n} {f : Tensor} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hV : ContDiffAt ℝ ∞ V p) (hf : ContDiffAt ℝ ∞ f p)
    (hD : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0)
    (hb : goodSecond G p ⬝ᵥ goodSecond G p ≠ 0) :
    initialAmplitude τ G (fun q => a • V q) (fun q => a • f q) p =
      a • initialAmplitude τ G V f p := by
  rw [initialAmplitude_expansion τ hG (hV.const_smul a) (hf.const_smul a) hD hb,
    initialAmplitude_expansion τ hG hV hf hD hb,
    amplitudeCorrection_smul a hG hV hf hD hb]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma conjugatedMetric_smul {n : ℕ} (τ : ℝ) (a : ℂ) (G : Field n) {Z : Field n}
    {p : Base} (hZ : DifferentiableAt ℝ Z p) (v w : Base) :
    conjugatedMetric τ G (fun q => a • Z q) v w p = a * conjugatedMetric τ G Z v w p := by
  simp only [conjugatedMetric, linearizedMetric, partial_const_smul a hZ,
    covector, dotProduct_smul, smul_eq_mul]
  ring

lemma conjugatedD_smul {n : ℕ} (τ : ℝ) (a : ℂ) (G : Field n) {Z : Field n}
    {p : Base} (hZ : DifferentiableAt ℝ Z p) :
    conjugatedD τ G (fun q => a • Z q) p = a • conjugatedD τ G Z p := by
  ext i
  fin_cases i <;> simp [conjugatedD, tensorOf, conjugatedMetric_smul τ a G hZ]



theorem modeApprox_smul {n : ℕ} (τ : ℝ) (a : ℂ) {G V : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U) (hV : ContDiffOn ℝ ∞ V U)
    {f : Tensor} (hf : ContDiffOn ℝ ∞ f U) (q : ℕ) :
    EqOn (modeApprox τ G (fun p => a • V p) (fun p => a • f p) q)
      (fun p => a • modeApprox τ G V f q p) U := by
  have atU {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {b : Base → E} (hb : ContDiffOn ℝ ∞ b U) {p : Base} (hp : p ∈ U) :
      ContDiffAt ℝ ∞ b p := (hb p hp).contDiffAt (h.isOpen.mem_nhds hp)
  induction q with
  | zero =>
    intro p hp
    exact initialAmplitude_smul τ a hG.contDiffAt (atU hV hp) (atU hf hp)
      (h.determinant p hp) (h.good p hp)
  | succ q ih =>
    have hZ := contDiffOn_modeApprox τ h hV hf q
    have he : EqOn
        (residual τ G (fun p => a • f p)
          (modeApprox τ G (fun p => a • V p) (fun p => a • f p) q))
        (fun p => a • residual τ G f (modeApprox τ G V f q) p) U := by
      intro p hp
      have hei := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => ih hz)
      unfold residual
      rw [conjugatedD_congr τ G hei,
        conjugatedD_smul τ a G ((atU hZ hp).differentiableAt (by simp))]
      exact (smul_sub a _ _).symm
    intro p hp
    have hee := Filter.Eventually.mono (h.isOpen.mem_nhds hp) (fun z hz => he hz)
    change modeApprox τ G _ _ q p - initialAmplitude τ G (fun _ => 0) _ p = _
    rw [ih hp, initialAmplitude_congr τ G (Filter.EventuallyEq.refl _ _) hee]
    have hh := initialAmplitude_smul τ a hG.contDiffAt (contDiffAt_const (c := (0 : Ambient n)))
      (contDiffAt_residual τ hG.contDiffAt (atU hZ hp) (atU hf hp))
      (h.determinant p hp) (h.good p hp)
    simp only [smul_zero] at hh
    rw [hh]
    simp only [modeApprox, zeroParametrix, smul_sub]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Topology_Misc
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self _root_.linearReparam_projI
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter TopologicalSpace
open scoped unitInterval Topology uniformity

section Fract

open Int

/- properties of the (dis)continuity of `Int.fract` on `ℝ`.
To be PRed to Topology.Algebra.FloorRing
-/

theorem loc_constant_floor {x : ℝ} (h : x ∉ range (Int.cast : ℤ → ℝ)) : floor =ᶠ[𝓝 x] fun _ ↦ ⌊x⌋ := by
  filter_upwards [Ioo_floor_mem_nhds h]
  intro y hy
  rw [floor_eq_on_Ico]
  exact mem_Ico_of_Ioo hy

theorem fract_eventuallyEq {x : ℝ} (h : fract x ≠ 0) : fract =ᶠ[𝓝 x] fun x' ↦ x' - floor x := by
  rw [Int.fract_ne_zero_iff] at h
  exact EventuallyEq.rfl.sub ((loc_constant_floor h).fun_comp _)

theorem fract_preimage_mem_nhds {s : Set ℝ} {x : ℝ} (h1 : s ∈ 𝓝 (fract x))
    (h2 : fract x = 0 → s ∈ 𝓝 (1 : ℝ)) : fract ⁻¹' s ∈ 𝓝 x := by
  by_cases hx : fract x = 0
  · obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp h1
    obtain ⟨v, hvs, hv, h1v⟩ := mem_nhds_iff.mp (h2 hx)
    rw [mem_nhds_iff]
    exact ⟨fract ⁻¹' (u ∪ v), preimage_mono (union_subset hus hvs),
      (hu.union hv).preimage_fract fun _ ↦ subset_union_right h1v, subset_union_left hxu⟩
  · exact (continuousAt_fract (sub_ne_zero.1 hx)).preimage_mem_nhds h1

end Fract

section

-- TODO: move to Mathlib.Topology.Constructions
-- needs classical
variable {α β γ δ ι : Type*} [TopologicalSpace α] [TopologicalSpace β] {x : α}
open scoped Classical in
theorem isOpen_slice_of_isOpen_over {Ω : Set (α × β)} {x₀ : α}
    (hΩ_op : ∃ U ∈ 𝓝 x₀, IsOpen (Ω ∩ Prod.fst ⁻¹' U)) : IsOpen (Prod.mk x₀ ⁻¹' Ω) := by
  rcases hΩ_op with ⟨U, hU, hU_op⟩; convert hU_op.preimage (Continuous.prodMk_right x₀) using 1
  simp_rw [preimage_inter, preimage_preimage, preimage_const, mem_of_mem_nhds hU, ite_eq_left,
    inter_univ]

end

section projI

variable {α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {x c : α}

theorem projI_le_iff : projI x ≤ c ↔ 0 ≤ c ∧ (1 ≤ c ∨ x ≤ c) := by
  simp_rw [projI_def, max_le_iff, min_le_iff]

theorem min_projI (h2 : 0 ≤ c) : min c (projI x) = projI (min c x) := by
  obtain (h3 | h3) := le_total c x <;> simp [h2, h3, projI_le_iff, projI_eq_min.mpr]
  simp [projI_eq_min.mpr, h2.trans h3, min_left_comm c, h3]

-- about Path.truncate
theorem truncate_projI_right {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ)
    (s : I) : γ.truncate t₀ (projI t₁) s = γ.truncate t₀ t₁ s := by
  simp_rw [Path.truncate, Path.coe_mk_mk, Path.extend, IccExtend, Function.comp_def]
  rw [min_projI (s.prop.1.trans <| le_max_left _ _), ContinuousMap.coe_mk, projIcc_projI]

end projI

section

open Metric

attribute [fun_prop] continuous_infDist_pt

end

open Subtype
end
end
end

section
-- module Solutions.OAIQ249_SI.InductiveConstructions
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

-- set_option trace.filter_inst_type true

open Set Filter Function
open scoped Topology unitInterval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` and the local to global
inductive homotopy construction in a way that uncouples the general
topological argument from the things specific to loops or homotopies of jet sections.

First there is a lemma `inductive_construction` which abstracts the locally ultimately constant
arguments, assuming we work with a fixed covering. It builds on
`LocallyFinite.exists_forall_eventually_of_indexType`.

From `inductive_construction` alone we deduce `inductive_htpy_construction` which builds a homotopy
in a similar context. This is meant to be used to go from Chapter 2 to Chapter 3.

Combining `inductive_construction` with an argument using local existence and exhaustions, we
get `inductive_construction_of_loc` building a function from local existence and patching
assumptions. It also has a version `relative_inductive_construction_of_loc` which does this
relative to a closed set. This is used for `exists_surrounding_loops`.

This file also contains supporting lemmas about `IndexType`. A short term goal will be to
get rid of the `indexing` abstraction and do everything in terms of `IndexType`, unless
`indexing` makes those supporting lemmas really cleaner to prove.
-/


section inductive_construction

@[inherit_doc] local notation "𝓘" => IndexType

theorem inductive_construction {X Y : Type*} [TopologicalSpace X] {N : ℕ} {U : IndexType N → Set X}
    (P₀ : ∀ x : X, Germ (𝓝 x) Y → Prop) (P₁ : ∀ _i : IndexType N, ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : IndexType N → (X → Y) → Prop) (U_fin : LocallyFinite U)
    (init : ∃ f : X → Y, (∀ x, P₀ x f) ∧ P₂ 0 f)
    (ind : ∀ (i : IndexType N) (f : X → Y), (∀ x, P₀ x f) → P₂ i f → (∀ j < i, ∀ x, P₁ j x f) →
      ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (¬IsMax i → P₂ i.succ f') ∧ (∀ j ≤ i, ∀ x, P₁ j x f') ∧
        ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ j, ∀ x, P₁ j x f := by
  let P : 𝓘 N → (X → Y) → Prop := fun n f ↦
    (∀ x, P₀ x f) ∧ (¬IsMax n → P₂ n.succ f) ∧ ∀ j ≤ n, ∀ x, P₁ j x f
  let Q : 𝓘 N → (X → Y) → (X → Y) → Prop := fun n f f' ↦ ∀ x ∉ (U n.succ), f' x = f x
  obtain ⟨f, hf⟩ : ∃ f : 𝓘 N → X → Y, ∀ n, P n (f n) ∧ (¬IsMax n → Q n (f n) (f n.succ)) := by
    apply IndexType.exists_by_induction
    · rcases init with ⟨f₀, h₀f₀, h₁f₀⟩
      rcases ind 0 f₀ h₀f₀ h₁f₀ (by simp [IndexType.not_lt_zero]) with ⟨f', h₀f', h₂f', h₁f', -⟩
      exact ⟨f', h₀f', h₂f', h₁f'⟩
    · rintro n f ⟨h₀f, h₂f, h₁f⟩ hn
      rcases ind _ f h₀f (h₂f hn) fun j hj ↦ h₁f _ <| j.le_of_lt_succ hj with
        ⟨f', h₀f', h₂f', h₁f', hf'⟩
      exact ⟨f', ⟨h₀f', h₂f', h₁f'⟩, hf'⟩
  dsimp only [P] at hf
  simp only [forall_and] at hf
  rcases hf with ⟨⟨h₀f, -, h₁f⟩, hfU⟩
  rcases U_fin.exists_forall_eventually_of_indexType hfU with ⟨F, hF⟩
  refine ⟨F, fun x ↦ ?_, fun j ↦ ?_⟩
  · rcases(hF x).exists with ⟨n₀, hn₀⟩
    simp only [Germ.coe_eq.mpr hn₀.symm, h₀f n₀ x]
  · intro x
    rcases((hF x).and <| eventually_ge_atTop j).exists with ⟨n₀, hn₀, hn₀'⟩
    convert (h₁f _ _ hn₀' x) using 1
    all_goals try with_reducible_and_instances rfl
    exact Germ.coe_eq.mpr hn₀.symm

set_option backward.isDefEq.respectTransparency.types false in
theorem inductive_construction_of_loc' {X Y : Type*} [EMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (P₀ P₀' P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop) {f₀ : X → Y}
    (hP₀f₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y}, IsOpen U₁ → IsOpen U₂ →
      IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f) ∧
        (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₀' x f ∧ P₁ x f := by
  let P : Set X → Prop := fun U ↦ ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ x ∈ U, P₁ x f
  have hP₁ : Antitone P := by
    rintro U V hUV ⟨f, h, h'⟩
    exact ⟨f, h, fun x hx ↦ h' x (hUV hx)⟩
  have hP₂ : P ∅ := ⟨f₀, fun x ↦ (hP₀f₀ x).1, fun x h ↦ h.elim⟩
  have hP₃ : ∀ x : X, x ∈ univ → ∃ V ∈ 𝓝 x, P V := fun x _ ↦ by
    rcases loc x with ⟨f, h₀f, h₁f⟩
    exact ⟨_, h₁f, f, h₀f, fun x ↦ id⟩
  rcases exists_locallyFinite_subcover_of_locally isClosed_univ hP₁ hP₂ hP₃ with
    ⟨K, U : IndexType 0 → Set X, K_cpct, U_op, hU, hKU, U_loc, hK⟩
  have ind' : ∀ (i : 𝓘 0) (f : X → Y), (∀ x, P₀ x f ∧ P₀' x f) →
      (∀ j < i, ∀ x, RestrictGermPredicate P₁ (K j) x ↑f) →
      ∃ f' : X → Y, (∀ x : X, P₀ x ↑f' ∧ P₀' x ↑f') ∧
        (∀ j ≤ i, ∀ x, RestrictGermPredicate P₁ (K j) x f') ∧ ∀ x, x ∉ U i → f' x = f x := by
    simp_rw [forall_restrictGermPredicate_iff, ← eventually_nhdsSet_iUnion₂]
    rintro (i : ℕ) f h₀f h₁f
    have cpct : IsCompact (⋃ j < i, K j) :=
      (finite_lt_nat i).isCompact_biUnion fun j _ ↦ K_cpct j
    rcases hU i with ⟨f', h₀f', h₁f'⟩
    rcases mem_nhdsSet_iff_exists.mp h₁f with ⟨V, V_op, hKV, h₁V⟩
    rcases ind V_op (U_op i) cpct (K_cpct i) hKV (hKU i) h₀f h₀f' h₁V h₁f' with
      ⟨F, h₀F, h₁F, hF⟩
    rw [← biUnion_le] at h₁F
    exact ⟨F, h₀F, h₁F, fun x hx ↦ hF.self_of_nhdsSet x (Or.inr hx)⟩
  have :=
    inductive_construction (fun x φ ↦ P₀ x φ ∧ P₀' x φ)
      (fun j : 𝓘 0 ↦ RestrictGermPredicate P₁ (K j)) (fun _ _ ↦ True) U_loc ⟨f₀, hP₀f₀, trivial⟩
  simp only [IndexType.not_isMax, not_false_iff, forall_true_left, true_and] at this
  rcases this ind' with ⟨f, h, h'⟩
  refine ⟨f, fun x ↦ ⟨(h x).1, (h x).2, ?_⟩⟩
  rcases mem_iUnion.mp (hK trivial : x ∈ ⋃ j, K j) with ⟨j, hj⟩
  exact (h' j x hj).self_of_nhds


/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  and such that `f₁` satisfies `P₀'` everywhere into a map satisfying `P₁` on `K₁ ∪ K₂` for any
  compact sets `Kᵢ ⊆ Uᵢ` and `P₀'` everywhere. -/
theorem inductive_construction_of_loc {X Y : Type*} [EMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (P₀ P₀' P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop) {f₀ : X → Y}
    (hP₀f₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y}, IsOpen U₁ → IsOpen U₂ →
      IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f) ∧
        (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₀' x f ∧ P₁ x f := by
  apply inductive_construction_of_loc' P₀ P₀' P₁ hP₀f₀ loc
  intro U₁ U₂ K₁ K₂ f₁ f₂ hU₁ hU₂ hK₁ hK₂
  solve_by_elim

theorem set_juggling {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    {K : Set X} (hK : IsClosed K) {U₁ U₂ K₁ K₂ : Set X} (U₁_op : IsOpen U₁)
    (U₂_op : IsOpen U₂) (K₁_cpct : IsCompact K₁) (K₂_cpct : IsCompact K₂) (hK₁U₁ : K₁ ⊆ U₁)
    (hK₂U₂ : K₂ ⊆ U₂) (U : Set X) (U_op : IsOpen U) (hKU : K ⊆ U) :
    ∃ K₁' K₂' U₁' U₂',
      IsOpen U₁' ∧ IsOpen U₂' ∧ IsCompact K₁' ∧ IsCompact K₂' ∧ K₁ ⊆ K₁' ∧ K₁' ⊆ U₁' ∧ K₂' ⊆ U₂' ∧
      K₁' ∪ K₂' = K₁ ∪ K₂ ∧ K ⊆ U₂'ᶜ ∧ U₁' ⊆ U ∪ U₁ ∧ U₂' ⊆ U₂ := by
  obtain ⟨U', U'_op, hKU', hU'U⟩ : ∃ U' : Set X, IsOpen U' ∧ K ⊆ U' ∧ closure U' ⊆ U :=
    normal_exists_closure_subset hK U_op hKU
  refine ⟨K₁ ∪ closure (K₂ ∩ U'), K₂ \ U', U₁ ∪ U, U₂ \ K,
    U₁_op.union U_op, U₂_op.sdiff hK, ?_, K₂_cpct.diff U'_op, subset_union_left,
    ?_, by gcongr, ?_, by grind, ?_, sdiff_subset⟩
  · exact K₁_cpct.union (K₂_cpct.closure_of_subset inter_subset_left)
  · gcongr; grw [← hU'U]
    gcongr
    exact inter_subset_right
  · rw [union_assoc]
    congr
    apply subset_antisymm
    · exact union_subset (K₂_cpct.isClosed.closure_subset_iff.mpr inter_subset_left) sdiff_subset
    · calc K₂ = K₂ ∩ U' ∪ K₂ \ U' := (inter_union_sdiff K₂ U').symm
        _     ⊆ closure (K₂ ∩ U') ∪ K₂ \ U' := union_subset_union_left (K₂ \ U') subset_closure
  · rw [union_comm]

/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  into a map satisfying `P₁` on `K₁ ∪ K₂` for any compact sets `Kᵢ ⊆ Uᵢ`.
This is deduced this version from the version where `K` is empty but adding some `P'₀`, see
`inductive_construction_of_loc`. -/
theorem relative_inductive_construction_of_loc {X Y : Type*} [EMetricSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    {K : Set X} (hK : IsClosed K) {f₀ : X → Y} (hP₀f₀ : ∀ x, P₀ x f₀) (hP₁f₀ : ∀ᶠ x near K, P₁ x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y},
      IsOpen U₁ → IsOpen U₂ → IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f) ∧ (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, (∀ x, P₀ x f ∧ P₁ x f) ∧ ∀ᶠ x near K, f x = f₀ x := by
  let P₀' : ∀ x : X, Germ (𝓝 x) Y → Prop := RestrictGermPredicate (fun x φ ↦ φ.value = f₀ x) K
  have hf₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀ := fun x ↦
    ⟨hP₀f₀ x, fun _ ↦ Eventually.of_forall fun x' ↦ rfl⟩
  have ind' : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y},
      IsOpen U₁ → IsOpen U₂ → IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f) ∧
        (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x := by
    intro U₁ U₂ K₁ K₂ f₁ f₂ U₁_op U₂_op K₁_cpct K₂_cpct hK₁U₁ hK₂U₂ hf₁ hf₂ hf₁U₁ hf₂U₂
    obtain ⟨h₀f₁, h₀'f₁⟩ := forall_and.mp hf₁
    rw [forall_restrictGermPredicate_iff] at h₀'f₁
    rcases(hasBasis_nhdsSet K).mem_iff.mp (hP₁f₀.germ_congr_set h₀'f₁) with ⟨U,
      ⟨U_op, hKU⟩, hU : ∀ {x}, x ∈ U → P₁ x f₁⟩
    obtain ⟨K₁', K₂', U₁', U₂', U₁'_op, U₂'_op, K₁'_cpct, K₂'_cpct, hK₁K₁', hK₁'U₁', hK₂'U₂',
        hK₁'K₂', hKU₂', hU₁'U, hU₂'U₂⟩ : ∃ (K₁' K₂' U₁' U₂' : Set X),
        IsOpen U₁' ∧ IsOpen U₂' ∧ IsCompact K₁' ∧ IsCompact K₂' ∧
        K₁ ⊆ K₁' ∧ K₁' ⊆ U₁' ∧ K₂' ⊆ U₂' ∧ K₁' ∪ K₂' = K₁ ∪ K₂ ∧ K ⊆ U₂'ᶜ ∧
        U₁' ⊆ U ∪ U₁ ∧ U₂' ⊆ U₂ := by
      apply set_juggling <;> assumption
    have hU₁'P₁ : ∀ x ∈ U₁', P₁ x ↑f₁ :=
      fun x hx ↦ (hU₁'U hx).casesOn (fun h _ ↦ hU h) (fun h _ ↦ hf₁U₁ x h) (hU₁'U hx)
    rcases ind U₁'_op U₂'_op K₁'_cpct K₂'_cpct hK₁'U₁' hK₂'U₂' h₀f₁ hf₂ hU₁'P₁
      (fun x hx ↦ hf₂U₂ x (hU₂'U₂ hx)) with ⟨f, h₀f, hf, h'f⟩
    refine ⟨f, fun x ↦ ⟨h₀f x, restrictGermPredicate_congr (hf₁ x).2 ?_⟩, ?_, ?_⟩
    · exact h'f.filter_mono (nhdsSet_mono <| subset_union_of_subset_right hKU₂' K₁')
    · rwa [hK₁'K₂'] at hf
    · apply h'f.filter_mono; gcongr
  rcases inductive_construction_of_loc P₀ P₀' P₁ hf₀ loc ind' with ⟨f, hf⟩
  simp only [forall_and, forall_restrictGermPredicate_iff, P₀'] at hf ⊢
  exact ⟨f, ⟨hf.1, hf.2.2⟩, hf.2.1⟩

end inductive_construction
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Equivariant
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function FiniteDimensional Prod Int

open scoped Topology unitInterval

theorem continuous_linearReparam : Continuous linearReparam := by
  have h1 : Continuous (uncurry fun t x ↦ t + 4⁻¹ - abs (x - 2⁻¹) : ℝ × ℝ → ℝ) := by fun_prop
  exact h1.continuousOn.comp_fract (by fun_prop) fun s ↦ by norm_num
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Analysis_Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Filter

open scoped Topology ContDiff

namespace Real

theorem smoothTransition_projI {x : ℝ} : smoothTransition (projI x) = smoothTransition x :=
  smoothTransition.projIcc

end Real

open Filter
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Basic
attribute [-instance] _root_.SmoothSurroundingFamily.instCoeFunForallLoop
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Basic definitions and properties of loops
-/

section

open Set Function FiniteDimensional Int TopologicalSpace

open scoped Topology unitInterval

noncomputable section

variable {K X X' Y Z : Type*}

-- variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-! ## Definition and periodicity lemmas -/


variable (X)

initialize_simps_projections Loop (toFun → apply)

variable {X}

namespace Loop

/-! ## Support of a loop family -/


/-! ## From paths to loops -/


/-! ## Round trips -/


attribute [fun_prop] Path.trans_continuous_family

/-! ## Average value of a loop -/

end Loop

section C1

/-! ## Differentiation of loop families -/


variable (π : E → ℝ) (N : ℝ) (γ : E → Loop F) (hγ : IsCompact (Loop.support γ))

variable [FiniteDimensional ℝ F]


variable [FiniteDimensional ℝ E]

attribute [fun_prop] contDiff_parametric_integral_of_contDiff

variable {γ}

theorem contDiff_average {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n fun x ↦ (γ x).average := by
  unfold Loop.average; fun_prop

end C1
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_Corrugation
attribute [-instance] _root_.SmoothSurroundingFamily.instCoeFunForallLoop
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-! # Theillière's corrugation operation

This files introduces the fundamental calculus tool of convex integration. The version of convex
integration that we formalize is Theillière's corrugation-based convex integration.
It improves a map `f : E → F` by adding to it some corrugation map
`fun x ↦ (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)` where `γ` is a family of loops in
`F` parametrized by `E` and `N` is some (very large) real number.

Under the assumption that `∀ x, (γ x).average = D f x p.v` for some dual pair `p`, this improved
map will have a derivative which is almost a value of `γ x` in direction `p.v` and almost the
derivative of `f` in direction `ker p.π`. More precisely, its derivative will be almost
`p.update (D f x) (γ x (N*p.π x))`. In addition the improved map will be very close to `f`
in C⁰ topology. All those "almost" and "very close" refer to the asymptotic behavior when `N`
is very large.

The main definition is `corrugation`. The main results are:
* `fderiv_corrugated_map` computing the difference between `D (f + corrugation p.π N γ) x` and
    `p.update (D f x) (γ x (N*p.π x)) + corrugation.remainder p.π N γ x`
* `remainder_c0_small_on` saying this difference is very small
* `corrugation.c0_small_on` saying that corrugations are C⁰-small

-/

section

noncomputable section

open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {π : E →L[ℝ] ℝ} (N : ℝ) (γ : E → Loop F)

open scoped Borelize

/-- Theillière's corrugations. -/
def corrugation (π : E →L[ℝ] ℝ) (N : ℝ) (γ : E → Loop F) : E → F := fun x ↦
  (1 / N) • ∫ t in (0)..N * π x, γ x t - (γ x).average

@[inherit_doc] local notation "𝒯" => corrugation π

variable (π)

variable {γ}

theorem corrugation.contDiff' {n : ℕ∞} {γ : G → E → Loop F} (hγ_diff : 𝒞 n ↿γ) {x : H → E}
    (hx : 𝒞 n x) {g : H → G} (hg : 𝒞 n g) : 𝒞 n fun h ↦ 𝒯 N (γ <| g h) <| x h := by
  apply ContDiff.const_smul
  apply contDiff_parametric_primitive_of_contDiff
  · apply ContDiff.sub
    · exact hγ_diff.comp₃ hg.fst' hx.fst' contDiff_snd
    · apply contDiff_average
      exact hγ_diff.comp₃ hg.fst'.fst' hx.fst'.fst' contDiff_snd
  · exact contDiff_const.mul (π.contDiff.comp hx)

notation "∂₁" => partialFDerivFst ℝ

/-- The remainder appearing when differentiating a corrugation.
-/
def corrugation.remainder (π : E → ℝ) (N : ℝ) (γ : E → Loop F) : E → E →L[ℝ] F := fun x ↦
  (1 / N) • ∫ t in (0)..N * π x, ∂₁ (fun x t ↦ (γ x).normalize t) x t

@[inherit_doc] local notation "R" => corrugation.remainder π

variable [FiniteDimensional ℝ E]

open scoped ContDiff

theorem Remainder.smooth {γ : G → E → Loop F} (hγ_diff : 𝒞 ∞ ↿γ) {x : H → E} (hx : 𝒞 ∞ x)
    {g : H → G} (hg : 𝒞 ∞ g) : 𝒞 ∞ fun h ↦ R N (γ <| g h) <| x h := by
  apply ContDiff.const_smul
  apply contDiff_parametric_primitive_of_contDiff
  · let ψ : E → H × ℝ → F := fun x q ↦ (γ (g q.1) x).normalize q.2
    change  𝒞 ∞ fun q : H × ℝ ↦ ∂₁ ψ (x q.1) (q.1, q.2)
    refine (ContDiff.contDiff_top_partial_fst ?_).comp₂ hx.fst' (contDiff_fst.prodMk contDiff_snd)
    apply ContDiff.sub
    · apply hγ_diff.comp₃ hg.fst'.snd' contDiff_fst contDiff_snd.snd
    · apply contDiff_average
      exact hγ_diff.comp₃ hg.fst'.snd'.fst' contDiff_fst.fst' contDiff_snd
  · exact contDiff_const.mul (π.contDiff.comp hx)
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_ExistsOfConvex
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open scoped Topology Manifold ContDiff

open Set Function Filter

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {HG : Type*} [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ G HG) {N : Type*} [TopologicalSpace N] [ChartedSpace HG N]
  [IsManifold IG ∞ N]

variable (I)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem reallyConvex_contMDiffAt (x : M) (n : ℕ∞) :
    ReallyConvex (smoothGerm I x) {φ : Germ (𝓝 x) F | φ.ContMDiffAt I n} := by
  classical
  rw [Nontrivial.reallyConvex_iff]
  rintro w _w_pos w_supp w_sum
  have : (support w).Finite := hasFiniteSupport_of_finsum_eq_one w_sum
  set fin_supp := this.toFinset with H
  have : (support fun i : (𝓝 x).Germ F ↦ w i • i) ⊆ fin_supp := by
    rw [Set.Finite.coe_toFinset]
    exact support_smul_subset_left w id
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Filter.Germ.ContMDiffAt.sum fun φ hφ ↦ (smoothGerm.contMDiffAt _).smul (w_supp ?_)
  simpa [H] using hφ

theorem exists_contMDiff_of_convex {P : M → F → Prop} (hP : ∀ x, Convex ℝ {y | P x y}) {n : ℕ∞}
    (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, CMDiff[U] n f ∧ ∀ x ∈ U, P x (f x)) :
    ∃ f : M → F, CMDiff n f ∧ ∀ x, P x (f x) := by
  let PP : (Σ x : M, Germ (𝓝 x) F) → Prop := fun p ↦ p.2.ContMDiffAt I n ∧ P p.1 p.2.value
  have hPP : ∀ x : M, ReallyConvex (smoothGerm I x) {φ | PP ⟨x, φ⟩} := fun x ↦ by
    apply ReallyConvex.inter
    · apply reallyConvex_contMDiffAt
    let v : Germ (𝓝 x) F →ₛₗ[smoothGerm.valueRingHom I x] F := Filter.Germ.valueₛₗ I x
    change ReallyConvex (smoothGerm I x) (v ⁻¹' {y | P x y})
    dsimp only [← smoothGerm.valueOrderRingHom_toRingHom] at v
    apply ReallyConvex.preimageₛₗ
    rw [reallyConvex_iff_convex]
    apply hP
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩ := fun x ↦ by
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩
    use f
    filter_upwards [eventually_mem_nhds_iff.mpr U_in] with y hy
    exact ⟨hf.contMDiffAt hy, hf' y (mem_of_mem_nhds hy)⟩
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩
  exact ⟨f, fun x ↦ (hf x).1, fun x ↦ (hf x).2⟩

theorem exists_contDiff_of_convex {P : E → F → Prop} (hP : ∀ x, Convex ℝ {y | P x y}) {n : ℕ∞}
    (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, ContDiffOn ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
    ∃ f : E → F, ContDiff ℝ n f ∧ ∀ x, P x (f x) := by
  simp_rw [← contMDiff_iff_contDiff]
  simp_rw [← contMDiffOn_iff_contDiffOn] at hP' ⊢
  exact exists_contMDiff_of_convex _ hP hP'

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

open TopologicalSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- lemma exists_smooth_and_eqOn_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (isOpen_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end
-- lemma exists_smooth_and_eqOn_aux2 {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (isOpen_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end
theorem exists_smooth_and_eqOn {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : Continuous f)
    (hε : Continuous ε) (h2ε : ∀ x, 0 < ε x) {s : Set E} (hs : IsClosed s)
    (hfs : ∃ U ∈ 𝓝ˢ s, ContDiffOn ℝ n f U) :
    ∃ f' : E → F, ContDiff ℝ n f' ∧ (∀ x, dist (f' x) (f x) < ε x) ∧ EqOn f' f s := by
  have h0 : ∀ x, dist (f x) (f x) < ε x := fun x ↦ by simp_rw [dist_self, h2ε]
  let P : E → F → Prop := fun x t ↦ dist t (f x) < ε x ∧ (x ∈ s → t = f x)
  have hP : ∀ x, Convex ℝ {y | P x y} := fun x ↦
    (convex_ball (f x) (ε x)).inter (convex_setOf_imp_eq _ _)
  obtain ⟨f', hf', hPf'⟩ : ∃ f' : E → F, ContDiff ℝ n f' ∧  ∀ x, P x (f' x) := by
    apply exists_contDiff_of_convex hP
    intro x
    obtain ⟨U, hU, hfU⟩ := hfs
    by_cases hx : x ∈ s
    · refine ⟨U, mem_nhdsSet_iff_forall.mp hU x hx, ?_⟩
      exact ⟨f, hfU, fun y _ ↦ ⟨h0 y, fun _ ↦ rfl⟩⟩
    · have : IsOpen {y : E | dist (f x) (f y) < ε y} := isOpen_lt (continuous_const.dist hf) hε
      exact ⟨_, (this.sdiff hs).mem_nhds ⟨h0 x, hx⟩, fun _ ↦ f x, contDiffOn_const, fun y hy ↦
        ⟨hy.1, fun h2y ↦ (hy.2 h2y).elim⟩⟩
  exact ⟨f', hf', fun x ↦ (hPf' x).1, fun x ↦ (hPf' x).2⟩

end
end
end
end

section
-- module Solutions.OAIQ249_SI.ToMathlib_Topology_Path
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

open Set Function

open scoped Topology unitInterval

noncomputable section

variable {X X' Y Z : Type*} [TopologicalSpace X]
  [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Path

variable {x : X} {γ γ' : Path x x}

/-- Reformulate `strans` without using `extend`. This is useful to not have to prove that the
  arguments to `γ` lie in `I` after this. -/
theorem strans_def {x : X} {t₀ t : I} (γ γ' : Path x x) :
    γ.strans γ' t₀ t =
      if h : t ≤ t₀ then γ ⟨t / t₀, unitInterval.div_mem t.2.1 t₀.2.1 h⟩
      else γ' ⟨(t - t₀) / (1 - t₀),
        unitInterval.div_mem (sub_nonneg.mpr <| le_of_not_ge h) (sub_nonneg.mpr t₀.2.2)
          (sub_le_sub_right t.2.2 t₀)⟩ := by
  split_ifs with h <;> simp [strans, h, ← extend_apply]

theorem subset_range_strans_left {x : X} {γ γ' : Path x x} {t₀ : I} (h : t₀ ≠ 0) :
    range γ ⊆ range (γ.strans γ' t₀) := by
  rintro _ ⟨t, rfl⟩
  use t * t₀
  simp [strans, unitInterval.mul_le_right, unitInterval.coe_ne_zero.mpr h]

theorem subset_range_strans_right {x : X} {γ γ' : Path x x} {t₀ : I} (h : t₀ ≠ 1) :
    range γ' ⊆ range (γ.strans γ' t₀) := by
  rintro _ ⟨t, rfl⟩
  have := mul_nonneg t.2.1 (sub_nonneg.mpr t₀.2.2)
  let t' : I := ⟨t₀ + t * (1 - t₀), add_nonneg t₀.2.1 this, by
      rw [add_comm, ← le_sub_iff_add_le]
      exact (mul_le_mul_of_nonneg_right t.2.2 <| sub_nonneg.mpr t₀.2.2).trans_eq (one_mul _)⟩
  have h2 : t₀ ≤ t' := le_add_of_nonneg_right this
  have h3 := sub_ne_zero.mpr (unitInterval.coe_ne_one.mpr h).symm
  use t'
  simp [h2, h3, t']

theorem range_strans_subset {x : X} {γ γ' : Path x x} {t₀ : I} :
    range (γ.strans γ' t₀) ⊆ range γ ∪ range γ' := by
  rintro _ ⟨t, rfl⟩
  by_cases h : t ≤ t₀
  · rw [strans_def, dite_eq_left h]; exact Or.inl (mem_range_self _)
  · rw [strans_def, dite_eq_right h]; exact Or.inr (mem_range_self _)

end Path
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Surrounding
attribute [-instance] _root_.SmoothSurroundingFamily.instCoeFunForallLoop _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.SmoothSurroundingFamily.centeringDensity_average _root_.SmoothSurroundingFamily.localCenteringDensity_average
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Surrounding families of loops

In order to carry out the corrugation technique of convex integration, one needs to a family of
loops with various prescribed properties.

This file begins the work of constructing such a family.

The key definitions are:
 * `Surrounded`
 * `SurroundingPts`
 * `SurroundingFamily`

The key results are:
 * `surrounded_iff_mem_interior_convexHull_aff_basis`
 * `surrounded_of_convexHull`
 * `smooth_surrounding`
 * `eventually_surroundingPts_of_tendsto_of_tendsto`
 * `surrounding_loop_of_convexHull`
 * `local_loops`
 * `satisfied_or_refund`
 * `extend_loops`
 * `exists_surrounding_loops`
-/

section

-- to obtain that normed spaces are locally connected
open Set Function Module Int Prod Path Filter
open scoped Topology unitInterval ContDiff

namespace IsPathConnected

attribute [simp] Path.trans_range

end IsPathConnected

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

set_option hygiene false
@[inherit_doc] local notation "d" => finrank ℝ F
set_option hygiene true

/-
The definition below gets a prime because it clashes with a manifold definition
in mathlib which is in the root namespace.
XXX: this is no longer true.
-/

section SurroundingPoints

set_option hygiene false
@[inherit_doc] local notation "ι" => Fin (d + 1)
set_option hygiene true

/-- `f` is surrounded by a set `s` if there is an affine basis `p` in `s` with weighted average `f`.
-/
def Surrounded (f : F) (s : Set F) : Prop :=
  ∃ p w, SurroundingPts f p w ∧ ∀ i, p i ∈ s

theorem surrounded_iff_mem_interior_convexHull_aff_basis [FiniteDimensional ℝ F] {f : F}
    {s : Set F} :
    Surrounded f s ↔
      ∃ b, b ⊆ s ∧ AffineIndependent ℝ ((↑) : b → F) ∧ affineSpan ℝ b = ⊤ ∧
        f ∈ interior (convexHull ℝ b) := by
  constructor
  · rintro ⟨p, w, ⟨⟨indep, w_pos, w_sum, rfl⟩, h_mem⟩⟩
    have h_tot : affineSpan ℝ (range p) = ⊤ :=
      indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (Fintype.card_fin _)
    refine ⟨range p, range_subset_iff.mpr h_mem, indep.range, h_tot, ?_⟩
    let basis : AffineBasis ι ℝ F := ⟨p, indep, h_tot⟩
    erw [basis.interior_convexHull]
    intro i
    erw [← Finset.affineCombination_eq_linear_combination _ _ _ w_sum,
      basis.coord_apply_combination_of_mem (Finset.mem_univ i) w_sum]
    exact w_pos i
  · rintro ⟨b, h₀, h₁, h₂, h₃⟩
    have : Fintype b := (finite_set_of_fin_dim_affineIndependent ℝ h₁).fintype
    have hb : Fintype.card b = d + 1 := by
      rw [← h₁.affineSpan_eq_top_iff_card_eq_finrank_add_one, Subtype.range_coe_subtype,
        ofPred_mem_eq, h₂]
    let p := ((↑) : _ → F) ∘ (Fintype.equivFinOfCardEq hb).symm
    have hp : b = range p := by
      ext x
      exact ⟨by intro h; use Fintype.equivFinOfCardEq hb ⟨x, h⟩; simp [p], by
        rintro ⟨y, rfl⟩; apply Subtype.coe_prop⟩
    rw [hp] at h₀ h₂ h₃
    replace h₁ : AffineIndependent ℝ p :=
      h₁.comp_embedding (Fintype.equivFinOfCardEq hb).symm.toEmbedding
    let basis : AffineBasis ι ℝ F := ⟨_, h₁, h₂⟩
    erw [basis.interior_convexHull, mem_ofPred_eq] at h₃
    refine ⟨p, fun i ↦ basis.coord i f, ⟨h₁, h₃, ?_, ?_⟩, fun i ↦ h₀ (mem_range_self i)⟩
    · exact basis.sum_coord_apply_eq_one f
    · erw [← Finset.univ.affineCombination_eq_linear_combination p _
        (basis.sum_coord_apply_eq_one f), basis.affineCombination_coord_eq_self]

--- `prop:surrounded_by_open`
set_option backward.isDefEq.respectTransparency false in
theorem surrounded_of_convexHull [FiniteDimensional ℝ F] {f : F} {s : Set F} (hs : IsOpen s)
    (hsf : f ∈ convexHull ℝ s) : Surrounded f s := by
  rw [surrounded_iff_mem_interior_convexHull_aff_basis]
  obtain ⟨t, hts, hai, hf⟩ :
    ∃ t : Finset F,
      (t : Set F) ⊆ s ∧ AffineIndependent ℝ ((↑) : t → F) ∧ f ∈ convexHull ℝ (t : Set F) := by
    simp_rw [← exists_prop, ← mem_iUnion, ← convexHull_eq_union]
    exact hsf
  have htne : (t : Set F).Nonempty := convexHull_nonempty_iff.mp ⟨f, hf⟩
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := hs.exists_between_affineIndependent_span_eq_top hts htne hai
  have hb₀ : b.Finite := (finite_set_of_fin_dim_affineIndependent ℝ hb₃)
  obtain ⟨c, hc⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hb₄
  rw [← hs.interior_eq] at hb₂
  obtain ⟨ε, hε, hcs⟩ :=
    (eventually_homothety_image_subset_of_finite_subset_interior ℝ c hb₀ hb₂).exists_gt
  have hbε := Convex.subset_interior_image_homothety_of_one_lt (convex_convexHull ℝ _) hc ε hε
  rw [AffineMap.image_convexHull] at hbε
  let t : Units ℝ := Units.mk0 ε (by linarith)
  refine ⟨AffineMap.homothety c (t : ℝ) '' b, hcs, ?_, ?_, hbε (convexHull_mono hb₁ hf)⟩
  · rwa [(AffineEquiv.homothetyUnitsMulHom c t).affineIndependent_set_of_eq_iff]
  · exact (AffineEquiv.homothetyUnitsMulHom c t).span_eq_top_iff.mp hb₄

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/

end SurroundingPoints

section surroundingLoop

variable {O : Set F} {b : F} {p : Fin (d + 1) → F} (O_conn : IsPathConnected O)
  (hp : ∀ i, p i ∈ O) (hb : b ∈ O)

variable {O_conn hp hb}

theorem surroundingLoop_mem (t s : ℝ) : surroundingLoop O_conn hp hb t s ∈ O := by
  revert s
  rw [← range_subset_iff]
  simp only [surroundingLoop, Loop.roundTripFamily, Loop.roundTrip_range,
    cast_coe]
  refine Subset.trans (truncate_range _) ?_
  simp only [trans_range, union_subset_iff, O_conn.range_somePath_subset,
    O_conn.range_pathThrough_subset, true_and]

theorem surroundingLoop_surrounds {f : F} {w : Fin (d + 1) → ℝ} (h : SurroundingPts f p w) :
    (surroundingLoop O_conn hp hb 1).Surrounds f := by
  rw [Loop.surrounds_iff_range_subset_range]
  refine ⟨p, w, h, ?_⟩
  simp only [surroundingLoop, Loop.roundTripFamily_one, Loop.roundTrip_range, trans_range,
    range_subset_iff, mem_union, O_conn.mem_range_pathThrough, or_true, forall_true_iff]

theorem surroundingLoop_projI (t : ℝ) :
    surroundingLoop O_conn hp hb (projI t) = surroundingLoop O_conn hp hb t :=
  Loop.roundTrip_eq fun s ↦ by simp_rw [Path.cast_coe, truncate_projI_right]

theorem surrounding_loop_of_convexHull [FiniteDimensional ℝ F] {f b : F} {O : Set F}
    (O_op : IsOpen O) (O_conn : IsConnected O) (hsf : f ∈ convexHull ℝ O) (hb : b ∈ O) :
    ∃ γ : ℝ → Loop F,
      Continuous ↿γ ∧
        (∀ t, γ t 0 = b) ∧
          (∀ s, γ 0 s = b) ∧
            (∀ s t, γ (projI t) s = γ t s) ∧ (∀ t s, γ t s ∈ O) ∧ (γ 1).Surrounds f := by
  rcases surrounded_of_convexHull O_op hsf with ⟨p, w, h, hp⟩
  rw [O_op.isConnected_iff_isPathConnected] at O_conn
  exact ⟨surroundingLoop O_conn hp hb, continuous_surroundingLoop, surroundingLoop_zero_right,
    surroundingLoop_zero_left, fun s t ↦ by rw [surroundingLoop_projI], surroundingLoop_mem,
    surroundingLoop_surrounds h⟩

end surroundingLoop

/-- `γ` forms a family of loops surrounding `g` with base `b` in `Ω`. -/
structure SurroundingFamilyIn (g b : E → F) (γ : E → ℝ → Loop F) (U : Set E)
    (Ω : Set <| E × F) : Prop extends SurroundingFamily g b γ U where
  val_in' : ∀ x ∈ U, ∀ t ∈ I, ∀ s ∈ I, (x, γ x t s) ∈ Ω

namespace SurroundingFamily

variable {g b : E → F} {γ : E → ℝ → Loop F} {U : Set E}

omit [NormedSpace ℝ E]

protected theorem t_le_zero (h : SurroundingFamily g b γ U) (x : E) (s : ℝ) {t : ℝ} (ht : t ≤ 0) :
    γ x t s = γ x 0 s := by rw [← h.projI, projI_eq_zero.mpr ht]

protected theorem t_le_zero_eq_b (h : SurroundingFamily g b γ U) (x : E) (s : ℝ) {t : ℝ}
    (ht : t ≤ 0) : γ x t s = b x := by rw [h.t_le_zero x s ht, h.t₀]

protected theorem t_ge_one (h : SurroundingFamily g b γ U) (x : E) (s : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    γ x t s = γ x 1 s := by rw [← h.projI, projI_eq_one.mpr ht]

protected theorem mono (h : SurroundingFamily g b γ U) {V : Set E} (hVU : V ⊆ U) :
    SurroundingFamily g b γ V :=
  ⟨h.base, h.t₀, h.projI, fun x hx ↦ h.surrounds x (hVU hx), h.cont⟩

variable [NormedSpace ℝ E] in
protected theorem surrounds_of_close_univ [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hg : Continuous g) (h : SurroundingFamily g b γ univ) :
    ∃ ε : E → ℝ,
      (∀ x, 0 < ε x) ∧
        Continuous ε ∧
          ∀ (x) (γ' : Loop F), (∀ z, dist (γ' z) (γ x 1 z) < ε x) → γ'.Surrounds (g x) := by
  let P : E → ℝ → Prop := fun x t ↦
    0 < t ∧ ∀ γ' : Loop F, (∀ z, dist (γ' z) (γ x 1 z) < t) → γ'.Surrounds (g x)
  have hP : ∀ x, Convex ℝ {t | P x t} := by
    intro x
    rw [convex_iff_ordConnected]
    constructor
    rintro ε₁ hε₁ ε₂ hε₂ ε₃ ⟨hε₁₃, hε₃₂⟩
    exact ⟨hε₁.1.trans_le hε₁₃, fun γ hγ ↦ hε₂.2 γ fun z ↦ (hγ z).trans_le hε₃₂⟩
  rsuffices ⟨ε, hε, hPε⟩ : ∃ ε : E → ℝ, 𝒞 0 ε ∧ ∀ x, P x (ε x)
  -- obtain ⟨ε, hε, hPε⟩ := exists_contDiff_of_convex hP _
  · exact ⟨ε, fun x ↦ (hPε x).1, contDiff_zero.mp hε, fun x ↦ (hPε x).2⟩
  refine exists_contDiff_of_convex hP fun x ↦ ?_
  obtain ⟨ε, hε, h2⟩ := (h.surrounds x (mem_univ _)).eventually_surrounds
  have h3 : {y : E | dist (g y) (g x) < ε} ∈ 𝓝 x :=
    (Metric.isOpen_ball.preimage hg).mem_nhds
      (by simp_rw [mem_preimage, Metric.mem_ball, dist_self, hε.lt])
  have h4 : {y : E | ∀ z, dist (γ y 1 z) (γ x 1 z) < ε / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ fun z ↦ by simp_rw [dist_self, half_pos hε]
    have hc : Continuous ↿fun y s ↦ dist (γ y 1 s) (γ x 1 s) :=
      (h.cont.comp₃ continuous_fst continuous_const continuous_snd).dist
        (h.cont.comp₃ continuous_const continuous_const continuous_snd)
    have : IsOpen {y : E | sSup ((fun z ↦ dist (γ y 1 z) (γ x 1 z)) '' I) < ε / 2} :=
      isOpen_lt (isCompact_Icc.continuous_sSup hc) continuous_const
    have hc : ∀ y, Continuous fun s ↦ dist (γ y 1 s) (γ x 1 s) := fun y ↦
      hc.comp₂ continuous_const continuous_id
    simp_rw [isCompact_Icc.sSup_lt_iff_of_continuous (nonempty_Icc.mpr zero_le_one)
        (hc _).continuousOn] at this
    convert this using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    refine ⟨fun h z _ ↦ h z, fun h z ↦ ?_⟩
    rw [← (γ y 1).fract_eq, ← (γ x 1).fract_eq]
    exact h _ (unitInterval.fract_mem _)
  refine ⟨_, inter_mem h4 h3, fun _ ↦ ε / 2, contDiffOn_const, fun y hy ↦
      ⟨half_pos hε, fun γ' hγ' ↦ h2 _ _ (fun z ↦ ?_) hy.2⟩⟩
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add (hγ' z) (hy.1 z)).trans_le (add_halves ε).le)

end SurroundingFamily

variable {g b : E → F} {U K C : Set E} {Ω : Set (E × F)}

namespace SurroundingFamilyIn

variable {γ : E → ℝ → Loop F}

omit [NormedSpace ℝ E]

/-- Abbreviation for `toSurroundingFamily` -/
theorem to_sf (h : SurroundingFamilyIn g b γ U Ω) : SurroundingFamily g b γ U :=
  h.toSurroundingFamily

theorem val_in (h : SurroundingFamilyIn g b γ U Ω) {x : E} (hx : x ∈ U) {t : ℝ} {s : ℝ} :
    (x, γ x t s) ∈ Ω := by
  rw [← Loop.fract_eq, ← h.projI]
  exact h.val_in' x hx (projI t) projI_mem_Icc (fract s) (unitInterval.fract_mem s)

protected theorem mono (h : SurroundingFamilyIn g b γ U Ω) {V : Set E} (hVU : V ⊆ U) :
    SurroundingFamilyIn g b γ V Ω :=
  ⟨h.to_sf.mono hVU, fun x hx ↦ h.val_in' x (hVU hx)⟩

/-- Continuously reparameterize a `surroundingFamilyIn` so that it is constant near
  `s ∈ {0,1}` and `t ∈ {0,1}` -/
protected theorem reparam (h : SurroundingFamilyIn g b γ U Ω) :
    SurroundingFamilyIn g b (fun x t ↦ (γ x (linearReparam t)).reparam linearReparam) U Ω := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x t; rw [Loop.reparam_apply, linearReparam_zero, h.base]
  · intro x s; rw [Loop.reparam_apply, linearReparam_zero, h.t₀]
  · intro x t s; simp_rw [Loop.reparam_apply, linearReparam_projI, h.projI]
  · intro x hx; rw [linearReparam_one]
    exact (h.surrounds x hx).reparam continuous_linearReparam
  · exact h.cont.comp₃ continuous_fst continuous_linearReparam.fst'.snd'
      continuous_linearReparam.snd'.snd'
  · exact fun x hx t _ s _ ↦ h.val_in hx

end SurroundingFamilyIn

section local_loops

variable {x₀ : E} (hΩ_conn : IsPathConnected (Prod.mk x₀ ⁻¹' Ω)) (hb_in : (x₀, b x₀) ∈ Ω)
  {p : Fin (d + 1) → F} (hp : ∀ i, p i ∈ Prod.mk x₀ ⁻¹' Ω)

omit [NormedSpace ℝ E]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- /-- The witness of `local_loops`. -/
-- def local_loops_def (x : E) (t : ℝ) : loop F :=
-- b x - b x₀ +ᵥ surrounding_loop hΩ_conn hp hb_in t
/-- Note: The conditions in this lemma are currently a bit weaker than the ones mentioned in the
blueprint.
TODO: use `local_loops_def`
-/
theorem local_loops [FiniteDimensional ℝ F] {x₀ : E} (hΩ_op : ∃ U ∈ 𝓝 x₀, IsOpen (Ω ∩ fst ⁻¹' U))
    (hg : ContinuousAt g x₀) (hb : Continuous b)
    (hconv : g x₀ ∈ convexHull ℝ (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀)) :
    ∃ γ : E → ℝ → Loop F, ∃ U ∈ 𝓝 x₀, SurroundingFamilyIn g b γ U Ω := by
  have hΩ_op_x₀ : IsOpen (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀) :=
    (isOpen_slice_of_isOpen_over hΩ_op).connectedComponentIn
  have b_in : b x₀ ∈ Prod.mk x₀ ⁻¹' Ω :=
    connectedComponentIn_nonempty_iff.mp (convexHull_nonempty_iff.mp ⟨g x₀, hconv⟩)
  have hΩ_conn : IsConnected (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀) :=
    isConnected_connectedComponentIn_iff.mpr b_in
  have hb_in : b x₀ ∈ (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀) :=
    mem_connectedComponentIn b_in
  rcases surrounding_loop_of_convexHull hΩ_op_x₀ hΩ_conn hconv hb_in with
    ⟨γ, h1γ, h2γ, h3γ, h4γ, h5γ, h6γ⟩
  have h5γ : ∀ t s : ℝ, γ t s ∈ mk x₀ ⁻¹' Ω := fun t s ↦ connectedComponentIn_subset _ _ (h5γ t s)
  let δ : E → ℝ → Loop F := fun x t ↦ (b x - b x₀) +ᵥ γ t
  have hδ : Continuous ↿δ := by
    dsimp only [δ, HasUncurry.uncurry, Loop.vadd_apply]
    fun_prop
  have hδx₀ : ∀ t s, δ x₀ t s = γ t s := by
    intro t s
    simp only [δ, zero_add, Loop.vadd_apply, sub_self]
  have hδs0 : ∀ x t, δ x t 0 = b x := by intro x t; simp [δ, h2γ]
  have hδt0 : ∀ x s, δ x 0 s = b x := by intro x s; simp [δ, h3γ]
  have hδt1 : ∀ x t s, δ x (projI t) s = δ x t s := by intro x t s; simp [δ, h4γ]
  have hδΩ : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ I, ∀ s ∈ I, (x, δ x t s) ∈ Ω := by
    rcases hΩ_op with ⟨U, hUx₀, hU⟩
    -- todo: this is nicer with `IsCompact.eventually_forall_of_forall_eventually` twice, but then
    -- we need the continuity of `δ` with the arguments reassociated differently.
    have : ∀ᶠ x : E in 𝓝 x₀, ∀ ts : ℝ × ℝ, ts ∈ I ×ˢ I → (x, δ x ts.1 ts.2) ∈ Ω := by
      apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_mem
      · fun_prop
      · rintro ⟨t, s⟩ _
        rw [hδx₀]
        change Ω ∈ 𝓝 (x₀, γ t s)
        exact mem_nhds_iff.mpr
          ⟨_, inter_subset_left, hU, ⟨h5γ t s, show x₀ ∈ U from mem_of_mem_nhds hUx₀⟩⟩
    refine this.mono ?_; intro x h t ht s hs; exact h (t, s) ⟨ht, hs⟩
  have hδsurr : ∀ᶠ x in 𝓝 x₀, (δ x 1).Surrounds (g x) := by
    rcases h6γ with ⟨p, w, h⟩
    obtain ⟨W, hW⟩ := smooth_surroundingPts h
    let c : E → F × (Fin (d + 1) → F) := fun x ↦ (g x, δ x 1 ∘ p)
    have hc : ContinuousAt c x₀ := by fun_prop
    have hcx₀ : c x₀ = (g x₀, γ 1 ∘ p) := by
      simp [c, δ]
    rw [← hcx₀] at hW
    filter_upwards [hc.tendsto.eventually hW]
    rintro x ⟨_, hx⟩
    exact ⟨_, _, hx⟩
  exact ⟨δ, _, hδΩ.and hδsurr, ⟨⟨hδs0, hδt0, hδt1, fun x ↦ And.right, hδ⟩, fun x ↦ And.left⟩⟩

end local_loops

attribute [fun_prop] continuous_projI

theorem ρ_mem_I {x : ℝ} : ρ x ∈ I :=
  projI_mem_Icc

section satisfied_or_refund

variable {γ₀ γ₁ : E → ℝ → Loop F}

variable (h₀ : SurroundingFamily g b γ₀ U) (h₁ : SurroundingFamily g b γ₁ U)

variable {h₀ h₁}

omit [NormedSpace ℝ E]

attribute [fun_prop] continuous_projIcc

theorem surroundingFamily_sfHomotopy [NormedSpace ℝ E] [FiniteDimensional ℝ E] (τ : ℝ) :
    SurroundingFamily g b (sfHomotopy h₀ h₁ τ) U := by
  constructor
  · intro x t;
    simp only [sfHomotopy, Icc.mk_zero, zero_le_one, extend_apply, Path.source, Loop.ofPath_apply,
      left_mem_Icc, fract_zero]
  · intro x s
    -- have h2t : ρ τ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (ρ_nonneg τ) ht,
    -- have h3t : ρ (1 - τ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (ρ_nonneg _) ht,
    -- have h4t : t ≤ 1 := ht.trans zero_le_one,
    simp [sfHomotopy]
  · intro x t s; simp only [sfHomotopy, projI_projI]
  -- { intros x t s ht, simp only [sfHomotopy, min_eq_left ht, min_self] },
  · intro x hx; obtain (h | h) := le_total τ (1 / 2)
    · have : τ < 1 := h.trans_lt (by norm_num)
      refine (h₀.surrounds x hx).mono ?_
      simp only [mul_one, Loop.range_ofPath, sfHomotopy, projI_one]
      exact Subset.trans (by simp only [SurroundingFamily.range_path, ρ_eq_one_of_le h]; rfl)
        (subset_range_strans_left <| by simp [this])
    · have : 0 < τ := lt_of_lt_of_le (by norm_num) h
      have h : 1 - τ ≤ 1 / 2 := by linarith
      refine (h₁.surrounds x hx).mono ?_
      simp only [mul_one, Loop.range_ofPath, sfHomotopy, projI_one]
      exact Subset.trans (by simp only [SurroundingFamily.range_path, ρ_eq_one_of_le h]; rfl)
        (subset_range_strans_right <| by simp [this])
  · fun_prop

/-- A more precise version of `sfHomotopy_in`. -/
theorem sfHomotopy_in' {ι} (h₀ : SurroundingFamily g b γ₀ U) (h₁ : SurroundingFamily g b γ₁ U)
    (τ : ι → ℝ) (x : ι → E) (i : ι) {V : Set E} (hx : x i ∈ V) {t : ℝ} (ht : t ∈ I) {s : ℝ}
    (h_in₀ : ∀ i, x i ∈ V → ∀ t ∈ I, ∀ (s : ℝ), τ i ≠ 1 → (x i, γ₀ (x i) t s) ∈ Ω)
    (h_in₁ : ∀ i, x i ∈ V → ∀ t ∈ I, ∀ (s : ℝ), τ i ≠ 0 → (x i, γ₁ (x i) t s) ∈ Ω) :
    (x i, sfHomotopy h₀ h₁ (τ i) (x i) t s) ∈ Ω := by
  by_cases hτ0 : τ i = 0
  · simp only [hτ0, sfHomotopy_zero]; exact h_in₀ i hx t ht s (by norm_num [hτ0])
  by_cases hτ1 : τ i = 1
  · simp only [hτ1, sfHomotopy_one]; exact h_in₁ i hx t ht s (by norm_num [hτ1])
  generalize hy : sfHomotopy h₀ h₁ (τ i) (x i) t s = y
  have h2y : y ∈ range (sfHomotopy h₀ h₁ (τ i) (x i) t) := by rw [← hy]; exact mem_range_self _
  rw [sfHomotopy, Loop.range_ofPath, projI_eq_self.mpr ht] at h2y
  replace h2y := range_strans_subset h2y
  rcases h2y with (⟨s', rfl⟩ | ⟨s', rfl⟩)
  · exact h_in₀ _ hx _ (unitInterval.mul_mem ρ_mem_I ht) _ hτ1
  · exact h_in₁ _ hx _ (unitInterval.mul_mem ρ_mem_I ht) _ hτ0

theorem sfHomotopy_in (h₀ : SurroundingFamilyIn g b γ₀ U Ω) (h₁ : SurroundingFamilyIn g b γ₁ U Ω)
    (τ : ℝ) ⦃x : E⦄ (hx : x ∈ U) {t : ℝ} (ht : t ∈ I) {s : ℝ} :
    (x, sfHomotopy h₀.to_sf h₁.to_sf τ x t s) ∈ Ω :=
  sfHomotopy_in' h₀.to_sf h₁.to_sf (fun _ ↦ τ) (fun _ ↦ x) () hx ht
    (fun _i hx _t _ _s _ ↦ h₀.val_in hx) fun _i hx _t _ _s _ ↦ h₁.val_in hx

theorem surroundingFamilyIn_sfHomotopy [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h₀ : SurroundingFamilyIn g b γ₀ U Ω) (h₁ : SurroundingFamilyIn g b γ₁ U Ω) (τ : ℝ) :
    SurroundingFamilyIn g b (sfHomotopy h₀.to_sf h₁.to_sf τ) U Ω :=
  ⟨surroundingFamily_sfHomotopy _, fun _x hx _t ht _s _hs ↦ sfHomotopy_in h₀ h₁ _ hx ht⟩

end satisfied_or_refund

section extend_loops

variable [FiniteDimensional ℝ E]

/-
Note: we also want add the condition that `γ = γ₀` outside a neighborhood of `U₁ᶜ`.
This makes it easier to find the limit of a sequence of these constructions.
-/
theorem extend_loops {U₀ U₁ K₀ K₁ : Set E} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hK₀ : IsClosed K₀)
    (hK₁ : IsClosed K₁) (hKU₀ : K₀ ⊆ U₀) (hKU₁ : K₁ ⊆ U₁) {γ₀ γ₁ : E → ℝ → Loop F}
    (h₀ : SurroundingFamilyIn g b γ₀ U₀ Ω) (h₁ : SurroundingFamilyIn g b γ₁ U₁ Ω) :
    ∃ U ∈ 𝓝ˢ (K₀ ∪ K₁),
      ∃ γ : E → ℝ → Loop F,
        SurroundingFamilyIn g b γ U Ω ∧
          (∀ᶠ x in 𝓝ˢ K₀, γ x = γ₀ x) ∧ ∀ᶠ x in 𝓝ˢ (U₁ᶜ), γ x = γ₀ x := by
  obtain ⟨V₀, hV₀, hKV₀, hVU₀⟩ := normal_exists_closure_subset hK₀ hU₀ hKU₀
  let L₁ := K₁ \ U₀
  have hL₁ : IsClosed L₁ := hK₁.sdiff hU₀
  have hV₀L₁ : Disjoint (closure V₀) L₁ := disjoint_sdiff_self_right.mono hVU₀ Subset.rfl
  obtain ⟨V₂, hV₂, hLV₂, h2V₂⟩ :=
    normal_exists_closure_subset hL₁ (isClosed_closure.isOpen_compl.inter hU₁)
      (subset_inter (subset_compl_iff_disjoint_left.mpr hV₀L₁) <| sdiff_subset.trans hKU₁)
  obtain ⟨V₁, hV₁, hLV₁, hV₁₂⟩ := normal_exists_closure_subset hL₁ hV₂ hLV₂
  rw [subset_inter_iff, subset_compl_iff_disjoint_left] at h2V₂
  rcases h2V₂ with ⟨hV₀₂, hV₂U₁⟩
  have hVU₁ : V₁ ⊆ U₁ := subset_closure.trans (hV₁₂.trans <| subset_closure.trans hV₂U₁)
  have hdisj : Disjoint (closure V₀ ∪ V₂ᶜ) (closure V₁) := by
    refine Disjoint.union_left (hV₀₂.mono_right (hV₁₂.trans subset_closure)) ?_
    rw [← subset_compl_iff_disjoint_left, compl_compl]; exact hV₁₂
  refine ⟨V₀ ∪ U₁ ∩ U₀ ∪ V₁, ((hV₀.union <| hU₁.inter hU₀).union hV₁).mem_nhdsSet.mpr ?_, ?_⟩
  · refine union_subset (hKV₀.trans <| subset_union_left.trans <| subset_union_left) ?_
    rw [← inter_union_sdiff K₁];
    exact union_subset_union ((inter_subset_inter_left _ hKU₁).trans <| subset_union_right) hLV₁
  obtain ⟨ρ, h0ρ, h1ρ, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_closure.union hV₂.isClosed_compl)
      isClosed_closure hdisj
  let h₀' : SurroundingFamilyIn g b γ₀ (U₁ ∩ U₀) Ω := h₀.mono inter_subset_right
  let h₁' : SurroundingFamilyIn g b γ₁ (U₁ ∩ U₀) Ω := h₁.mono inter_subset_left
  let γ := sfHomotopy h₀'.to_sf h₁'.to_sf
  have hγ : ∀ τ, SurroundingFamilyIn g b (γ τ) (U₁ ∩ U₀) Ω := surroundingFamilyIn_sfHomotopy h₀' h₁'
  have heq1 : ∀ x ∈ closure V₀ ∪ V₂ᶜ, γ (ρ x) x = γ₀ x := by
    intro x hx
    simp_rw [γ, h0ρ hx, Pi.zero_apply, sfHomotopy_zero]
  have heq2 : ∀ x ∈ V₀, γ (ρ x) x = γ₀ x := fun x hx ↦
    heq1 x (subset_closure.trans subset_union_left hx)
  refine ⟨fun x t ↦ γ (ρ x) x t, ?_, ?_, ?_⟩
  · refine ⟨⟨fun x ↦ (hγ <| ρ x).base x, fun x ↦ (hγ <| ρ x).t₀ x, fun x ↦ (hγ <| ρ x).projI x,
      ?_, ?_⟩, ?_⟩
    · rintro x ((hx | hx) | hx)
      · simp_rw [heq2 x hx, h₀.surrounds x (hVU₀ <| subset_closure hx)]
      · simp_rw [γ]
        exact (hγ <| ρ x).surrounds x hx
      · simp_rw [γ, h1ρ (subset_closure hx), Pi.one_apply, sfHomotopy_one, h₁.surrounds x (hVU₁ hx)]
    · fun_prop
    · intro x hx t ht s _; refine sfHomotopy_in' _ _ _ id _ hx ht ?_ ?_
      · intro x hx t _ht s hρx; refine h₀.val_in ?_; rcases hx with ((hx | ⟨-, hx⟩) | hx)
        · exact (subset_closure.trans hVU₀) hx
        · exact hx
        · exact (hρx <| h1ρ <| subset_closure hx).elim
      · intro x hx t _ht s hρx; refine h₁.val_in ?_; rcases hx with ((hx | ⟨hx, -⟩) | hx)
        · exact (hρx <| h0ρ <| subset_closure.trans subset_union_left hx).elim
        · exact hx
        · exact hVU₁ hx
  · exact eventually_of_mem (hV₀.mem_nhdsSet.mpr hKV₀) heq2
  · exact eventually_of_mem
      (isClosed_closure.isOpen_compl.mem_nhdsSet.mpr <| compl_subset_compl.mpr hV₂U₁)
      fun x hx ↦ heq1 x <| mem_union_right _ <| compl_subset_compl.mpr subset_closure hx

end extend_loops

variable (g b Ω)
omit [NormedSpace ℝ E]

structure SurroundingFamilyGerm (x : E) (φ : Germ (𝓝 x) (ℝ → Loop F)) : Prop where
  Surrounds : (φ.value 1).Surrounds <| g x
  val_in' : ∀ t ∈ I, ∀ s ∈ I, (x, φ.value t s) ∈ Ω

variable {g b Ω}

/-
The following proof is slightly tedious because the definition of `surroundingFamilyIn`
splits weirdly into `SurroundingFamily` which includes one condition on `C`
and one extra condition on `C` instead of putting everything which does not depend on `C`
on one side and the two conditions depending on `C` on the other side as we do here.
-/
theorem surroundingFamilyIn_iff_germ {γ : E → ℝ → Loop F} :
    SurroundingFamilyIn g b γ C Ω ↔
      (∀ x, LoopFamilyGerm b x γ) ∧ ∀ x ∈ C, SurroundingFamilyGerm g Ω x γ := by
  constructor
  · rintro ⟨⟨base, t₀, projI, family_surrounds, family_cont⟩, H⟩
    exact ⟨fun x ↦ ⟨base x, t₀ x, projI x, fun t s ↦ family_cont.continuousAt⟩, fun x x_in ↦
      ⟨family_surrounds x x_in, H x x_in⟩⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨fun x ↦ (h x).base, fun x ↦ (h x).t₀, fun x ↦ (h x).projI,
        fun x hx ↦ (h' x hx).Surrounds, ?_⟩,
      fun x hx ↦ (h' x hx).val_in'⟩
    apply continuous_iff_continuousAt.mpr
    rintro ⟨x, t, s⟩
    apply (h x).cont

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [SecondCountableTopology E]

theorem exists_surrounding_loops (hK : IsClosed K) (hΩ_op : IsOpen Ω) (hg : ∀ x, ContinuousAt g x)
    (hb : Continuous b)
    (hconv : ∀ x, g x ∈ convexHull ℝ (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x))
    {γ₀ : E → ℝ → Loop F} (hγ₀_surr : ∃ V ∈ 𝓝ˢ K, SurroundingFamilyIn g b γ₀ V Ω) :
    ∃ γ : E → ℝ → Loop F, SurroundingFamilyIn g b γ univ Ω ∧ ∀ᶠ x in 𝓝ˢ K, γ x = γ₀ x := by
  rcases hγ₀_surr with ⟨V, V_in, hV⟩
  obtain ⟨hV, h'V⟩ := surroundingFamilyIn_iff_germ.mp hV
  simp only [surroundingFamilyIn_iff_germ, mem_univ, forall_true_left, ← forall_and]
  apply
    relative_inductive_construction_of_loc (LoopFamilyGerm b) (SurroundingFamilyGerm g Ω) hK hV
      (mem_of_superset V_in h'V)
  · intro x
    rcases local_loops ⟨univ, univ_mem, by simp only [preimage_univ, inter_univ, hΩ_op]⟩ (hg x) hb
        (hconv x) with
      ⟨γ, U, U_in, H⟩
    obtain ⟨H, H'⟩ := surroundingFamilyIn_iff_germ.mp H
    exact ⟨γ, H, mem_of_superset U_in H'⟩
  · intro U₁ U₂ K₁ K₂ γ₁ γ₂ hU₁ hU₂ hK₁ hK₂ hKU₁ hKU₂ hγ₁ hγ₂ h'γ₁ h'γ₂
    rcases extend_loops hU₁ hU₂ hK₁.isClosed hK₂.isClosed hKU₁ hKU₂
      (surroundingFamilyIn_iff_germ.mpr ⟨hγ₁, h'γ₁⟩)
      (surroundingFamilyIn_iff_germ.mpr ⟨hγ₂, h'γ₂⟩) with ⟨U, U_in, γ, H, H''⟩
    rcases surroundingFamilyIn_iff_germ.mp H with ⟨H, H'⟩
    exact ⟨γ, H, mem_of_superset U_in H', Eventually.union_nhdsSet.mpr H''⟩
end
end
end

section
-- module Solutions.OAIQ249_SI.Loops_Exists
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

section

noncomputable section

open Set Function Int Metric Filter Real MeasureTheory
open scoped  MeasureTheory.Measure Topology unitInterval ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  {g b : E → F} {Ω : Set (E × F)} {U K C : Set E}

variable [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exist_loops_aux1 (hK : IsCompact K) (hΩ_op : IsOpen Ω) (hb : 𝒞 ∞ b)
    (hgK : ∀ᶠ x near K, g x = b x)
    (hconv : ∀ x, g x ∈ hull (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x)) :
    ∃ γ : E → ℝ → Loop F,
      ∃ V ∈ 𝓝ˢ K,
        ∃ ε > 0,
          SurroundingFamilyIn g b γ V Ω ∧
            (∀ x ∈ V, ball (x, b x) (ε + ε) ⊆ Ω) ∧ ∀ x ∈ V, ∀ (t s), dist (γ x t s) (b x) < ε := by
  have b_in : ∀ x, (x, b x) ∈ Ω := fun x ↦
    (connectedComponentIn_nonempty_iff.mp (convexHull_nonempty_iff.mp ⟨g x, hconv x⟩) : _)
  -- we could probably get away with something simpler to get γ₀.
  obtain
    ⟨γ₀, hγ₀_cont, hγ₀, h2γ₀, h3γ₀, -, hγ₀_surr⟩ :=-- γ₀ is γ* in notes
      surrounding_loop_of_convexHull
      isOpen_univ isConnected_univ (by rw [convexHull_univ]; exact mem_univ 0) (mem_univ (0 : F))
  obtain ⟨ε₀, hε₀, V, hV, hεΩ⟩ :=
    hK.exists_thickening_image_subset hΩ_op
      (fun x hx ↦ (continuous_id.prodMk hb.continuous).continuousAt) fun x _ ↦ b_in x
  let range_γ₀ := (fun i : ℝ × ℝ ↦ ‖γ₀ i.1 i.2‖) '' I ×ˢ I
  have h4γ₀ : BddAbove range_γ₀ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image (by fun_prop)
  have h0 : 0 < 1 + sSup range_γ₀ :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (le_csSup_of_le h4γ₀
          (mem_image_of_mem _ <| mk_mem_prod unitInterval.zero_mem unitInterval.zero_mem) <|
        norm_nonneg _)
  generalize h0ε₁ : ε₀ / 2 = ε₁
  have hε₁ : 0 < ε₁ := h0ε₁ ▸ div_pos hε₀ two_pos
  let ε := ε₁ / (1 + sSup range_γ₀)
  have hε : 0 < ε := div_pos hε₁ h0
  have h2ε : ∀ t s : ℝ, ‖ε • γ₀ t s‖ < ε₁ := by
    intro t s
    simp only [ε, norm_smul, Real.norm_eq_abs, abs_eq_self.mpr hε.le, mul_comm_div]
    refine lt_of_lt_of_le ?_ (mul_one _).le
    rw [mul_lt_mul_iff_right₀ hε₁, div_lt_one h0]
    refine (zero_add _).symm.le.trans_lt (add_lt_add_of_lt_of_le zero_lt_one (le_csSup h4γ₀ ?_))
    rw [← Loop.fract_eq, ← h3γ₀]
    exact mem_image_of_mem _ (mk_mem_prod projI_mem_Icc <| unitInterval.fract_mem _)
  let γ₁ : E → ℝ → Loop F := fun x t ↦ (γ₀ t).transform fun y ↦ b x + ε • y
  -- `γ₁ x` is `γₓ` in notes
  refine ⟨γ₁, ?_⟩
  have hbV : ∀ᶠ x near K, x ∈ V := hV
  have h1 : ∀ x ∈ V, ∀ (_t _s : ℝ), ball (x, b x) (ε₁ + ε₁) ⊆ Ω := by
    intro x hx _t _s
    simp only [← h0ε₁, add_halves]
    exact (ball_subset_thickening (mem_image_of_mem _ hx) _).trans hεΩ
  refine ⟨_, hgK.and hbV, ε₁, hε₁, ⟨⟨by simp [γ₁, hγ₀], by simp [γ₁, h2γ₀],
    ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro x t s; simp [γ₁, h3γ₀]
  · rintro x ⟨hx, -⟩; simp_rw [γ₁, hx]
    exact (hγ₀_surr.smul0 hε.ne').vadd0
  · exact hb.continuous.fst'.add (continuous_const.smul <| hγ₀_cont.snd')
  · rintro x ⟨-, hx⟩ t _ht s _hs
    have : ‖ε • γ₀ t s‖ < ε₀ := (h2ε t s).trans (h0ε₁ ▸ half_lt_self hε₀)
    exact h1 x hx t s (by simpa [γ₁, ← h0ε₁])
  · intro x hx
    rw [← h0ε₁, add_halves]
    exact (ball_subset_thickening (mem_image_of_mem _ hx.2) _).trans hεΩ
  · rintro x ⟨-, -⟩ t s
    simp [γ₁, h2ε]

attribute [fun_prop] Continuous.infDist Continuous.if_const

/- Some remarks about `exist_loops_aux2`:
  `δ`: loop after smoothing
  `γ`: loop before smoothing (defined on all of `E`)
  Requirements:
  (0) `δ x t` is a loop
  (1) `δ` lands in `Ω`
  (2) `δ` has the correct values: for `s = 0` and `t = 0` it should be `b`
  (3) `δ` should be constant on `t ≤ 0` and for `t ≥ 1`.
  (4) `δ x 1` surrounds `g x`.
  (5) Near `K`, the line connecting `b` and `δ` lies in `Ω`

  Strategy:
  (a) We need `ε₁` satisfying the following conditions:
  (a1) We need to ensure that an `ε₁ x`-ball around `(x, δ x s t)` lies in `Ω` for some
    continuous `ε₁`.
  (a4) Furthermore, `ε₁` should be small enough so that any function with that
    distance from `γ` still surrounds `g`, using `SurroundingFamily.surrounds_of_close`.
  (a5): `ε₁ x < ε₀` (obtained from `exist_loops_aux1`)
  (b) Replace `γ x t s` by `γ x (linearReparam t) (linearReparam s)`.
  (e) Let `δ' x` be a family of loops that is at most `ε₁` away from `γ` using
    `exists_smooth_and_eqOn`. Since `γ` is smooth near `s ∈ ℤ` and `t ≤ 0` we can also
    ensure that `δ' = γ` for those values (*).
    Now let `δ x t s = δ' x (smoothTransition t) (fract s)`
    We immediately get (0) and (3). We get (2) by (*).
    This is still smooth, since `δ'` is doesn't depend on `s` near `s ∈ ℤ`.
  (f) (a1) gives (1), (a4) gives (4) and (a5) gives (5).

  Note: to ensure (2) the reparamerization strategy that was originally in the blueprint
  (ensuring that `γ` is locally constant in the `t` and `s` directions)
  didn't work. Indeed it needed to take the convolution in the `x`-direction,
  meaning that the value won't stay the same, since `γ` is not constant in the `x`-direction.
-/
theorem exist_loops_aux2 [FiniteDimensional ℝ E] (hK : IsCompact K) (hΩ_op : IsOpen Ω) (hg : 𝒞 ∞ g)
    (hb : 𝒞 ∞ b) (hgK : ∀ᶠ x near K, g x = b x)
    (hconv : ∀ x, g x ∈ hull (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x)) :
    ∃ γ : E → ℝ → Loop F,
      SurroundingFamilyIn g b γ univ Ω ∧
        𝒞 ∞ ↿γ ∧ ∀ᶠ x near K, ∀ t s, closedBall (x, b x) (dist (γ x t s) (b x)) ⊆ Ω := by
  obtain ⟨γ₁, V, hV, ε₀, hε₀, hγ₁, hΩ, h2γ₁⟩ := exist_loops_aux1 hK hΩ_op hb hgK hconv
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK.isClosed hΩ_op (fun x ↦ hg.continuous.continuousAt) hb.continuous
      (fun x ↦ hconv x) ⟨V, hV, hγ₁⟩
  let γ₃ : E → ℝ → Loop F := fun x t ↦ (γ₂ x (linearReparam t)).reparam linearReparam
  have hγ₃ : SurroundingFamilyIn g b γ₃ univ Ω := hγ₂.reparam
  obtain ⟨ε₁, hε₁, hcε₁, hγε₁⟩ := hγ₃.to_sf.surrounds_of_close_univ hg.continuous
  classical
  let f : E → ℝ × ℝ → ℝ := fun x y ↦ if Ωᶜ.Nonempty then infDist (x, γ₃ x y.1 y.2) (Ωᶜ) else 1
  have hI : IsCompact (I ×ˢ I) := isCompact_Icc.prod isCompact_Icc
  have h1f : Continuous ↿f := (continuous_fst.prodMk hγ₃.cont).infDist.if_const _ continuous_const
  have h3f {x y} : 0 < f x y := by
    by_cases hΩ : Ωᶜ.Nonempty
    · simp_rw [f, ite_eq_left hΩ, ← hΩ_op.isClosed_compl.notMem_iff_infDist_pos hΩ,
        notMem_compl_iff, hγ₃.val_in (mem_univ _)]
    · simp_rw [f, ite_eq_right hΩ, zero_lt_one]
  let ε₂ : E → ℝ := fun x ↦ min (min ε₀ (ε₁ x)) (sInf (f x '' I ×ˢ I))
  have hcε₂ : Continuous ε₂ := by
    have := hI.continuous_sInf h1f; unfold ε₂; fun_prop
  have hε₂ : ∀ {x}, 0 < ε₂ x := fun {x} ↦
    lt_min (lt_min hε₀ (hε₁ x))
      ((hI.lt_sInf_iff_of_continuous
          ((nonempty_Icc.mpr zero_le_one).prod (nonempty_Icc.mpr zero_le_one)) (by fun_prop) _).mpr
        fun x _ ↦ h3f)
  let γ₄ := ↿γ₃
  have h0γ₄ : ∀ x t s, γ₄ (x, t, s) = γ₃ x t s := fun x t s ↦ rfl
  let C₁ : Set ℝ := Iic (5⁻¹ : ℝ) ∪ Ici (4 / 5)
  have h0C₁ : (0 : ℝ) ∈ C₁ := Or.inl (by rw [mem_Iic]; norm_num1)
  have h2C₁ : ∀ (s : ℝ) (hs : fract s = 0), fract ⁻¹' C₁ ∈ 𝓝 s := by
    refine fun s hs ↦ fract_preimage_mem_nhds ?_ fun _ ↦ ?_
    · exact hs ▸ mem_of_superset (Iic_mem_nhds <| by norm_num) subset_union_left
    · exact mem_of_superset (Ici_mem_nhds <| by norm_num) subset_union_right
  let C : Set (E × ℝ × ℝ) := (fun x ↦ x.2.1) ⁻¹' Iic (5⁻¹ : ℝ) ∪ (fun x ↦ fract x.2.2) ⁻¹' C₁
  have hC : IsClosed C := by
    refine (isClosed_Iic.preimage continuous_snd.fst).union ?_
    refine ((isClosed_Iic.union isClosed_Ici).preimage_fract ?_).preimage continuous_snd.snd
    exact fun _ ↦ Or.inl (show (0 : ℝ) ≤ 5⁻¹ by norm_num)
  let U₁ : Set ℝ := Iio (4⁻¹ : ℝ) ∪ Ioi (3 / 4)
  let U : Set (E × ℝ × ℝ) := (fun x ↦ x.2.1) ⁻¹' Iio (4⁻¹ : ℝ) ∪ (fun x ↦ fract x.2.2) ⁻¹' U₁
  have hUC : U ∈ 𝓝ˢ C := by
    have hU : IsOpen U := by
      refine (isOpen_Iio.preimage continuous_snd.fst).union ?_
      refine ((isOpen_Iio.union isOpen_Ioi).preimage_fract ?_).preimage continuous_snd.snd
      exact fun _ ↦ Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
    -- Porting note: the following four lines were
    /-
    exact hU.mem_nhds_set.mpr (union_subset_union (λ x hx, lt_of_le_of_lt hx (by norm_num)) $
      union_subset_union (λ x hx, lt_of_le_of_lt hx (by norm_num))
      (λ x hx, lt_of_lt_of_le (by norm_num) hx))
    in Lean 3.
    -/
    apply hU.mem_nhdsSet.mpr
    refine (union_subset_union fun (x : E × ℝ × ℝ)
      (hx : x.2.1 ≤ 5⁻¹) ↦ lt_of_le_of_lt hx (by norm_num)) ?_
    refine union_subset_union (fun (x : E × ℝ × ℝ)
      (hx : fract x.2.2 ≤ 5⁻¹) ↦ lt_of_le_of_lt hx (by norm_num)) ?_
    exact fun x hx ↦ lt_of_lt_of_le (by norm_num : (3 / 4 : ℝ) < 4 / 5) hx
  have h2γ₄ : EqOn γ₄ (fun x ↦ b x.1) U := by
    rintro ⟨x, t, s⟩ hxts
    simp_rw [h0γ₄, γ₃, Loop.reparam_apply]
    obtain (ht | hs) := hxts
    · exact hγ₂.to_sf.t_le_zero_eq_b x (linearReparam s) (linearReparam_nonpos (le_of_lt ht))
    · rw [← Loop.fract_eq, fract_linearReparam_eq_zero, hγ₂.base]
      exact Or.imp le_of_lt le_of_lt hs
  have h3γ₄ : ContDiffOn ℝ ∞ γ₄ U := hb.fst'.contDiffOn.congr h2γ₄
  obtain ⟨γ₅, hγ₅, hγ₅₄, hγ₅C⟩ :=
    exists_smooth_and_eqOn hγ₃.cont hcε₂.fst' (fun x ↦ hε₂) hC ⟨U, hUC, h3γ₄⟩
  let γ : E → ℝ → Loop F := fun x t ↦
    ⟨fun s ↦ γ₅ (x, smoothTransition t, fract s), fun s ↦ by rw [fract_add_one s]⟩
  have hγ : 𝒞 ∞ ↿γ := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨x, t, s⟩; by_cases hs : fract s = 0
    · have : (fun x ↦ γ x.1 x.2.1 x.2.2) =ᶠ[𝓝 (x, t, s)] fun x ↦ b x.1 := by
        have :
          (fun x : E × ℝ × ℝ ↦ (x.1, smoothTransition x.2.1, fract x.2.2)) ⁻¹' C ∈ 𝓝 (x, t, s) := by
          simp_rw [C, preimage_union, preimage_preimage, fract_fract]
          refine mem_of_superset ?_ subset_union_right
          refine continuousAt_id.snd'.snd'.preimage_mem_nhds (h2C₁ s hs)
        filter_upwards [this] with x hx
        exact (hγ₅C hx).trans
          (h2γ₄ <| (subset_interior_iff_mem_nhdsSet.mpr hUC).trans interior_subset hx)
      exact hb.fst'.contDiffAt.congr_of_eventuallyEq this
    · exact (hγ₅.comp₃ contDiff_fst smoothTransition.contDiff.fst'.snd' <|
          contDiff_snd.snd'.sub contDiff_const).contDiffAt.congr_of_eventuallyEq
        ((EventuallyEq.rfl.prodMk <| EventuallyEq.rfl.prodMk <|
              (fract_eventuallyEq hs).comp_tendsto continuousAt_id.snd'.snd').fun_comp ↿γ₅)
  refine ⟨γ, ⟨⟨?_, ?_, ?_, ?_, hγ.continuous⟩, ?_⟩, hγ, ?_⟩
  · intro x t
    simp_rw [γ, fract_zero]
    rw [hγ₅C]
    · exact hγ₃.base x _
    · exact Or.inr (by rw [mem_preimage, fract_zero]; exact h0C₁)
  · intro x s
    simp_rw [γ, smoothTransition.zero_of_nonpos le_rfl]
    rw [hγ₅C]
    · exact hγ₃.t₀ x (fract s)
    · exact Or.inl (show (0 : ℝ) ≤ 5⁻¹ by norm_num)
  · intro x t s
    simp_rw [γ, smoothTransition_projI]
  · rintro x -
    refine hγε₁ _ _ fun s ↦ ?_
    simp_rw [← (γ₃ x 1).fract_eq s, γ, smoothTransition.one_of_one_le le_rfl]
    exact (hγ₅₄ (x, 1, fract s)).trans_le ((min_le_left _ _).trans <| min_le_right _ _)
  · rintro x - t - s -; rw [← notMem_compl_iff]
    by_cases hΩ : Ωᶜ.Nonempty; swap
    · rw [not_nonempty_iff_eq_empty] at hΩ; rw [hΩ]; apply notMem_empty
    refine notMem_of_dist_lt_infDist (x := ?_) ?_
    · exact (x, γ₃ x (smoothTransition t) (fract s))
    · rw [dist_comm, dist_prod_same_left]
      refine (hγ₅₄ (x, _, fract s)).trans_le ((min_le_right _ _).trans <| csInf_le ?_ ?_)
      · exact (isCompact_Icc.prod isCompact_Icc).bddBelow_image (by fun_prop)
      · rw [← hγ₃.projI]
        simp_rw [f, ite_eq_left hΩ]
        apply mem_image_of_mem _ (mk_mem_prod projI_mem_Icc (unitInterval.fract_mem s))
  · refine eventually_of_mem (Filter.inter_mem hV hγ₂₁) fun x hx t s ↦ ?_
    refine (closedBall_subset_ball ?_).trans (hΩ x hx.1)
    refine (dist_triangle ..).trans_lt (add_lt_add_of_le_of_lt
      ((hγ₅₄ (x, _, fract s)).le.trans <| (min_le_left _ _).trans <| min_le_left ..) ?_)
    simp_rw [γ₃, HasUncurry.uncurry, Loop.reparam_apply, show γ₂ x = γ₁ x from hx.2]
    exact h2γ₁ x hx.1 ..

variable (g b Ω U K)

variable {g b Ω U K}

theorem exist_loops [FiniteDimensional ℝ E] (hK : IsCompact K) (hΩ_op : IsOpen Ω) (hg : 𝒞 ∞ g)
    (hb : 𝒞 ∞ b) (hgK : ∀ᶠ x near K, g x = b x)
    (hconv : ∀ x, g x ∈ hull (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x)) :
    ∃ γ : ℝ → E → Loop F, NiceLoop g b Ω K γ := by
  obtain ⟨γ₁, hγ₁, hsγ₁, h2γ₁⟩ := exist_loops_aux2 hK hΩ_op hg hb hgK hconv
  let γ₂ : SmoothSurroundingFamily g :=
    ⟨hg, fun x ↦ γ₁ x 1, hsγ₁.comp₃ contDiff_fst contDiff_const contDiff_snd, fun x ↦
      hγ₁.surrounds x (mem_univ _)⟩
  classical
  let γ₃ : ℝ → E → Loop F := fun t x ↦ (γ₁ x t).reparam <| (γ₂.reparametrize x).equivariantMap
  have hγ₃ : 𝒞 ∞ ↿γ₃ := hsγ₁.comp₃ contDiff_snd.fst contDiff_fst γ₂.reparametrize_smooth.snd'
  obtain ⟨χ, hχ, h1χ, h0χ, h2χ⟩ :=
    exists_contDiff_one_nhds_of_interior hK.isClosed
      (subset_interior_iff_mem_nhdsSet.mpr <| hgK.and h2γ₁)
  simp_rw [← or_iff_not_imp_left] at h0χ
  let γ : ℝ → E → Loop F := fun t x ↦ χ x • Loop.const (b x) + (1 - χ x) • γ₃ t x
  have h1γ : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x := by
    intro x t ht; ext s;
    simp [γ, γ₃, hγ₁.to_sf.t_le_zero _ _ ht]
  have h2γ : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x := by
    intro x t ht; ext s
    simp [γ, γ₃, hγ₁.to_sf.t_ge_one _ _ ht]
  refine ⟨γ, h1γ, h2γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t
    simp [γ, γ₃, hγ₁.t₀]
  · intro x t
    simp [γ, γ₃, hγ₁.base]
  · intro x
    have h1 : IntervalIntegrable (χ x • Loop.const (b x) : Loop F) volume 0 1 := by
      change IntervalIntegrable (fun _ ↦ χ x • b x) volume (0 : ℝ) (1 : ℝ)
      exact intervalIntegrable_const
    have h2 : IntervalIntegrable ((1 - χ x) • γ₃ 1 x : Loop F) volume 0 1 :=
      ((hγ₃.comp₃ contDiff_const contDiff_const contDiff_id).continuous.intervalIntegrable ..).smul
        _
    have h3 : (γ₃ 1 x).average = g x := γ₂.reparametrize_average x
    simp only [h1, h2, Loop.average_add, Loop.average_smul, Loop.average_const, h3, γ, γ₃]
    rcases h0χ x with (⟨hx, -⟩ | hx)
    · rw [hx, smul_add_one_sub_smul]
    · simp [hx]
  · intro x t s
    have : ∀ (P : F → Prop) (t), (∀ t ∈ I, P (γ t x s)) → P (γ t x s) := by
      intro P t hP
      rcases le_total 0 t with (h1t | h1t)
      · rcases le_total t 1 with (h2t | h2t)
        · exact hP t ⟨h1t, h2t⟩
        · rw [h2γ x t h2t]; exact hP 1 ⟨zero_le_one, le_rfl⟩
      · rw [h1γ x t h1t]; exact hP 0 ⟨le_rfl, zero_le_one⟩
    refine this (fun y ↦ (x, y) ∈ Ω) t fun t _ht ↦ ?_
    rcases h0χ x with (⟨_hx, h2x⟩ | hx)
    · refine h2x t (γ₂.reparametrize x s) ?_
      simp [γ, γ₃, dist_smul_add_one_sub_smul_le (h2χ x)]
    · simp only [hx, zero_smul, sub_zero, one_smul, zero_add, γ]
      exact hγ₁.val_in (mem_univ _)
  · exact (hχ.fst'.snd'.smul hb.fst'.snd').add ((contDiff_const.sub hχ.fst'.snd').smul hγ₃)
  · exact h1χ.mono fun x (hx : χ x = 1) ↦ by simp [γ, hx]
end
end
end

section
-- module Solutions.OAIQ249_SI.Local_HPrinciple
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

/-!
# Local h-principle for open and ample relations

This file proves `lem:h_principle_open_ample_loc` from the blueprint. This is the local
version of the h-principle for open and ample relations. The proof brings together the
main result `exist_loops` from the loop folder (Chapter 1 in the blueprint) and
the corrugation technique.

One formalization issue is that the whole construction carries around a lot of data.
On paper it is easy to state one lemma listing once all this data and proving many properties.
Here it is more convenient to give each property its own lemma so carrying around data,
assumptions and constructions requires some planning. Our way to mitigate this issue
is to use two ad-hoc structures `Landscape` and `StepLandscape` which partly bundle
all this.

The `Landscape` structure record three sets in a vector space, a closed
set `C` and two nested compact sets `K₀` and `K₁`. This is the ambient data for
the local h-principle result. We call this partly bundled because it doesn't include
the data of the formal solution we want to improve. Instead we have a Prop-valued
structure `Landscape.accepts` that takes a landscape and a formal solution and assert
some compatibility conditions. There are four conditions, which is already enough
motivation to introduce a structure instead of one definition using the logical
conjunction operator that would lead to awkward and error prone access to the
individual conditions.

The proof of this proposition involves an induction on a flag of subspaces (nested
subspaces of increasing dimensions). For the purpose of this induction we use
a second structure `StepLandscape` that extends `Landscape` with two more pieces
of data, a subspace and a dual pair, and a compatibility condition, namely the subspace
has to be in the hyperplane defined by the dual pair.

In this setup, given `(L : StepLandscape E) {𝓕 : FormalSol R} (h : L.accepts R 𝓕)`,
the loop family constructed by Chapter 2 is `L.loop h`. Together with corrugation,
it is used to build `L.improveStep h` which is the homotopy of 1-jet sections improving
the formal solution `𝓕` in that step of the main inductive proof. A rather long series of
lemmas prove all the required properties of that homotopy, corresponding to
lemma `lem:integration_step` from the blueprint.

The inductive proof itself is the proof of `RelLoc.FormalSol.improve`.
Here all conclusions are stated at once this the induction requires to know about each
of them to proceed to the next step. We could have introduced one more ad-hoc structure
to record those conclusion but this isn't needed (at least in that Chapter) since we
need to access its components only once.

-/

section


noncomputable section

open scoped unitInterval Filter Topology ContDiff

open Filter Set RelLoc

open LinearMap (ker)

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

section ImproveStep

/-!
## Improvement step

This section proves `lem:integration_step`.
-/


/-- The setup for a one-step improvement towards a local h-principle is two compact subsets
`K₀ ⊆ K₁` in `E` with `K₀ ⊆ interior K₁` and a closed subset `C`
together with a dual pair `p` and a subspace `E'` of the corresponding hyperplane `ker p.π`.
-/
structure StepLandscape extends Landscape E where
  E' : Submodule ℝ E
  p : DualPair E
  hEp : E' ≤ p.π.ker

variable {E}

variable (R : RelLoc E F)

namespace StepLandscape

/-- A one-step improvement landscape accepts a formal solution if it can improve it. -/
structure Accepts (L : StepLandscape E) (𝓕 : JetSec E F) : Prop where
  h_op : IsOpen R
  hK₀ : ∀ᶠ x near L.K₀, 𝓕.IsPartHolonomicAt L.E' x
  hShort : ∀ x, 𝓕.IsShortAt R L.p x
  hC : ∀ᶠ x near L.C, 𝓕.IsHolonomicAt x

/-- The union of all slices of `R` corresponding to `𝓕`. -/
def Ω (L : StepLandscape E) (𝓕 : JetSec E F) : Set (E × F) :=
  {p | p.2 ∈ 𝓕.sliceAt R L.p p.1}

-- ⋃ x, ({x} : Set E) ×ˢ (connectedComponentIn (𝓕.sliceAt R L.p x) <| 𝓕.φ x L.p.v)
/-- The linear form in a `StepLandscape`, coming from the underlying dual pair. -/
def π (L : StepLandscape E) : E →L[ℝ] ℝ :=
  L.p.π

/-- The vector in a `StepLandscape`, coming from the underlying dual pair. -/
def v (L : StepLandscape E) : E :=
  L.p.v

/-- One more compact set in the landscape: K₁ ∩ C, needed as an input to the
loop construction. -/
def K (L : StepLandscape E) : Set E :=
  L.K₁ ∩ L.C

/-- The base function for the loop family associated in any jet section in a
step landscape. -/
def b (L : StepLandscape E) (𝓕 : JetSec E F) : E → F := fun x ↦ 𝓕.φ x L.v

/-- The desired average for the loop family associated in any jet section in a
step landscape. -/
def g (L : StepLandscape E) (𝓕 : JetSec E F) : E → F := fun x ↦ D 𝓕.f x L.v

theorem isCompact_K (L : StepLandscape E) : IsCompact L.K :=
  L.hK₁.inter_right L.hC

variable {R}

theorem Accepts.open [FiniteDimensional ℝ E] {L : StepLandscape E} {𝓕 : JetSec E F}
    (h : L.Accepts R 𝓕) : IsOpen (L.Ω R 𝓕) := by
  set ψ : E × F → OneJet E F := fun p ↦ (p.1, 𝓕.f p.1, L.p.update (𝓕.φ p.1) p.2)
  change IsOpen {p : E × F | ψ p ∈ R}
  apply IsOpen.preimage _ h.h_op
  apply continuous_fst.prodMk (𝓕.f_diff.continuous.fst'.prodMk _)
  exact L.p.continuous_update 𝓕.φ_diff.continuous.fst' continuous_snd

theorem smooth_b (L : StepLandscape E) (𝓕 : JetSec E F) : 𝒞 ∞ (L.b 𝓕) :=
  (ContinuousLinearMap.apply ℝ F L.v).contDiff.comp 𝓕.φ_diff

theorem smooth_g (L : StepLandscape E) (𝓕 : JetSec E F) : 𝒞 ∞ (L.g 𝓕) :=
  (ContinuousLinearMap.apply ℝ F L.v).contDiff.comp (contDiff_infty_iff_fderiv.mp 𝓕.f_diff).2

theorem Accepts.rel {L : StepLandscape E} {𝓕 : JetSec E F} (h : L.Accepts R 𝓕) :
    ∀ᶠ x : E near L.K, (L.g 𝓕) x = (L.b 𝓕) x := by
  apply (h.hC.filter_mono <| monotone_nhdsSet inter_subset_right).mono
  intro x hx
  dsimp [JetSec.IsHolonomicAt] at hx
  dsimp [StepLandscape.g, StepLandscape.b]
  rw [hx]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

open scoped Borelize
variable (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕)
-- Porting note: the elaboration smiley below was not necessary in Lean 3.
/-- The loop family to use in some landscape to improve a formal solution. -/
def loop (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) : ℝ → E → Loop F :=
  Classical.choose <|
    (exist_loops L.isCompact_K h.open (L.smooth_g 𝓕) (L.smooth_b 𝓕):) h.rel h.hShort

theorem nice (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) :
    NiceLoop (L.g ↑𝓕) (L.b ↑𝓕) (Ω R L 𝓕) L.K (L.loop h) :=
  Classical.choose_spec <|
    (exist_loops L.isCompact_K h.open (L.smooth_g 𝓕) (L.smooth_b 𝓕):) h.rel h.hShort

theorem loop_smooth (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) : 𝒞 ∞ ↿(L.loop h) :=
  (L.nice h).smooth

theorem loop_smooth' (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) {t : G → ℝ}
    (ht : 𝒞 ∞ t) {s : G → ℝ} (hs : 𝒞 ∞ s) {x : G → E} (hx : 𝒞 ∞ x) :
    𝒞 ∞ fun g ↦ L.loop h (t g) (x g) (s g) :=
  (L.loop_smooth h).comp (ht.prodMk <| hx.prodMk hs)

variable (L : StepLandscape E)

/-- The cut-off function associated to a step landscape, equal to one near K₀ and
zero outside K₁. -/
def ρ (L : StepLandscape E) : E → ℝ :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.isClosed L.h₀₁).choose

theorem ρ_smooth (L : StepLandscape E) : 𝒞 ∞ L.ρ :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.isClosed L.h₀₁).choose_spec.1

/-- Homotopy of formal solutions obtained by corrugation in the direction of `p : dualPair E`
in some landscape to improve a formal solution `𝓕` from being `L.E'`-holonomic to
`L.E' ⊔ span {p.v}`-holonomic near `L.K₀`.
-/
def improveStep {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (N : ℝ) : HtpyJetSec E F where
  f t x := 𝓕.f x + (smoothStep t * L.ρ x) • corrugation L.π N (L.loop h t) x
  f_diff :=
    𝓕.f_diff.snd'.add <|
      (smoothStep.smooth.fst'.mul L.ρ_smooth.snd').smul <|
        corrugation.contDiff' _ N (L.loop_smooth h) contDiff_snd contDiff_fst
  φ t x :=
    L.p.update (𝓕.φ x) (L.loop h (smoothStep t * L.ρ x) x <| N * L.π x) +
      (smoothStep t * L.ρ x) • corrugation.remainder L.p.π N (L.loop h 1) x
  φ_diff := by
    apply ContDiff.add
    · apply L.p.smooth_update
      · exact 𝓕.φ_diff.snd'
      apply L.loop_smooth'
      · exact smoothStep.smooth.fst'.mul L.ρ_smooth.snd'
      · apply contDiff_const.mul L.π.contDiff.snd'
      · exact contDiff_snd
    · apply ContDiff.fun_smul
      · exact smoothStep.smooth.fst'.mul L.ρ_smooth.snd'
      · exact Remainder.smooth _ _ (L.loop_smooth h) contDiff_snd contDiff_const

variable {L}
variable {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (N : ℝ)

@[simp]
theorem improveStep_apply (t : ℝ) (x : E) :
    L.improveStep h N t x =
      (𝓕.f x + (smoothStep t * L.ρ x) • corrugation L.π N (L.loop h t) x,
        L.p.update (𝓕.φ x) (L.loop h (smoothStep t * L.ρ x) x <| N * L.π x) +
          (smoothStep t * L.ρ x) • corrugation.remainder L.p.π N (L.loop h 1) x) :=
  rfl

@[simp]
theorem improveStep_apply_f (t : ℝ) (x : E) :
    (L.improveStep h N t).f x = 𝓕.f x + (smoothStep t * L.ρ x) • corrugation L.π N (L.loop h t) x :=
  rfl

@[simp]
theorem improveStep_apply_φ (t : ℝ) (x : E) :
    (L.improveStep h N t).φ x =
      L.p.update (𝓕.φ x) (L.loop h (smoothStep t * L.ρ x) x <| N * L.π x) +
        (smoothStep t * L.ρ x) • corrugation.remainder L.p.π N (L.loop h 1) x :=
  rfl

end StepLandscape

end ImproveStep
end
end
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual finite-atlas smoothing operator on smooth vector-bundle sections. -/
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
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

def bundleSmooth (r : ℕ) (s : ℝ) (u : ∀ x, E x) (x : M) : E x :=
  ∑ i : A.centers, A.bundleRestore e i (finiteSmooth r s (A.bundleLocalize e i u)) x

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

variable [CompactSpace M]

lemma bundleCutoff_smooth (i : A.centers) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart (i : M)).source) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContDiff ℝ ∞ (A.bundleCutoff e i ψ u) :=
  localize_smooth_on (i : M) hψ hsupp (A.bundleComponent_smooth_on e hdomain i hu)

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

lemma bundleLocalize_add (i : A.centers) (u v : ∀ x, E x) :
    A.bundleLocalize e i (u + v) = A.bundleLocalize e i u + A.bundleLocalize e i v := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target <;>
    simp [bundleLocalize, localize, bundleComponent, hx, smul_add]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedModeOperators
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric finite differential parametrix as a linear map on actual
compactly supported smooth fields. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma tsupport_conjugatedD (τ : ℝ) (G Z : Field n) :
    tsupport (conjugatedD τ G Z) ⊆ tsupport Z := by
  apply closure_minimal _ (isClosed_tsupport Z)
  intro p hp
  by_contra hn
  have hz : Z =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  exact hp (by rw [conjugatedD_congr τ G hz]; exact congrFun (conjugatedD_zero τ G) p)

def conjugatedDLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (K : Compacts Base) :
    SupportedField (F := Ambient n) K →ₗ[ℂ] SupportedField (F := Fin 3 → ℂ) K where
  toFun Z := ContDiffMapSupportedIn.of_support_subset
    (contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_conjugatedD τ hG.contDiffAt Z.contDiff.contDiffAt))
    (subset_closure.trans ((tsupport_conjugatedD τ G Z).trans Z.tsupport_subset))
  map_add' Z W := by
    apply DFunLike.ext
    intro p
    change conjugatedD τ G (fun q => Z q + W q) p =
      conjugatedD τ G Z p + conjugatedD τ G W p
    have hh := conjugatedD_sub τ G ((Z.contDiff.add W.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
      (W.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    have he : (fun q => (Z q + W q) - W q) = (Z : Field n) := by
      funext q
      exact add_sub_cancel_right _ _
    rw [he] at hh
    exact sub_eq_iff_eq_add.mp hh.symm
  map_smul' c Z := by
    apply DFunLike.ext
    intro p
    exact conjugatedD_smul τ c G (Z.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)

/-- All correction depths preserve the same compact support. -/
def forcedMode (τ : ℝ) (h : ModeDomain G U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (q : ℕ) (f : SupportedField (F := Fin 3 → ℂ) K) :
    SupportedField (F := Ambient n) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset h.isOpen
      ((forcedMode_tsupport τ G f q).trans (f.tsupport_subset.trans hKU))
      (contDiffOn_modeApprox τ h contDiffOn_const f.contDiff.contDiffOn q))
    (subset_closure.trans ((forcedMode_tsupport τ G f q).trans f.tsupport_subset))

lemma forcedMode_sub (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (q : ℕ)
    (f g : SupportedField (F := Fin 3 → ℂ) K) :
    forcedMode τ h K hKU q (f - g) =
      forcedMode τ h K hKU q f - forcedMode τ h K hKU q g := by
  apply DFunLike.ext
  intro p
  by_cases hp : p ∈ U
  · have hh := modeApprox_sub τ hG h (V := fun _ => 0) (W := fun _ => 0)
      contDiffOn_const contDiffOn_const f.contDiff.contDiffOn g.contDiff.contDiffOn q hp
    change modeApprox τ G (fun _ => 0) (fun p => f p - g p) q p =
      modeApprox τ G (fun _ => 0) f q p - modeApprox τ G (fun _ => 0) g q p
    simpa only [sub_self] using hh
  · have hk : p ∉ (K : Set Base) := fun hmem => hp (hKU hmem)
    change forcedMode τ h K hKU q (f - g) p =
      forcedMode τ h K hKU q f p - forcedMode τ h K hKU q g p
    rw [(forcedMode τ h K hKU q (f - g)).zero_on_compl hk,
      (forcedMode τ h K hKU q f).zero_on_compl hk,
      (forcedMode τ h K hKU q g).zero_on_compl hk]
    exact (sub_self _).symm

def forcedModeLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (q : ℕ) :
    SupportedField (F := Fin 3 → ℂ) K →ₗ[ℂ] SupportedField (F := Ambient n) K where
  toFun := forcedMode τ h K hKU q
  map_add' f g := by
    have hh := forcedMode_sub τ hG h K hKU q (f + g) g
    rw [add_sub_cancel_right] at hh
    exact sub_eq_iff_eq_add.mp hh.symm
  map_smul' c f := by
    apply DFunLike.ext
    intro p
    by_cases hp : p ∈ U
    · have hh := modeApprox_smul τ c hG h (V := fun _ => 0)
        contDiffOn_const f.contDiff.contDiffOn q hp
      change modeApprox τ G (fun _ => 0) (fun p => c • f p) q p =
        c • modeApprox τ G (fun _ => 0) f q p
      simpa only [smul_zero] using hh
    · have hk : p ∉ (K : Set Base) := fun hmem => hp (hKU hmem)
      change forcedMode τ h K hKU q (c • f) p = c • forcedMode τ h K hKU q f p
      rw [(forcedMode τ h K hKU q (c • f)).zero_on_compl hk,
        (forcedMode τ h K hKU q f).zero_on_compl hk]
      simp only [Pi.zero_apply, smul_zero]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma bundleOn_apply (F : P × ℝ → E) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1)
    {p : P} (hp : p ∈ S) (t : ℝ) : bundleOn F S hS hF hper p (t : Period) = F (p, t) := by
  simp only [bundleOn, dite_eq_left hp, bundle_apply]

lemma bundleOn_smooth (F : P × ℝ → E) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ Set.univ))
    (hper : ∀ p ∈ S, Function.Periodic (fun t => F (p, t)) 1) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => bundleOn F S hS hF hper z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := by
  apply hF.congr
  intro z hz
  exact bundleOn_apply F S hS hF hper hz.1 z.2

lemma angleOn_smooth (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => angleOn F S hS hF z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := bundleOn_smooth _ _ _ _ _

lemma slowOn_smooth (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ)) (v : P) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => slowOn F S hS hF v z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := bundleOn_smooth _ _ _ _ _


end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedInitialMode
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported initial amplitudes with both forcing and a free normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma initialAmplitude_tsupport (τ : ℝ) (G V : Field n) (f : Tensor) :
    tsupport (initialAmplitude τ G V f) ⊆ tsupport V ∪ tsupport f :=
  modeApprox_tsupport τ G V f 0

def initialMode (τ : ℝ) (h : ModeDomain G U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (V : SupportedField (F := Ambient n) K)
    (f : SupportedField (F := Fin 3 → ℂ) K) : SupportedField (F := Ambient n) K :=
  let hs := (initialAmplitude_tsupport τ G V f).trans (Set.union_subset V.tsupport_subset f.tsupport_subset)
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset h.isOpen (hs.trans hKU)
      (contDiffOn_initialAmplitude τ h V.contDiff.contDiffOn f.contDiff.contDiffOn))
    (subset_closure.trans hs)

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedNormalSeed
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported normal seeds and the exact leading quadratic metric. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm )

def supportedFreeSeed (δ τ : ℝ) {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K) :
    SupportedField (F := Ambient 4) K :=
  let hs := (freeSeed_tsupport δ τ b F).trans b.tsupport_subset
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset h.isOpen (hs.trans hKU)
      (freeSeed_isFree hF h δ τ b.contDiff.contDiffOn).smooth)
    (subset_closure.trans hs)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridCutoffSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local cell cutoff has the exact global refined support used in
phase selection. This keeps the solver's geometry on that original support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma cellCutoff_eq_vectorPlaneRead (i : A.centers) (a : Finset Index) (h : ℝ) (k : Index) :
    A.vectorPlaneRead i (refinedCutoff (i : M) (A.weight i) a h k) =
      fun y => A.planeWeight i y * normalizedCutoff a h k y := by
  funext y
  change (chart (i : M)).target.indicator (fun x =>
      (A.outer i ((chart (i : M)).symm x))^2 *
        refinedCutoff (i : M) (A.weight i) a h k ((chart (i : M)).symm x))
      (planeCoordinateIsometry.symm y) = _
  by_cases hy : planeCoordinateIsometry.symm y ∈ (chart (i : M)).target
  · have he : chartCoordinates (i : M)
        ((chart (i : M)).symm (planeCoordinateIsometry.symm y)) = y := by
      change planeCoordinateIsometry ((chart (i : M))
        ((chart (i : M)).symm (planeCoordinateIsometry.symm y))) = y
      rw [(chart (i : M)).right_inv hy,LinearIsometryEquiv.apply_symm_apply]
    simp only [refinedCutoff,he,planeWeight,Function.comp_apply,
      chartWeight,indicator_of_mem hy]
    by_cases hw : A.weight i ((chart (i : M)).symm (planeCoordinateIsometry.symm y)) = 0
    · simp only [hw,zero_mul,mul_zero]
    · rw [A.outer_one i _ (subset_tsupport _ hw),one_pow,one_mul]
  · simp only [planeWeight,Function.comp_apply,chartWeight,
      indicator_of_notMem hy,zero_mul]

lemma cellCutoff_tsupport (i : A.centers) {a : Finset Index} {h : ℝ}
    (hh : 0 < h)
    (hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion a h)
    (k : Index) :
    tsupport (supportedCellCutoff (A.supportedPlaneWeight i) hh hcover k) ⊆
      (modeSupport (A.cellChartCompact i a h k) : Set SmallModes.Base) := by
  let f := supportedCellCutoff (A.supportedPlaneWeight i) hh hcover k
  have he : (f : SmallModes.Base → ℝ) =
      A.vectorPlaneRead i (refinedCutoff (i : M) (A.weight i) a h k) := by
    rw [A.cellCutoff_eq_vectorPlaneRead]
    rfl
  intro y hy
  have hK : y ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (f.tsupport_subset hy).1
  have hr := A.vectorPlaneRead_support_on_weight i
    (refinedCutoff (i : M) (A.weight i) a h k) hK (by simpa only [← he] using hy)
  obtain ⟨x,⟨p,hp,rfl⟩,rfl⟩ := hK
  refine ⟨chart (i : M) p,⟨p,?_,rfl⟩,rfl⟩
  simpa only [LinearIsometryEquiv.symm_apply_apply,
    (chart (i : M)).left_inv (A.weight_support i hp)] using hr

def exactCellCutoff (i : A.centers) {a : Finset Index} {h : ℝ}
    (hh : 0 < h)
    (hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion a h)
    (k : Index) : SupportedField (F := ℝ) (modeSupport (A.cellChartCompact i a h k)) :=
  ContDiffMapSupportedIn.of_support_subset
    (supportedCellCutoff (A.supportedPlaneWeight i) hh hcover k).contDiff
    ((subset_tsupport _).trans (A.cellCutoff_tsupport i hh hcover k))

@[simp] lemma exactCellCutoff_apply (i : A.centers) {a : Finset Index} {h : ℝ}
    (hh : 0 < h)
    (hcover : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion a h)
    (k : Index) (x : SmallModes.Base) :
    A.exactCellCutoff i hh hcover k x = A.planeWeight i x * normalizedCutoff a h k x := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AnchoredAtlasPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase catalogs for a fixed smoothing atlas, using geometry only on its weight supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def ReadJetBall (z : ℝ) (F G : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ G ∧ ∀ i x,
    x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x-
      firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤ z^4 ∧
    ‖secondJetTriple (spaceCoordinates ∘ A.vectorPlaneRead i F) x-
      secondJetTriple (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤ z^4

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
local instance atlasMeanDualAdd_rf4ab46_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def atlasMean (μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor)
    (u : ∀ x : M, CovariantTwoTensor x) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => μ i (A.tensorPlaneRead i u))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridRestoredGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normal margins for the restored phases selected on a
variable grid in one fixed atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry PhaseGrid JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

abbrev GridPhaseIndex (s : A.centers → Finset Index) := Σ i : A.centers, (s i) × Fin 3

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

/-- Restrict a locally smooth family to the admissible domain. -/
def ofLocal (F : A → C(Period, E))
    (hF : ContDiffOn ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)) ((O : Set A) ×ˢ Set.univ)) :
    Family O E :=
  ⟨bundleOn (fun z : A × ℝ => F z.1 (z.2 : Period)) O O.isOpen hF
      (fun p _ => SmoothPeriodicCalculus.periodic_lift F p),
    bundleOn_smooth _ _ _ _ _, fun p hp => by simp [bundleOn, hp]⟩

@[simp] lemma ofLocal_apply (F : A → C(Period, E))
    (hF : ContDiffOn ℝ ∞ (fun z : A × ℝ => F z.1 (z.2 : Period)) ((O : Set A) ×ˢ Set.univ))
    {p : A} (hp : p ∈ O) (t : Period) : (ofLocal F hF).val p t = F p t := by
  refine Quotient.inductionOn' t ?_
  intro x
  exact bundleOn_apply _ _ _ _ _ hp x

def angle (F : Family O E) : Family O E :=
  ofLocal (angleOn F.val O O.isOpen F.smooth) (angleOn_smooth _ _ _ _)

def slow (F : Family O E) (v : A) : Family O E :=
  ofLocal (slowOn F.val O O.isOpen F.smooth v) (slowOn_smooth _ _ _ _ _)

def inner (F G : Family O E) : Family O ℝ :=
  ⟨fun p => ⟨fun t => Inner.inner ℝ (F.val p t) (G.val p t),
      (F.val p).continuous.inner (G.val p).continuous⟩,
    F.smooth.inner ℝ G.smooth, fun p hp => by ext t; simp [F.outside hp, G.outside hp]⟩

@[simp] lemma inner_apply (F G : Family O E) (p : A) (t : Period) :
    (F.inner G).val p t = Inner.inner ℝ (F.val p t) (G.val p t) := rfl

def constant (f : A → E) (hf : ContDiffOn ℝ ∞ f O) : Family O E :=
  ofLocal (fun p => ContinuousMap.const Period (f p))
    (hf.comp contDiffOn_fst (fun _ hz => hz.1))

@[simp] lemma constant_apply (f : A → E) (hf : ContDiffOn ℝ ∞ f O)
    {p : A} (hp : p ∈ O) (t : Period) : (constant f hf).val p t = f p :=
  ofLocal_apply _ _ hp t

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilyAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra and support preservation for periodic families on an open domain. -/
noncomputable section

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {O : TopologicalSpace.Opens A} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

def vectorMean (F : Family O E) : Family O E :=
  constant (fun p => average (F.val p)) (contDiffOn_average_joint O.isOpen F.smooth)

@[simp] lemma vectorMean_apply (F : Family O E) (p : A) (t : Period) :
    F.vectorMean.val p t = average (F.val p) := by
  by_cases hp : p ∈ O
  · exact constant_apply _ _ hp t
  · rw [F.vectorMean.outside hp, F.outside hp]
    change (0 : E) = average (fun _ => (0 : E))
    rw [average_const]

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] {O : TopologicalSpace.Opens A}

def mean (F : Family O ℝ) : Family O ℝ := F.vectorMean

def fluct (F : Family O ℝ) : Family O ℝ := F - F.mean

@[simp] lemma mean_apply (F : Family O ℝ) (p : A) (t : Period) :
    F.mean.val p t = average (F.val p) := vectorMean_apply F p t
@[simp] lemma fluct_apply (F : Family O ℝ) (p : A) (t : Period) :
    F.fluct.val p t = fluctuation (F.val p) t := by
  simp only [fluct, sub_apply, mean_apply, fluctuation]

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicExpansionStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite periodic cancellation step on an open admissible domain. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

structure Geometry (O : TopologicalSpace.Opens A) (v : A) where
  plane : A → Submodule ℝ E
  Y : A → E
  C : A → E
  X₀ : A → E
  smoothY : ContDiffOn ℝ ∞ Y O
  smoothC : ContDiffOn ℝ ∞ C O
  smoothX₀ : ContDiffOn ℝ ∞ X₀ O
  derivativeY : ∀ p ∈ O, fderiv ℝ Y p v = C p
  gram_ne : ∀ p ∈ O, PeriodicCorrector.gramDet (Y p) (C p) ≠ 0
  perpY : ∀ p ∈ O, ∀ w, w ∈ plane p → inner ℝ (Y p) w = 0
  perpC : ∀ p ∈ O, ∀ w, w ∈ plane p → inner ℝ (C p) w = 0
  perpX₀ : ∀ p ∈ O, ∀ w, w ∈ plane p → inner ℝ (X₀ p) w = 0
  V : Family O E
  V_mem : ∀ p ∈ O, ∀ t, V.val p t ∈ plane p
  q : A → ℝ
  smoothq : ContDiffOn ℝ ∞ q O
  q_pos : ∀ p ∈ O, 0 < q p
  circle : ∀ p ∈ O, ∀ t, inner ℝ (V.val p t) (V.val p t) = q p

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

def longitudinal : Family O E := Family.constant g.X₀ g.smoothX₀ + g.V

def transverse : Family O E := Family.constant g.Y g.smoothY

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicMetricCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of the pullback metric of the finite periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}



/-- The coefficient A_i=U_{i,x}+U_{i+1,theta}; index zero stores U_1. -/
def xCoefficient (dx : A) (U : ℕ → Family O E) (i : ℕ) : Family O E :=
  (U (i - 1)).slow dx + (U i).angle

/-- The coefficient B_i=U_{i,y}; index zero stores U_1. -/
def yCoefficient (dy : A) (U : ℕ → Family O E) (i : ℕ) : Family O E :=
  (U (i - 1)).slow dy

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicGlobalization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported local periodic coefficients extend smoothly by zero. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Family
variable {O : TopologicalSpace.Opens A}

lemma smooth_global (F : Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → F.val p = 0) :
    ContDiff ℝ ∞ (fun z : A × ℝ => F.val z.1 (z.2 : Period)) := by
  apply contDiff_of_zero_off_closed O.isOpen F.smooth hK hKO
  intro p hp t
  by_cases hpO : p ∈ O
  · rw [hz p hpO hp]
    rfl
  · rw [F.outside hpO]
    rfl

def global (F : Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → F.val p = 0) : PeriodicExpansion.Family A E :=
  ⟨F.val, F.smooth_global hK hKO hz⟩

@[simp] lemma global_apply (F : Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ p ∈ O, p ∉ K → F.val p = 0) (p : A) (t : Period) :
    (F.global hK hKO hz).val p t = F.val p t := rfl

end Family

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma inner_toEuclidean (v w : RVec 4) :
    inner ℝ (toEuclidean v) (toEuclidean w) = v ⬝ᵥ w := by
  simpa [toEuclidean] using (spaceCoordinates_dot (spaceCoordinates.symm v)
    (spaceCoordinates.symm w)).symm

lemma gram_toEuclidean (v w : RVec 4) :
    PeriodicCorrector.gramDet (toEuclidean v) (toEuclidean w) =
      NormalFrame.gramDet v w := by
  simp only [PeriodicCorrector.gramDet, NormalFrame.gramDet, inner_toEuclidean]

lemma euclidean_y_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => toEuclidean (slot 2 (lowJet G q))) p (coordinateVector 1) =
      toEuclidean (slot 6 (lowJet G p)) := by
  have hs := (slot_smooth 2).comp (lowJet_smooth hG)
  have hd := (toEuclidean.hasFDerivAt.comp p
    (hs.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = toEuclidean (fderiv ℝ (fun q => slot 2 (lowJet G q)) p (coordinateVector 1)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector 1)) hd
    _ = _ := congrArg toEuclidean (slot_y_derivative hG p)

end ClosedSurfaceR4.JetVelocityCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

def euclideanVelocity : LowJet → C(Period, Euclidean) :=
  bundleOn (fun z => ι (l.velocity z)) O O.isOpen
    (JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn l.smoothVelocity)
    (fun J hJ t => congrArg ι (l.periodic J hJ t))

lemma euclideanVelocity_apply {J : LowJet} (hJ : J ∈ O) (t : ℝ) :
    l.euclideanVelocity J (t : Period) = ι (l.velocity (J, t)) :=
  bundleOn_apply _ _ _ _ _ hJ t

lemma euclideanVelocity_smooth :
    ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => l.euclideanVelocity z.1 (z.2 : Period))
      (O ×ˢ univ) := bundleOn_smooth _ _ _ _ _

lemma euclideanVelocity_length {J : LowJet} (hJ : J ∈ O) (t : Period) :
    inner ℝ (l.euclideanVelocity J t) (l.euclideanVelocity J t) = l.q J := by
  refine Quotient.inductionOn' t ?_
  intro t
  rw [l.euclideanVelocity_apply hJ, inner_toEuclidean]
  exact l.length J hJ t

def plane (J : LowJet) : Submodule ℝ Euclidean :=
  LinearMap.ker (innerSL ℝ (ι (slot 2 J))).toLinearMap ⊓
    LinearMap.ker (innerSL ℝ (ι (slot 6 J))).toLinearMap

lemma mem_plane {J : LowJet} {w : Euclidean} :
    w ∈ plane J ↔ inner ℝ (ι (slot 2 J)) w = 0 ∧
      inner ℝ (ι (slot 6 J)) w = 0 := Iff.rfl

lemma tangent_perp {J : LowJet} {w : Euclidean} (hw : w ∈ plane J) :
    inner ℝ (ι (tangent J)) w = 0 := by
  obtain ⟨hy, hc⟩ := mem_plane.mp hw
  have hw' : ι (JetVelocityCoordinates.toEuclidean.symm w) = w := JetVelocityCoordinates.toEuclidean.apply_symm_apply w
  rw [← hw', inner_toEuclidean] at hy hc ⊢
  exact tangential_part_perp _ _ _ _ hy hc

/-- Pulling back through the actual second jet supplies the differentiated
constraint `Y_y=C`, rather than adding that constraint as a new input. -/
def geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) : Geometry (E := Euclidean) S (coordinateVector 1) where
  plane p := plane (lowJet G p)
  Y p := ι (slot 2 (lowJet G p))
  C p := ι (slot 6 (lowJet G p))
  X₀ p := ι (tangent (lowJet G p))
  smoothY := (JetVelocityCoordinates.toEuclidean.contDiff.comp ((slot_smooth 2).comp (lowJet_smooth hG))).contDiffOn
  smoothC := (JetVelocityCoordinates.toEuclidean.contDiff.comp ((slot_smooth 6).comp (lowJet_smooth hG))).contDiffOn
  smoothX₀ := JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
    (l.smoothTangent.comp (lowJet_smooth hG).contDiffOn hGO)
  derivativeY p _ := euclidean_y_derivative hG p
  gram_ne p hp := by rw [gram_toEuclidean]; exact l.gram_ne _ (hGO hp)
  perpY _ _ _ hw := (mem_plane.mp hw).1
  perpC _ _ _ hw := (mem_plane.mp hw).2
  perpX₀ _ _ _ hw := tangent_perp hw
  V := Family.ofLocal (fun p => l.euclideanVelocity (lowJet G p))
    (l.euclideanVelocity_smooth.comp
      ((lowJet_smooth hG).contDiffOn.comp contDiffOn_fst (fun z _ => mem_univ z.1)
        |>.prodMk contDiffOn_snd) (fun z hz => ⟨hGO hz.1, mem_univ z.2⟩))
  V_mem p hp t := by
    rw [Family.ofLocal_apply _ _ hp]
    refine Quotient.inductionOn' t ?_
    intro t
    rw [l.euclideanVelocity_apply (hGO hp)]
    apply mem_plane.mpr
    constructor
    · rw [inner_toEuclidean]; exact l.perpY _ (hGO hp) t
    · rw [inner_toEuclidean]; exact l.perpC _ (hGO hp) t
  q p := l.q (lowJet G p)
  smoothq := l.smoothQ.comp (lowJet_smooth hG).contDiffOn hGO
  q_pos _ hp := l.q_pos (hGO hp)
  circle p hp t := by
    rw [Family.ofLocal_apply _ _ hp]
    exact l.euclideanVelocity_length (hGO hp) t

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalPeriodicPolynomialExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric polynomial coefficients of the finite periodic derivative ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial vectorPolynomialValue
  )


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

def xTangent (dx : A) (U : ℕ → Family O E) (L i : ℕ) : Family O E :=
  if i = 0 then g.longitudinal else
  if i = L then (U (i - 1)).slow dx else xCoefficient dx U i

def yTangent (U : ℕ → Family O E) (i : ℕ) : Family O E :=
  if i = 0 then g.transverse else yCoefficient dy U i

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma xTangent_zero (dx : A) (U : ℕ → Family O E) (L : ℕ) :
    g.xTangent dx U L 0 = g.longitudinal := by simp [xTangent]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma yTangent_zero (U : ℕ → Family O E) : g.yTangent U 0 = g.transverse := by
  simp [yTangent]

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualSmul
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberNormed
local instance polynomialMetricSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def atlasPolynomialVariation (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G X : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinateRealLinearized (P i) ε (A.jetChartMap i G)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0)

def atlasPolynomialQuadratic (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G X : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i G)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0)

def atlasPolynomialRemainder (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G X : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => coordinateTaylorRemainder (P i) ε (A.jetChartMap i G)
    (A.jetChartMap i X ∘ planeCoordinateIsometry.symm))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPhaseMeanDomains
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed mean domains and common margins obtained from compact atlas geometry. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

structure PhaseMeanDomains (F : M → Space) (Q : A.centers → PhaseBasis)
    (reference : A.centers → SmallModes.Base → Tensor) where
  r : ℝ
  ρ : ℝ
  R : ℝ
  r_pos : 0 < r
  ρ_pos : 0 < ρ
  R_pos : 0 < R
  Ω : A.centers → Fin 3 → Set SmallModes.Base
  U : A.centers → Fin 3 → Set SmallModes.Base
  K : A.centers → Fin 3 → Set SmallModes.Base
  openΩ : ∀ i j, IsOpen (Ω i j)
  openU : ∀ i j, IsOpen (U i j)
  compactK : ∀ i j, IsCompact (K i j)
  UK : ∀ i j, U i j ⊆ K i j
  KΩ : ∀ i j, K i j ⊆ Ω i j
  support : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j
  immersion : ∀ i j x, x ∈ Ω i j →
    Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
  good : ∀ i j x, x ∈ Ω i j →
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j)
  U₀ : A.centers → Set JetPolynomial.Base
  K₀ : A.centers → Compacts JetPolynomial.Base
  openU₀ : ∀ i, IsOpen (U₀ i)
  U₀K₀ : ∀ i, U₀ i ⊆ K₀ i
  supportU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i
  margin : ∀ i j x, x ∈ U i j →
    ρ + ‖(Q i).Q j‖*r ≤ (Q i).Q j (reference i x) ∧
      (Q i).Q j (reference i x) ≤ R - ‖(Q i).Q j‖*r

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLocalModel
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single local polynomial models the global perturbation, with its
first and second variations, on the entire compact chart support. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance localModelFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance localModelFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance localModelDualAdd_rf4ab46_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance localModelDualSmul_rf4ab46_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance localModelSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance localModelSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The same local polynomials represent the global quadratic variation. -/
def PolynomialQuadraticRepresentation {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression) : Prop :=
  ∀ (F X : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ContMDiff planeModel spaceModel ∞ X → ∀ i : A.centers,
      ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
        coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F)
            (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
          A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SelectedGridGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact support and denominator consequences of the selected anchored phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def SelectedGridPointMargins (g : SmoothMetric M) (z : ℝ)
    (s : A.centers → Finset Index) (P : ∀ i, (s i) → PhaseBasis)
    (G : M → Space) (c b ε : ℝ) : Prop :=
  ∀ i (a : s i) x,
    x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    x ∈ tsupport (cutoff (z^6) a.val) →
    c/4 ≤ NormalFrame.gramDet
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).1
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).2 ∧
    b/2 ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ∧ ∀ j,
      ε/2 ≤ (P i a).Q j (A.tensorPlaneRead i g.inner x) ∧
      (ε/4)*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤
        ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
          (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ((P i a).ξ j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveCorrectionStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.adaptiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.adaptiveFiberNormed
local instance adaptiveFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance adaptiveDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}

namespace PreparedCorrection
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.adaptiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.adaptiveFiberNormed
local instance adaptiveFiberSpace_rf4ab46_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance adaptiveDualSmul_rf4ab46_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (c : PreparedCorrection d)

local instance adaptiveSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance adaptiveSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- At every stage the order can be held. It is increased as soon as the next
finite input bound and the next geometric threshold permit it. -/
theorem transition_nonempty (hF : ContMDiff planeModel spaceModel ∞ F)
    {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32) {n : ℕ} (s : c.Stage t n) :
    Nonempty (c.Transition s) := by
  classical
  let k := if s.CanAdvance then s.order+1 else s.order
  have hk : s.order ≤ k ∧ k ≤ s.order+1 := by dsimp [k]; split_ifs <;> omega
  have htime := correctionScale_pos ht n
  have htime1 : correctionScale t n ≤ 1 :=
    (correctionScale_le_initial ht.le htsmall n).trans (by linarith)
  have hnext : correctionScale t (n+1) ≤ correctionScale t n := by
    exact (scale_step_le_half htime.le
      ((correctionScale_le_initial ht.le htsmall n).trans htsmall)).trans (by linarith)
  have hnear : d.A.WeightedBound 1 2 (c.ρ/4) (s.map-F) := by
    intro i
    exact (s.near i).mono_const (correction_displacement_budget ht.le htsmall c.ρ_pos.le n)
  obtain ⟨U,hU,hsmall,herror,hinput⟩ := c.step s.order s.map s.smooth
    (correctionScale t n) htime s.scale_small (correctionOrder k)
    (by unfold correctionOrder; omega) (by unfold correctionOrder; omega)
    s.input hnear s.metric
  have he : (correctionScale t n)^((6/5 : ℝ)*(correctionOrder k : ℝ)) =
      (correctionScale t (n+1))^(correctionOrder k : ℝ) := by
    rw [correctionScale,← Real.rpow_mul htime.le]
  have hε : correctionScale t (n+1) < c.ε k := by
    dsimp [k]
    split_ifs with h
    · exact hnext.trans_lt h.1
    · exact hnext.trans_lt s.scale_small
  have hin : d.A.InputBound (correctionScale t (n+1)) (correctionInputOrder k)
      c.budget (s.map+U)
      (normalizedTensorDefect g.inner
        ((correctionScale t (n+1))^(correctionOrder k : ℝ)) (s.map+U)) := by
    by_cases hadv : s.CanAdvance
    · have hk' : k = s.order+1 := ite_eq_left hadv
      obtain ⟨C,hC,hCb⟩ := s.finiteInput ht htsmall (correctionInputOrder (s.order+1))
      have hsize := d.A.inputSize_bound ⟨C,hC,hCb⟩
      have hnsize := d.A.inputSize_nonneg ⟨C,hC,hCb⟩
      have hh := hinput (correctionInputOrder (s.order+1)) _ hnsize hsize
      rw [he] at hh
      rw [hk'] at hh ⊢
      exact d.A.inputBound_mono_const hh hadv.2
    · have hk' : k = s.order := ite_eq_right hadv
      have hh := hinput (correctionInputOrder s.order) c.budget c.budget_pos.le s.input
      rw [he] at hh
      rw [hk'] at hh ⊢
      exact d.A.inputBound_mono_const hh (c.preserve s.order _ htime s.scale_small).1
  have hmet : ∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner
      ((correctionScale t (n+1))^(correctionOrder k : ℝ)) (s.map+U)) x-
      d.A.tensorEncode g.inner x‖ ≤ c.a/8 := by
    have hL := c.L_nonneg s.order
    have hB := c.budget_pos
    have hb := d.A.tensorEncode_bound
      ((d.A.normalizedTensorDefect_smooth g.contMDiff _ (s.smooth.add hU)).sub_section g.contMDiff)
      (Real.rpow_pos_of_pos htime _) (by positivity) herror
    intro x
    have hh := hb.norm_le (mem_univ x)
    rw [he] at hh
    simpa only [d.A.tensorEncode_sub,Pi.sub_apply] using
      hh.trans (c.preserve s.order _ htime s.scale_small).2
  have hmap : d.A.WeightedBound 1 2 (c.stageRadius t (n+1)) (s.map+U-F) := by
    have hu := hsmall 2 (by unfold correctionOrder; omega)
    have hb := d.A.weightedBound_add (s.smooth.sub hF) hU zero_le_one s.near hu
    have heq : s.map+U-F = (s.map-F)+U := by abel
    rw [heq]
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    simp only [stageRadius,Finset.sum_range_succ]
    ring
  refine ⟨⟨⟨k,s.map+U,s.smooth.add hU,hε,hin,hmap,hmet⟩,U,hU,rfl,rfl,hsmall,?_⟩⟩
  intro m C hC hb
  have hh := hinput m C hC hb
  rw [he] at hh
  exact hh

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveCorrectionSequence
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the correction sequence, and unbounded growth of the
finite derivative order despite the absence of uniform high-order input bounds. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions_1
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance sequenceFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance sequenceFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance sequenceDualAdd_rf4ab46_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance sequenceDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions_1
local instance sequenceFiberNormed_rf4ab46_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance sequenceFiberSpace_rf4ab46_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance sequenceDualAdd_rf4ab46_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance sequenceDualSmul_rf4ab46_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (c : PreparedCorrection d) (hF : ContMDiff planeModel spaceModel ∞ F)
  {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)

local instance sequenceSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance sequenceSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def chosenTransition {n : ℕ} (s : c.Stage t n) : c.Transition s :=
  Classical.choice (c.transition_nonempty hF ht htsmall s)

def sequence (seed : c.Stage t 0) : (n : ℕ) → c.Stage t n
  | 0 => seed
  | n+1 => (c.chosenTransition hF ht htsmall (sequence seed n)).next

def increment (seed : c.Stage t 0) (n : ℕ) : M → Space :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).increment

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactFastFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily accurate primitive maps give an actual smooth exact metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance exactFastFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance exactFastFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance exactFastDualAdd_rf4ab46_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactFastDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance exactFastSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactFastSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Retain a proved property of the actual finite-accuracy approximant. -/
def GeometricFastFamilyWithProperty (g : SmoothMetric M) (R c b V₀ : ℝ) (property : ℝ → (M → Space) → Prop) : Prop :=
  ∀ N : ℕ, ∃ η C Cv : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 ≤ Cv ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ F : M → Space,
        ContMDiff planeModel spaceModel ∞ F ∧ property z F ∧
        A.WeightedBound 1 0 V₀ F ∧ A.WeightedBound z 442 Cv F ∧
        A.ShiftedBound 2 440 z (Cv/z^2) F ∧
        A.TensorWeightedBound 1 440 (C*z^(N+1)) (inducedTensor F-g.inner) ∧
        ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
          ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
          c ≤ NormalFrame.gramDet
            (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
            (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
          b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLinearized
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberSpace
local instance polynomialAssemblyDualSmul_rf4ab46_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberNormed
local instance polynomialAssemblySectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAssemblySectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The local linearized operators act on the same global polynomial metric. -/
def PolynomialLinearRepresentation {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression) : Prop :=
  ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ (X : A.centers → RealModes.RField 4), (∀ i, ContDiff ℝ ∞ (X i)) →
      (∀ i, tsupport (X i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ ε : ℝ,
        linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore X)+
            A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ A.vectorPlaneRestore X) =
          A.tensorPlaneRestore (fun i => coordinateFullLinearized (Q i) ε (A.jetChartMap i F) (X i))

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
local instance atlasPrimitiveSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasPrimitiveSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def normalizedPolynomialDefect
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space) : ∀ x : M, CovariantTwoTensor x :=
  (δ^2)⁻¹ • (γ-A.atlasPolynomialMetric P ε G)-γ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSlowFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite family solving the perturbed mean equation to successively
higher amplitude orders. Every member is an actual smooth map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Uniform profiles for the nearby smooth maps at one finite stage. -/
def HasPolynomialSlowFamily {n : A.centers → ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (γ : ∀ x : M, CovariantTwoTensor x) (F : M → Space) (d b : ℝ) : Prop :=
  ∃ (a u η L : ℝ) (P D : ℕ → ℝ), 0 < a ∧ 0 < u ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧
    (∀ m, 0 ≤ P m) ∧ (∀ m, 0 ≤ D m) ∧
    (∀ m, A.ShiftedBound 2 m 1 (P m) F) ∧
    ∀ z : ℝ, 0 < z → z < η → ∃ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G ∧
      A.WeightedBound 1 3 (L*z^u) (G-F) ∧
      (∀ m, A.ShiftedBound 2 m (z^b) (P m) G) ∧
      (∀ m, A.TensorWeightedBound (z^b) m (D m*z^a)
        (A.normalizedPolynomialDefect Pol z (z^d) γ G))

end SmoothingAtlas

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ProfiledPhaseFastFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast approximants with prescribed accuracy in the leading five
primitive derivatives and the slow baseline, retained for the exact step. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PrimitiveRealization CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas

local instance profiledPhasePrimitiveFamilyFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledPhasePrimitiveFamilyFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance profiledPhasePrimitiveFamilyDualAdd_rf4ab46_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledPhasePrimitiveFamilyDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance profiledPhasePrimitiveFamilySectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledPhasePrimitiveFamilySectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def PhasePrimitiveProfileNear (A : SmoothingAtlas M) (F : M → Space) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    (S : TopologicalSpace.Opens JetPolynomial.Base) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (K : Set JetPolynomial.Base) (ε z : ℝ) (V : M → Space) : Prop :=
  ∃ G : M → Space, ∃ hG : ContMDiff planeModel spaceModel ∞ G,
    ∃ hGO : MapsTo (lowJet (A.jetChartMap i G ∘ e.symm)) S O,
    A.WeightedBound 1 3 ε (G-F) ∧
    (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
      let geom := l.geometry (A.jetChartMap i G ∘ e.symm) ((A.jetChartMap_smooth i hG).comp hi) hGO
      let t : Period := ((ℓ p/z : ℝ) : Period)
      ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i V ∘ e.symm) z p-
        ![geom.longitudinal.val p t,geom.Y p,geom.C p,
          (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤ ε) ∧
    (∀ p ∉ tsupport (A.weight i), V =ᶠ[𝓝 p] G) ∧
    ∀ p ∉ A.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPrimitiveFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite circular data used in the global primitive iteration.
All geometric fields are furnished by the generic radius/phase preparation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

structure CircularPrimitiveFamily (B : SmoothingAtlas M) (ι : Type*) [Fintype ι] where
  curves : ι → PhaseBoundaryCurve B
  radius : ι → ℝ
  outerRadius : ι → ℝ
  chartRadius : ι → ℝ
  linearPart : ι → Base
  convexPart : ι → ℝ
  radius_pos : ∀ a, 0 < radius a
  radius_outer : ∀ a, (radius a)^2 < (outerRadius a)^2
  radius_chart : ∀ a, radius a < chartRadius a
  weight_positive : ∀ a p, 0 < B.weight (curves a).index p ↔
    p ∈ circularCoordinateDisk ((curves a).index : M) (outerRadius a)
  region : ∀ a, circularCoordinateRegion ((curves a).index : M) (radius a) ⊆
    (coordinateChart ((curves a).index : M)).target
  carrier : ∀ a, (curves a).carrier = circularBoundary ((curves a).index : M) (radius a)
  cover : ∀ a x, x ∈ circularCoordinateRegion ((curves a).index : M) (radius a) →
    baseEquiv.symm x ∈ (curves a).phase.source
  first_coordinate : ∀ a x, (baseEquiv ((curves a).phase x)).1 =
    centeredConvexPhase (linearPart a) (convexPart a)
      (coordinateChart ((curves a).index : M) (curves a).index) (baseEquiv x)
  pair_finite : ∀ a b, a ≠ b → ((curves a).carrier ∩ (curves b).carrier).Finite
  triple_empty : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    (curves a).carrier ∩ (curves b).carrier ∩ (curves c).carrier = ∅
  tangencies_finite : ∀ a b, (circularPhaseTangencies ((curves a).index : M) ((curves b).index : M)
    (linearPart a) (convexPart a) (radius b) (radius a)).Finite
  independent : ∀ a b, a ≠ b → ∀ p ∈ boundaryCrossingSet curves univ,
    p ∈ (coordinateChart ((curves a).index : M)).source →
    p ∈ (coordinateChart ((curves b).index : M)).source →
    covectorDet
      (phaseDerivative (centeredAtlasPhase ((curves a).index : M) (linearPart a) (convexPart a) ∘
        (coordinateChart ((curves a).index : M)).symm) (coordinateChart ((curves a).index : M) p))
      (phaseDerivative (centeredAtlasPhase ((curves b).index : M) (linearPart b) (convexPart b) ∘
        (coordinateChart ((curves a).index : M)).symm) (coordinateChart ((curves a).index : M) p)) ≠ 0
  amplitude : ι → M → ℝ
  phase : ι → M → ℝ
  phase_smooth : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phase a)
  amplitude_smooth : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amplitude a)
  amplitude_nonneg : ∀ a p, 0 ≤ amplitude a p
  amplitude_positive : ∀ a p, 0 < amplitude a p ↔
    p ∈ circularCoordinateDisk ((curves a).index : M) (radius a)
  phase_germ : ∀ a p, p ∈ circularCoordinateDisk ((curves a).index : M) (radius a) →
    phase a =ᶠ[𝓝 p] (fun q => ((curves a).phase (chart ((curves a).index : M) q)) 0)

namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

 def restrict (d : CircularPrimitiveFamily B ι) {κ : Type*} [Fintype κ]
    (f : κ → ι) (hf : Function.Injective f) : CircularPrimitiveFamily B κ where
  curves := d.curves ∘ f
  radius := d.radius ∘ f
  outerRadius := d.outerRadius ∘ f
  chartRadius := d.chartRadius ∘ f
  linearPart := d.linearPart ∘ f
  convexPart := d.convexPart ∘ f
  radius_pos a := d.radius_pos (f a)
  radius_outer a := d.radius_outer (f a)
  radius_chart a := d.radius_chart (f a)
  weight_positive a := d.weight_positive (f a)
  region a := d.region (f a)
  carrier a := d.carrier (f a)
  cover a := d.cover (f a)
  first_coordinate a := d.first_coordinate (f a)
  pair_finite a b hab := d.pair_finite (f a) (f b) (fun h => hab (hf h))
  triple_empty a b c hab hac hbc := d.triple_empty (f a) (f b) (f c)
    (fun h => hab (hf h)) (fun h => hac (hf h)) (fun h => hbc (hf h))
  tangencies_finite a b := d.tangencies_finite (f a) (f b)
  independent a b hab p hp hpa hpb := by
    apply d.independent (f a) (f b) (fun h => hab (hf h)) p _ hpa hpb
    obtain ⟨j,_,k,_,hjk,hj,hk⟩ := hp
    exact ⟨f j,mem_univ _,f k,mem_univ _,fun h => hjk (hf h),hj,hk⟩
  amplitude := d.amplitude ∘ f
  phase := d.phase ∘ f
  phase_smooth a := d.phase_smooth (f a)
  amplitude_smooth a := d.amplitude_smooth (f a)
  amplitude_nonneg a := d.amplitude_nonneg (f a)
  amplitude_positive a := d.amplitude_positive (f a)
  phase_germ a := d.phase_germ (f a)

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularMetricSequence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered finite primitive realization. The metric convexity is required
only at the actual prefix metrics, preserving the order of the cycles. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace CircularPrimitiveFamily
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

def ConvexMetric (d : CircularPrimitiveFamily B ι) (g : SmoothMetric M) (a : ι) : Prop :=
  ∀ p ∈ tsupport (B.weight (d.curves a).index),
    ‖coordinateChart ((d.curves a).index : M) p-coordinateChart ((d.curves a).index : M) (d.curves a).index‖ ≤ d.chartRadius a →
    ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((d.curves a).index : M))
      (centeredConvexPhase (d.linearPart a) (d.convexPart a)
        (coordinateChart ((d.curves a).index : M) (d.curves a).index))
      (coordinateChart ((d.curves a).index : M) p) v v

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPrimitiveFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

namespace SmoothPrimitiveFamily
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyDualSmul
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familyFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.familySectionNormed
local instance familySectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma term_smooth (A : SmoothingAtlas M) (a : ι) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (d.term a p)) :=
  ((d.smoothAmplitude a).pow 2).smul_section (A.phaseDifferentialSquare_smooth _ (d.smoothPhase a))

include d in
lemma tensor_smooth (A : SmoothingAtlas M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)) := by
  have he : u = fun p => ∑ a, d.term a p := funext (fun p => (d.sum_eq p).symm)
  rw [he]
  exact ContMDiff.sum_section (fun a _ => d.term_smooth A a)

lemma cycleTensor_smooth (A : SmoothingAtlas M) (N c : ℕ) (s : Finset ι) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (d.cycleTensor N c s p)) :=
  (d.tensor_smooth A).const_smul_section.add_section
    ((ContMDiff.sum_section (fun a _ => d.term_smooth A a)).const_smul_section)

def cycleMetric (A : SmoothingAtlas M) (g : SmoothMetric M) (N c : ℕ) (s : Finset ι) : SmoothMetric M :=
  positiveTensorMetric (g.inner+d.cycleTensor N c s)
    (g.contMDiff.add_section (d.cycleTensor_smooth A N c s))
    (by
      intro p v w
      change g.inner p v w+d.cycleTensor N c s p v w =
        g.inner p w v+d.cycleTensor N c s p w v
      rw [g.symm,d.cycleTensor_symmetric])
    (by
      intro p v hv
      exact add_pos_of_pos_of_nonneg (g.pos p v hv) (d.cycleTensor_nonneg N c s p v))

end SmoothPrimitiveFamily

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPrefixMetrics
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ordered prefix metrics of a finite circular family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance prefixFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance prefixFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance prefixDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace CircularPrimitiveFamily
local instance prefixFiberNormed_rf4ab46_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance prefixFiberSpace_rf4ab46_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance prefixDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {B : SmoothingAtlas M} {N : ℕ} (d : CircularPrimitiveFamily B (Fin N))

local instance prefixSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance prefixSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def totalTensor (p : M) : CovariantTwoTensor p :=
  ∑ a, (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p

def smoothFamily : SmoothPrimitiveFamily (Fin N) d.totalTensor where
  amplitude := d.amplitude
  phase := d.phase
  smoothAmplitude := d.amplitude_smooth
  smoothPhase := d.phase_smooth
  sum_eq _ := rfl

def prefixMetric (g : SmoothMetric M) (k : Fin (N+1)) : SmoothMetric M :=
  d.smoothFamily.cycleMetric B g 1 0 (prefixIndices k)

end CircularPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected reference atlas supplies the actual identity operator,
smooth coefficient germs, and positive metric coefficients. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def localPhases := d.B.centeredPhaseFamily (fun i => (d.P i).ξ) d.L

def basis := d.B.centeredAtlasBasis d.P (fun i => (d.P i).ξ) d.L

def globalPhases := d.B.curvedAtlasPhase d.localPhases

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularMargins
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact positive inverse margins in the actual reference chart frames. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry
local instance referenceMarginFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceMarginFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance referenceMarginFiberComplete_rf4ab46_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
local instance referenceMarginFiberNormed_rf4ab46_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance referenceMarginFiberSpace_rf4ab46_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance referenceMarginFiberComplete_rf4ab46_2 : CompleteSpace TensorFiber := inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def chartCoefficient (i : d.B.centers) (j : Fin 3) (y : JetPolynomial.Base) : TensorFiber →L[ℝ] ℝ :=
  ((d.basis i y).Q j).comp fiberToThree

def chartReference (i : d.B.centers) (y : JetPolynomial.Base) : TensorFiber :=
  fiberFromThree (d.B.tensorChartRead i gref.inner y)

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ReferenceCoordinateData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Size, identity and positivity of the fixed reference data in any active
chart. The constants precede every independent radius and phase choice. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
local instance refDataFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance refDataFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance refDataDualNormed_rf4ab46_1 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance refDataDualSpace_rf4ab46_1 : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance refDataDualAdd_rf4ab46_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refDataDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance refDataSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance refDataSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def coordinateReference (i : d.B.centers) (p : M) : PrimitiveAmplitudeData (d.B.centers × Fin 3) :=
  d.B.primitiveCoordinateData d.basis (fun a => d.B.weight a.1) d.globalPhases gref.inner i
    {a | p ∈ tsupport (d.B.weight a.1)} (chart (i : M) p)

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferencePerturbationStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine independent circular phase and cutoff choices preserve the
fixed reference inverse margins for all sufficiently close starting maps. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
local instance perturbationFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance perturbationFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance perturbationDualAdd_rf4ab46_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance perturbationDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance perturbationSectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance perturbationSectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def perturbedPhases (ell : d.B.centers → Fin 3 → Base) :=
  d.B.curvedAtlasPhase (d.B.centeredPhaseFamily ell d.L)

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFamilyGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite generic boundary geometry is chosen before any amplitudes
or finite-point spherical modification. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

structure CircularFamilyGeometry (B : SmoothingAtlas M) (ι : Type*) [Fintype ι] where
  curves : ι → PhaseBoundaryCurve B
  radius : ι → ℝ
  outerRadius : ι → ℝ
  chartRadius : ι → ℝ
  linearPart : ι → Base
  convexPart : ι → ℝ
  radius_pos : ∀ a, 0 < radius a
  radius_outer : ∀ a, (radius a)^2 < (outerRadius a)^2
  radius_chart : ∀ a, radius a < chartRadius a
  weight_positive : ∀ a p, 0 < B.weight (curves a).index p ↔
    p ∈ circularCoordinateDisk ((curves a).index : M) (outerRadius a)
  region : ∀ a, circularCoordinateRegion ((curves a).index : M) (radius a) ⊆
    (coordinateChart ((curves a).index : M)).target
  carrier : ∀ a, (curves a).carrier = circularBoundary ((curves a).index : M) (radius a)
  cover : ∀ a x, x ∈ circularCoordinateRegion ((curves a).index : M) (radius a) →
    baseEquiv.symm x ∈ (curves a).phase.source
  first_coordinate : ∀ a x, (baseEquiv ((curves a).phase x)).1 =
    centeredConvexPhase (linearPart a) (convexPart a)
      (coordinateChart ((curves a).index : M) (curves a).index) (baseEquiv x)
  pair_finite : ∀ a b, a ≠ b → ((curves a).carrier ∩ (curves b).carrier).Finite
  triple_empty : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    (curves a).carrier ∩ (curves b).carrier ∩ (curves c).carrier = ∅
  tangencies_finite : ∀ a b, (circularPhaseTangencies ((curves a).index : M) ((curves b).index : M)
    (linearPart a) (convexPart a) (radius b) (radius a)).Finite
  independent : ∀ a b, a ≠ b → ∀ p ∈ boundaryCrossingSet curves univ,
    p ∈ (coordinateChart ((curves a).index : M)).source →
    p ∈ (coordinateChart ((curves b).index : M)).source →
    covectorDet
      (phaseDerivative (centeredAtlasPhase ((curves a).index : M) (linearPart a) (convexPart a) ∘
        (coordinateChart ((curves a).index : M)).symm) (coordinateChart ((curves a).index : M) p))
      (phaseDerivative (centeredAtlasPhase ((curves b).index : M) (linearPart b) (convexPart b) ∘
        (coordinateChart ((curves a).index : M)).symm) (coordinateChart ((curves a).index : M) p)) ≠ 0

namespace CircularFamilyGeometry
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

def withAmplitudes (d : CircularFamilyGeometry B ι) (amp phi : ι → M → ℝ)
    (hamp : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amp a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hamp0 : ∀ a p, 0 ≤ amp a p)
    (hpos : ∀ a p, 0 < amp a p ↔ p ∈ circularCoordinateDisk ((d.curves a).index : M) (d.radius a))
    (hgerm : ∀ a p, p ∈ circularCoordinateDisk ((d.curves a).index : M) (d.radius a) →
      phi a =ᶠ[𝓝 p] (fun q => ((d.curves a).phase (chart ((d.curves a).index : M) q)) 0)) :
    CircularPrimitiveFamily B ι where
  curves := d.curves
  radius := d.radius
  outerRadius := d.outerRadius
  chartRadius := d.chartRadius
  linearPart := d.linearPart
  convexPart := d.convexPart
  radius_pos := d.radius_pos
  radius_outer := d.radius_outer
  radius_chart := d.radius_chart
  weight_positive := d.weight_positive
  region := d.region
  carrier := d.carrier
  cover := d.cover
  first_coordinate := d.first_coordinate
  pair_finite := d.pair_finite
  triple_empty := d.triple_empty
  tangencies_finite := d.tangencies_finite
  independent := d.independent
  amplitude := amp
  phase := phi
  phase_smooth := hphi
  amplitude_smooth := hamp
  amplitude_nonneg := hamp0
  amplitude_positive := hpos
  phase_germ := hgerm

end CircularFamilyGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CycleCorrectedGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference charts give the generic finite geometry for any number of
cycles without shrinking the admissible chart radii after that number is
chosen. The actual corrected families are then attached to those circles. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance cycleGeometryFiberNormed_rf4ab46_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_rf4ab46_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance

namespace SmoothPrimitiveFamily
local instance cycleGeometryFiberNormed_rf4ab46_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_rf4ab46_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_rf4ab46_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {u : ∀ p : M, CovariantTwoTensor p} {ι κ : Type*} [Fintype ι] [Fintype κ]

local instance cycleGeometrySectionNormed_rf4ab46_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_rf4ab46_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Reindex only the genuine finite family, preserving its exact sum. -/
def reindex (f : SmoothPrimitiveFamily ι u) (e : κ ≃ ι) : SmoothPrimitiveFamily κ u where
  amplitude := f.amplitude ∘ e
  phase := f.phase ∘ e
  smoothAmplitude a := f.smoothAmplitude (e a)
  smoothPhase a := f.smoothPhase (e a)
  sum_eq p := by
    simpa only [Function.comp_apply] using
      (e.sum_comp (fun a => (f.amplitude a p)^2 •
        SmoothingAtlas.phaseDifferentialSquare (f.phase a) p)).trans (f.sum_eq p)

end SmoothPrimitiveFamily

namespace CircularFamilyGeometry
local instance cycleGeometryFiberNormed_rf4ab46_3 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_rf4ab46_3 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_rf4ab46_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

local instance cycleGeometrySectionNormed_rf4ab46_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_rf4ab46_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The actual restored phase, allowing repeated copies of a chart. -/
def copiedPhases (q : CircularFamilyGeometry B ι) (a : ι) : M → ℝ :=
  B.circularPhase (q.curves a).index (q.linearPart a) (q.convexPart a)

end CircularFamilyGeometry

namespace ReferenceCircularAtlas
local instance cycleGeometryFiberNormed_rf4ab46_4 : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleGeometryFiberSpace_rf4ab46_4 : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleGeometryDualSmul_rf4ab46_3 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance cycleGeometrySectionNormed_rf4ab46_3 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleGeometrySectionSpace_rf4ab46_3 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def cycleLinearParts {N m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3))
    (q : CircularFamilyGeometry d.B (Fin (N*m))) (k : Fin N) (i : d.B.centers) (j : Fin 3) : Base :=
  q.linearPart (finProdFinEquiv (k,e.symm (i,j)))

def cycleWeights {N m : ℕ} (e : Fin m ≃ (d.B.centers × Fin 3))
    (q : CircularFamilyGeometry d.B (Fin (N*m))) (k : Fin N) (b : d.B.centers × Fin 3) : M → ℝ :=
  shrinkingCircularWeight (b.1 : M) (d.B.weight b.1) (d.radius b.1)
    (q.radius (finProdFinEquiv (k,e.symm b)))

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RelativeImmersionHPrinciple
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

def localizedImmersionRel (K : Set Plane) : RelLoc Plane Vec :=
  {q | q.1 ∉ K ∨ Function.Injective q.2.2}

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
end


