-- Prove2me | Definitions.Def_OAIQ249SI007
-- name    : OAIQ249SI007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T09:49:43.340278+00:00
-- url     : https://prove2.me/theorems/e9ac0cc0-e005-48a5-82e9-cd9e05f3a51c
-- title:
--   Definitions bundle OAIQ249SI007 of the split of OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 354 declarations of OpenAI's Lean: 248 definitions, 13 inductive types or structures and 93 theorems. The definitions and types are `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartProjectedNormal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularRadiusField`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_pairSupport`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_transitionScalar`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.euclideanChartRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasIndexDecidable`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteGlobalPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteIncrementIndexDecidable`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteSurfaceQuadratic`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.freeGlobalPhase`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.linearPhaseCatalog`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.localProjectedNormal`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.localQuadraticPhaseCatalog`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.localizedNormalField`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseSurfaceSupport`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseWeightCutoff`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveAtlasPolynomial`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.projectedNormalField`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.transitionScalar`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.unitProjectedNormalField`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.remainderBoundSectionNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMeanFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMeanFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMetricFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMetricFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolyFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolyFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolynomialMeanFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolynomialMeanFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredReadFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredReadFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.selfReadFiberNormed` and 221 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Immersion_ClosedSurface_ChartModel`, `Immersion_ClosedSurface_CrossModes`, `Immersion_ClosedSurface_ForcedModes`, `Immersion_ClosedSurface_FreeAmplitude`, `Immersion_ClosedSurface_GradientBounds`, `Immersion_ClosedSurface_JetBounds`, `Immersion_ClosedSurface_LocalMean`, `Immersion_ClosedSurface_MeanError`, `Immersion_ClosedSurface_MetricTensors`, `Immersion_ClosedSurface_ModeBounds`, `Immersion_ClosedSurface_NormalJets`, `Immersion_ClosedSurface_OscillatoryModel`, `Immersion_ClosedSurface_PhaseMean`, `Immersion_ClosedSurface_PhaseStock`, `Immersion_ClosedSurface_ProjectionStability`, `Immersion_ClosedSurface_QuadraticMean`, `Immersion_ClosedSurface_QuadraticSupport`, `Immersion_ClosedSurface_RealBounds`, `Immersion_ClosedSurface_RealModes`, `Immersion_ClosedSurface_SmoothCoordinates`, `SurfaceImmersion_Atlas_AtlasJetCoordinateRelation`, `SurfaceImmersion_Atlas_AtlasNormalProjection`, `SurfaceImmersion_Atlas_AtlasNormalProjectionBounds`, `SurfaceImmersion_Atlas_AtlasPhaseCatalog`, `SurfaceImmersion_Atlas_AtlasSelfTensorRead`, `SurfaceImmersion_Atlas_AtlasSupportedWeights`, `SurfaceImmersion_Atlas_AtlasTensorLocalBounds`, `SurfaceImmersion_Atlas_AtlasTensorTransition`, `SurfaceImmersion_Atlas_CenteredParabolicChart`, `SurfaceImmersion_Atlas_ChartedTrialAmplitude`, `SurfaceImmersion_Atlas_CompactPhaseFamily`, `SurfaceImmersion_Atlas_CoordinateQuadraticExpansion`, `SurfaceImmersion_Atlas_CoordinateTaylorIdentity`, `SurfaceImmersion_Atlas_CoordinateTensorPullback`, `SurfaceImmersion_Atlas_CrossAtlasJetRelation`, `SurfaceImmersion_Atlas_CrossAtlasTensorTransition`, `SurfaceImmersion_Atlas_EuclideanChartRead`, `SurfaceImmersion_Atlas_FiniteAtlasIncrement`, `SurfaceImmersion_Atlas_GoodPhaseCover`, `SurfaceImmersion_Atlas_GoodPhaseNeighborhood`, `SurfaceImmersion_Atlas_LinearPhaseChart`, `SurfaceImmersion_Atlas_LinearPhaseDerivativeBounds`, `SurfaceImmersion_Atlas_LocalizedCoordinatePullback`, `SurfaceImmersion_Atlas_NoncriticalPhaseCover`, `SurfaceImmersion_Atlas_ParabolicPhaseChart`, `SurfaceImmersion_Atlas_PhaseMarginCompact`, `SurfaceImmersion_Atlas_PhaseSupportCoordinates`, `SurfaceImmersion_Atlas_QuadraticPhaseCatalog`, `SurfaceImmersion_Atlas_RealPhaseChart`, `SurfaceImmersion_Atlas_RestrictedPhasePartition`, `SurfaceImmersion_Atlas_TangentMetricBounds`, `SurfaceImmersion_Atlas_UniformLinearPhaseBudgets`, `SurfaceImmersion_Correction_AtlasGlobalFreeModes`, `SurfaceImmersion_Correction_AtlasPolynomialLinearized`, `SurfaceImmersion_Correction_AtlasPolynomialRestoredRead`, `SurfaceImmersion_Correction_AtlasPrimitivePolynomial`, `SurfaceImmersion_Correction_AtlasRestoredPolynomialDirection`, `SurfaceImmersion_Correction_AtlasRestoredPolynomialRepresentation`, `SurfaceImmersion_Correction_AtlasSupportedPolynomialVariation`, `SurfaceImmersion_Correction_ChartedCombinedMean`, `SurfaceImmersion_Correction_ChartedFreeDisplacement`, `SurfaceImmersion_Correction_ChartedFreeResidual`, `SurfaceImmersion_Correction_ChartedFreeSeed`, `SurfaceImmersion_Correction_ChartedMeanData`, `SurfaceImmersion_Correction_ChartedMeanFamily`, `SurfaceImmersion_Correction_ChartedMeanFamilyData`, `SurfaceImmersion_Correction_ChartedMeanProfile`, `SurfaceImmersion_Correction_ChartedZeroMean`, `SurfaceImmersion_Correction_CombinedMeanGeometry`, `SurfaceImmersion_Correction_ConjugatedPolynomialOperator`, `SurfaceImmersion_Correction_CoordinateLinearizedResidual`, `SurfaceImmersion_Correction_CoordinatePolynomialPullback`, `SurfaceImmersion_Correction_CoordinatePolynomialRealization`, `SurfaceImmersion_Correction_CutoffTensorPolynomial`, `SurfaceImmersion_Correction_FiniteAtlasFreeMetric`, `SurfaceImmersion_Correction_FiniteSurfaceCorrection`, `SurfaceImmersion_Correction_GlobalSmoothedMetricStep`, `SurfaceImmersion_Correction_JetPolynomialDerivative`, `SurfaceImmersion_Correction_JetPolynomialFullCorrector`, `SurfaceImmersion_Correction_JetPolynomialScalar`, `SurfaceImmersion_Correction_JetPolynomialVector`, `SurfaceImmersion_Correction_LinearMeanBudgetsFromBounds`, `SurfaceImmersion_Correction_LinearPhaseMeanGeometry`, `SurfaceImmersion_Correction_MetricPolynomialSlowStep`, `SurfaceImmersion_Correction_PerturbationTaylorBounds`, `SurfaceImmersion_Correction_PerturbedMeanTransfer`, `SurfaceImmersion_Correction_PolynomialDiagonalVariations`, `SurfaceImmersion_Correction_PolynomialFiniteAssembly`, `SurfaceImmersion_Correction_PolynomialGeometry`, `SurfaceImmersion_Correction_PolynomialInteractionBounds`, `SurfaceImmersion_Correction_PolynomialJetRecursion`, `SurfaceImmersion_Correction_PolynomialMetricCoefficients`, `SurfaceImmersion_Correction_PolynomialMetricForcing`, `SurfaceImmersion_Correction_PolynomialMetricRemainder`, `SurfaceImmersion_Correction_PolynomialSolveData`, `SurfaceImmersion_Correction_PolynomialSolveFactors`, `SurfaceImmersion_Correction_PolynomialZeroPhaseExpansion`, `SurfaceImmersion_Correction_RealPolynomialQuadraticBounds`, `SurfaceImmersion_Correction_RealPolynomialVariationBounds`, `SurfaceImmersion_Correction_RestoredLinearizedMetric`, `SurfaceImmersion_Correction_RestoredPolynomialModeMean`, `SurfaceImmersion_Correction_RestoredQuadratureMean`, `SurfaceImmersion_Correction_SmoothCircularRadius`, `SurfaceImmersion_Correction_SmoothingTransition`, `SurfaceImmersion_Correction_SupportedMeanError`, `SurfaceImmersion_Correction_TensorMeanCoordinates`, `SurfaceImmersion_Correction_UniformGeometricMeanData`, `SurfaceImmersion_Correction_UniformLinearChartedMeanData`, `SurfaceImmersion_Correction_UniformLinearChartedMeanFamily`, `SurfaceImmersion_Correction_UniformPolynomialSmallIncrement`, `SurfaceImmersion_Geometry_ActualSecondFormFrame`, `SurfaceImmersion_Geometry_BoundaryJetAvoidance`, `SurfaceImmersion_Geometry_BoundaryJetCurvature`, `SurfaceImmersion_Geometry_BoundaryJetPositivity`, `SurfaceImmersion_Geometry_BoundaryJetSecondForm`, `SurfaceImmersion_Geometry_BoundaryNormalMatching`, `SurfaceImmersion_Geometry_BoundedCoefficientRecursion`, `SurfaceImmersion_Geometry_CoefficientJetBounds`, `SurfaceImmersion_Geometry_CompactAnsatzAsymptotics`, `SurfaceImmersion_Geometry_CompactNormalTriple`, `SurfaceImmersion_Geometry_CompactPositiveMetricJets`, `SurfaceImmersion_Geometry_CompactRealJetNeighborhood`, `SurfaceImmersion_Geometry_CovectorPullbackParameters`, `SurfaceImmersion_Geometry_ExplicitSplitCancellation`, `SurfaceImmersion_Geometry_FrozenBoundaryCoefficients`, `SurfaceImmersion_Geometry_GlobalMetricStepBound`, `SurfaceImmersion_Geometry_JetPullbackExpressions`, `SurfaceImmersion_Geometry_LocalizedTensorPullbackBound`, `SurfaceImmersion_Geometry_ManifoldMetricTensor`, `SurfaceImmersion_Geometry_MetricAcceleration`, `SurfaceImmersion_Geometry_MixedJetRegularity`, `SurfaceImmersion_Geometry_ModulatedJetScaling`, `SurfaceImmersion_Geometry_NormalFrameTransport`, `SurfaceImmersion_Geometry_PerturbedSolverTransfer`, `SurfaceImmersion_Geometry_ProjectedNormalLocal`, `SurfaceImmersion_Geometry_QuadraticInteraction`, `SurfaceImmersion_Geometry_RealQuadraticVariation`, `SurfaceImmersion_Geometry_RestoredMetricTensor`, `SurfaceImmersion_Geometry_ScalarJetTransport`, `SurfaceImmersion_Geometry_ShortMetricPath`, `SurfaceImmersion_Geometry_SplitSupportedBounds`, `SurfaceImmersion_Geometry_SplitSupportedTarget`, `SurfaceImmersion_Geometry_SupportedLocalMetricDefect`, `SurfaceImmersion_Geometry_SupportedNormalSeed`, `SurfaceImmersion_Geometry_SupportedRootAmplitude`, `SurfaceImmersion_Geometry_SurfaceTimeBlend`, `SurfaceImmersion_Geometry_TensorExpressionLinearMap`, `SurfaceImmersion_Geometry_TensorPullbackNorm`, `SurfaceImmersion_Geometry_TensorRealVariationBounds`, `SurfaceImmersion_Geometry_TimeBlendDomain`, `SurfaceImmersion_Geometry_TransverseCoefficientBounds`, `SurfaceImmersion_Geometry_UniformRemainderBound`, `SurfaceImmersion_Geometry_UniformStartingFamily`, `SurfaceImmersion_Geometry_UnperturbedGeometricSolver`, `SurfaceImmersion_Geometry_UnperturbedSolverFromBounds`, `SurfaceImmersion_Geometry_UnperturbedSolverRestrictedDomain`, `SurfaceImmersion_Geometry_VectorPlaneRestore`, `SurfaceImmersion_Primitive_BoundaryJetCrossings`, `SurfaceImmersion_Primitive_BoundaryProfileFrame`, `SurfaceImmersion_Primitive_BoundaryProfileGeometry`, `SurfaceImmersion_Primitive_CircularBoundaryProfiles`, `SurfaceImmersion_Primitive_CircularFamilyProfile`, `SurfaceImmersion_Primitive_IntrinsicExteriorCrossings`, `SurfaceImmersion_Primitive_JetVelocityCoordinates`, `SurfaceImmersion_Primitive_LocalPeriodicCalculus`, `SurfaceImmersion_Primitive_PeriodicFastEvaluation`, `SurfaceImmersion_Primitive_PeriodicFiniteAnsatz`, `SurfaceImmersion_Primitive_PhaseCrossingTransversality`, `SurfaceImmersion_Primitive_PhasePrimitiveSupport`, `SurfaceImmersion_Primitive_PhasePrimitiveTensor`, `SurfaceImmersion_Primitive_PrimitiveTermC1Bounds`, `SurfaceImmersion_Primitive_SecondCoefficientProfiles`, `SurfaceImmersion_Primitive_SurfaceVelocityFamily`, `SurfaceImmersion_Primitive_UniformPrimitiveProfiles`, `SurfaceImmersion_Primitive_VelocityNormalNonvanishing`, `SurfaceImmersion_Whitney_DoubleLocusSmoothStructure`.
--
--   **Imports.** It imports the published bundle `Def_SurfaceImmersion`; the bundle `OAIQ249SI008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ249SI010` and `OAIQ249SI011`; the statements `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_supported_patch_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_phase_exterior_preservation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_cross_phase_exterior_control`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exists_generic_circular_radii`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exterior_projected_normal_close_closure`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_catalog_atlas_cancellation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_exterior_crossing_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_cubic_remainder_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_term_background_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_small_metric_prepared_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_atlas_convex_phases`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_remainder_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_scaled_path_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_join_time_charts`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_signed_diagonal_filling`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_crosscap_connecting_arc_endpoint_regular`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_crosscap_source_geometry`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_smooth_interior_double_arc`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_linear_unperturbed_solver`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomial_nonlinear_unperturbed_solver`, `OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_polynomial_supported_linear_mean_data`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.uniform_linear_perturbed_mean_family_all_profiles`, `OAI.ClosedSurfaceR4.PhaseGeometry.CompactPhaseFamily.uniform_polynomial_solvers_all_profiles`, `OAI.ClosedSurfaceR4.PhaseGeometry.anchored_polynomial_grid_phases`, `OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_profiled_split_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_relative_phase_polynomial_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_uniform_polynomial_nearby_cancellation_all_profiles`, `OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets`, `OAI.ClosedSurfaceR4.RealModes.polynomial_inverse_chart_twoJet_bound` and `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_surface_collar_family`; the proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_supported_patch_geometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PhaseBoundaryCurve.exterior_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_phase_exterior_crossing_preservation`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_boundary_matching`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.compact_surface_phase_exterior_preservation`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exists_generic_circular_radii`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_exists_transverse_circular_radii`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_nonlinear_lowJet_neighborhood_of_C2`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_small_metric_prepared_family`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_remainder_C1_bound`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_half_arc_neighborhood`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crosscap_source_embedded_path`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_crosscap_coordinate_strip`, `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_metricPhaseData_of_whitney`, `OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation`, `OAI_ClosedSurfaceR4_PhaseGeometry_polynomial_inverse_chart_bound`, `OAI_ClosedSurfaceR4_PhaseGeometry_positive_good_phase_data`, `OAI.ClosedSurfaceR4.RealModes.realTwoJet_linear_prefix_bound`, `OAI_ClosedSurfaceR4_SurfaceVelocityFamily_actual_surface_collar_family` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family`.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
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
import Definitions.Def_OAIQ249SI008

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

lemma partial_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q - G q) p = coordDeriv v F p - coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_sub hF hG, sub_apply]


def linearizedMetric {n : ℕ} (G Z : Field n) (v w : Base) (p : Base) : ℂ :=
  coordDeriv v G p ⬝ᵥ coordDeriv w Z p + coordDeriv w G p ⬝ᵥ coordDeriv v Z p

section Gram
variable {n : ℕ}

lemma dot_tangentLift_left (X Y : Ambient n) (hD : gramDet X Y ≠ 0) (ux uy : ℂ) :
    X ⬝ᵥ tangentLift X Y ux uy = ux := by
  simp only [tangentLift, dotProduct_add, dotProduct_smul, smul_eq_mul, liftX, liftY]
  field_simp
  simp only [gramDet] at *
  ring

lemma dot_tangentLift_right (X Y : Ambient n) (hD : gramDet X Y ≠ 0) (ux uy : ℂ) :
    Y ⬝ᵥ tangentLift X Y ux uy = uy := by
  simp only [tangentLift, dotProduct_add, dotProduct_smul, smul_eq_mul, liftX, liftY,
    dotProduct_comm Y X]
  field_simp
  simp only [gramDet] at *
  ring


lemma dot_normalPart_left (X Y W : Ambient n) (hD : gramDet X Y ≠ 0) :
    X ⬝ᵥ normalPart X Y W = 0 := by
  simp only [normalPart, dotProduct_sub, dot_tangentLift_left X Y hD, sub_self]

lemma dot_normalPart_right (X Y W : Ambient n) (hD : gramDet X Y ≠ 0) :
    Y ⬝ᵥ normalPart X Y W = 0 := by
  simp only [normalPart, dotProduct_sub, dot_tangentLift_right X Y hD, sub_self]

end Gram

section CoordinateCalculus
variable {n : ℕ}

def covector (G Z : Field n) (v : Base) (p : Base) : ℂ := coordDeriv v G p ⬝ᵥ Z p

end CoordinateCalculus

section Phase
variable {n : ℕ}


def conjugatedMetric (τ : ℝ) (G Z : Field n) (v w : Base) (p : Base) : ℂ :=
  linearizedMetric G Z v w p + (Complex.I / (τ : ℂ)) *
    ((v.1 : ℂ) * covector G Z w p + (w.1 : ℂ) * covector G Z v p)

end Phase

section SmoothFormulas
variable {n : ℕ}

lemma contDiffAt_dot {F G : Field n} {p : Base}
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p) :
    ContDiffAt ℝ ∞ (fun q => F q ⬝ᵥ G q) p := by
  unfold dotProduct
  exact ContDiffAt.sum fun i _ => (contDiffAt_pi.mp hF i).mul (contDiffAt_pi.mp hG i)

lemma contDiffAt_gramDet {X Y : Field n} {p : Base}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) :
    ContDiffAt ℝ ∞ (fun q => gramDet (X q) (Y q)) p :=
  ((contDiffAt_dot hX hX).mul (contDiffAt_dot hY hY)).sub ((contDiffAt_dot hX hY).pow 2)

end SmoothFormulas

section LinearStructure
variable {n : ℕ}

lemma tangentLift_mul (X Y : Ambient n) (a ux uy : ℂ) :
    tangentLift X Y (a * ux) (a * uy) = a • tangentLift X Y ux uy := by
  have hx : liftX X Y (a * ux) (a * uy) = a * liftX X Y ux uy := by
    unfold liftX
    ring
  have hy : liftY X Y (a * ux) (a * uy) = a * liftY X Y ux uy := by
    unfold liftY
    ring
  simp only [tangentLift, hx, hy, smul_add, smul_smul]

lemma conjugatedMetric_sub (τ : ℝ) (G : Field n) {Z W : Field n} {p : Base}
    (hZ : DifferentiableAt ℝ Z p) (hW : DifferentiableAt ℝ W p) (v w : Base) :
    conjugatedMetric τ G (fun q => Z q - W q) v w p =
      conjugatedMetric τ G Z v w p - conjugatedMetric τ G W v w p := by
  unfold conjugatedMetric linearizedMetric covector
  rw [partial_sub hZ hW, partial_sub hZ hW]
  simp only [dotProduct_sub]
  ring

lemma contDiffAt_conjugatedMetric (τ : ℝ) {G Z : Field n} {p : Base}
    (hG : ContDiffAt ℝ ∞ G p) (hZ : ContDiffAt ℝ ∞ Z p) (v w : Base) :
    ContDiffAt ℝ ∞ (conjugatedMetric τ G Z v w) p := by
  have hX := contDiffAt_coordDeriv hG v
  have hY := contDiffAt_coordDeriv hG w
  have hZv := contDiffAt_coordDeriv hZ v
  have hZw := contDiffAt_coordDeriv hZ w
  exact ((contDiffAt_dot hX hZw).add (contDiffAt_dot hY hZv)).add
    (contDiffAt_const.mul ((contDiffAt_const.mul (contDiffAt_dot hY hZ)).add
      (contDiffAt_const.mul (contDiffAt_dot hX hZ))))


abbrev Tensor := Base → Fin 3 → ℂ

end LinearStructure

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ModeBounds
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



lemma ModeDomain.smoothAt {G : Field n} {U : Set Base} (h : ModeDomain G U)
    {p : Base} (hp : p ∈ U) : ContDiffAt ℝ ∞ G p :=
  (h.smooth p hp).contDiffAt (h.isOpen.mem_nhds hp)

lemma tangentLift_columns (G : Field n) (p : Base) (u v : ℂ) :
    tangentLift (coordDeriv dx G p) (coordDeriv dy G p) u v =
      u • tangentDualX G p + v • tangentDualY G p := by
  ext i
  simp only [tangentLift, tangentDualX, tangentDualY, liftX, liftY,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Quantitative
end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

def crossPair {n : ℕ} (θ ψ : ℝ) (A B : CVec n) : ℝ :=
  ((phase (θ - ψ) * (A ⬝ᵥ conjugate B)).re +
    (phase (θ + ψ) * (A ⬝ᵥ B)).re) / 2




def meanMetric {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Base → CVec n) (v w p : Base) : ℝ :=
  ∑ i, zeroPair (derivativeAmplitude τ (φ i) (Z i) v p)
    (derivativeAmplitude τ (φ i) (Z i) w p)



end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GradientBounds
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


def gradientAmplitude {n : ℕ} (τ : ℝ) (Z : Field n) (v : Base) : Field n :=
  fun p => coordDeriv v Z p + (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p

lemma contDiffOn_gradientAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {Z : Field n} (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) (v : Base) :
    ContDiffOn ℝ ∞ (gradientAmplitude τ Z v) U := by
  have hh : ContDiffOn ℝ ∞ (fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • Z p) U := by
    simpa only [Pi.smul_def'] using
      (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul hZ
  exact (contDiffOn_coordDeriv_vector hU hZ v).add hh

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanError
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



structure FreeCoefficient {n : ℕ} (G : Field n) (U : Set Base) (V : Field n) : Prop where
  smooth : ContDiffOn ℝ ∞ V U
  perpX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0
  perpY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0
  perpSecond : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0


def leadingDerivative {n : ℕ} (τ : ℝ) (V : Field n) (v : Base) : Field n :=
  fun p => (Complex.I / (τ : ℂ) * (v.1 : ℂ)) • V p

lemma contDiffOn_leadingDerivative {n : ℕ} (τ : ℝ) {V : Field n} {U : Set Base}
    (hV : ContDiffOn ℝ ∞ V U) (v : Base) :
    ContDiffOn ℝ ∞ (leadingDerivative τ V v) U := by
  unfold leadingDerivative
  simpa only [Pi.smul_def'] using
    (contDiffOn_const (c := Complex.I / (τ : ℂ) * (v.1 : ℂ))).smul hV

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealModes
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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

lemma complexify_dot {n : ℕ} (X Y : RVec n) :
    complexify X ⬝ᵥ complexify Y = (X ⬝ᵥ Y : ℝ) := by
  simp [dotProduct, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

lemma complexify_gram (X Y : RVec 4) :
    gramDet (complexify X) (complexify Y) = (NormalFrame.gramDet X Y : ℝ) := by
  simp [gramDet, NormalFrame.gramDet, complexify_dot]

lemma complexify_normalPart (X Y W : RVec 4) :
    complexify (realNormalPart X Y W) = normalPart (complexify X) (complexify Y) (complexify W) := by
  ext i
  simp [realNormalPart, normalPart, tangentLift, liftX, liftY, complexify_dot, complexify_gram]
  ring

lemma realNormalPart_perp (X Y W : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    X ⬝ᵥ realNormalPart X Y W = 0 ∧ Y ⬝ᵥ realNormalPart X Y W = 0 := by
  have hd : gramDet (complexify X) (complexify Y) ≠ 0 := by
    rw [complexify_gram]; exact Complex.ofReal_ne_zero.mpr hD
  constructor
  · exact Complex.ofReal_injective (by
      rw [← complexify_dot, complexify_normalPart]; exact dot_normalPart_left _ _ _ hd)
  · exact Complex.ofReal_injective (by
      rw [← complexify_dot, complexify_normalPart]; exact dot_normalPart_right _ _ _ hd)

lemma coordDeriv_complexify {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (v : Base) :
    coordDeriv v (fun q => complexify (F q)) p = complexify (coordDeriv v F p) := by
  exact congrArg (fun A : Base →L[ℝ] Ambient n => A v)
    (((complexifyCLM n).hasFDerivAt.comp p hF.hasFDerivAt).fderiv)

lemma contDiff_complexify {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p => complexify (F p)) := (complexifyCLM n).contDiff.comp hF

lemma contDiff_real_coordDeriv {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F) (v : Base) :
    ContDiff ℝ ∞ (coordDeriv v F) := by
  exact (hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

def realSecond (F : RField 4) : RField 4 := fun p =>
  realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv dy (coordDeriv dy F) p)

lemma complexify_realSecond {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    complexify (realSecond F p) = goodSecond (fun p => complexify (F p)) p := by
  have hd (v : Base) : coordDeriv v (fun q => complexify (F q)) =
      fun q => complexify (coordDeriv v F q) := by
    funext q; exact coordDeriv_complexify (hF.differentiable (by simp) q) v
  unfold realSecond goodSecond secondForm
  rw [hd dx, hd dy, coordDeriv_complexify ((contDiff_real_coordDeriv hF dy).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  exact complexify_normalPart _ _ _


structure RealModeDomain (F : RField 4) (U : Set Base) : Prop where
  isOpen : IsOpen U
  determinant : ∀ p ∈ U, NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0
  good : ∀ p ∈ U, realSecond F p ≠ 0

lemma RealModeDomain.complexDomain {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) :
    ModeDomain (fun p => complexify (F p)) U := by
  refine ⟨h.isOpen, (contDiff_complexify hF).contDiffOn, ?_, ?_⟩
  · intro p hp
    rw [coordDeriv_complexify (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p),
      coordDeriv_complexify (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p), complexify_gram]
    exact Complex.ofReal_ne_zero.mpr (h.determinant p hp)
  · intro p hp
    rw [← complexify_realSecond hF, complexify_dot]
    exact Complex.ofReal_ne_zero.mpr ((dotProduct_self_eq_zero).not.mpr (h.good p hp))

def freeNormal (F : RField 4) : RField 4 := fun p =>
  NormalFrame.unitPerp (coordDeriv dx F p) (coordDeriv dy F p) (realSecond F p)

lemma freeNormal_perp (F : RField 4) (p : Base) :
    coordDeriv dx F p ⬝ᵥ freeNormal F p = 0 ∧
    coordDeriv dy F p ⬝ᵥ freeNormal F p = 0 ∧ realSecond F p ⬝ᵥ freeNormal F p = 0 :=
  NormalFrame.unitPerp_orthogonal _ _ _


def freeSeed (δ τ : ℝ) (b : Base → ℝ) (F : RField 4) : Field 4 := fun p =>
  ((Real.sqrt 2 * δ * τ * b p : ℝ) : ℂ) • complexify (freeNormal F p)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def coordinateCenter (p : M) : Base := planeCoordinates (extChartAt planeModel p p)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealBounds
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

lemma norm_complexify {n : ℕ} (X : RVec n) : ‖complexify X‖ = ‖X‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr
    intro i
    simpa only [complexify_apply, Complex.norm_real] using norm_le_pi_norm X i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (complexify X))).mpr
    intro i
    simpa only [complexify_apply, Complex.norm_real] using norm_le_pi_norm (complexify X) i

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseMean
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.RootMean ClosedSurfaceR4.WeightedEstimates
open Set



lemma firstDirection_norm (i : Fin 3) : ‖firstDirection i‖ ≤ 1 := by
  fin_cases i <;> (first | (simp [firstDirection, dx, dy, Prod.norm_def]; all_goals first | (norm_num [firstDirection, dx, dy, Prod.norm_def]; done) | rfl | decide) | (norm_num [firstDirection, dx, dy, Prod.norm_def]; done) | norm_num [firstDirection, dx, dy, Prod.norm_def])
lemma secondDirection_norm (i : Fin 3) : ‖secondDirection i‖ ≤ 1 := by
  fin_cases i <;> (first | (simp [secondDirection, dx, dy, Prod.norm_def]; all_goals first | (norm_num [secondDirection, dx, dy, Prod.norm_def]; done) | rfl | decide) | (norm_num [secondDirection, dx, dy, Prod.norm_def]; done) | norm_num [secondDirection, dx, dy, Prod.norm_def])



def coefficient (Q : Base → Tensor →L[ℝ] ℝ) (e : Base → Base) (A : Base → Tensor) : Base → ℝ :=
  fun p => Q p (A (e p))



end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set

lemma contDiffOn_coefficient {U V : Set Base} {Q : Base → Tensor →L[ℝ] ℝ}
    {e : Base → Base} {A : Base → Tensor} (hQ : ContDiffOn ℝ ∞ Q V)
    (he : ContDiffOn ℝ ∞ e V) (heU : MapsTo e V U) (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (coefficient Q e A) V :=
  hQ.clm_apply (hA.comp he heU)




lemma coefficient_trial_range {U V : Set Base} {Q : Base → Tensor →L[ℝ] ℝ}
    {e : Base → Base} {reference A : Base → Tensor} {r ρ R : ℝ}
    (heU : MapsTo e V U)
    (hmargin : ∀ p ∈ V, ρ + ‖Q p‖ * r ≤ coefficient Q e reference p ∧
      coefficient Q e reference p ≤ R - ‖Q p‖ * r)
    (hA : InTrialBall U reference r A) : MapsTo (coefficient Q e A) V (Icc ρ R) := by
  intro p hp
  have hnorm : ‖coefficient Q e A p - coefficient Q e reference p‖ ≤ ‖Q p‖ * r := by
    rw [coefficient, coefficient, ← map_sub]
    exact (ContinuousLinearMap.le_opNorm (Q p) _).trans
      (mul_le_mul_of_nonneg_left (hA (e p) (heU hp)).le (norm_nonneg _))
  have hb := abs_le.mp (show |coefficient Q e A p - coefficient Q e reference p| ≤ ‖Q p‖ * r by
    simpa only [Real.norm_eq_abs] using hnorm)
  obtain ⟨hl, hu⟩ := hmargin p hp
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (realPartCLM)

def realLinearized {n : ℕ} (F U : RField n) (v w p : Base) : ℝ :=
  coordDeriv v F p ⬝ᵥ coordDeriv w U p + coordDeriv w F p ⬝ᵥ coordDeriv v U p

def realLinearizedTensor {n : ℕ} (F U : RField n) : Base → Fin 3 → ℝ :=
  fun p => ![realLinearized F U dx dx p, realLinearized F U dx dy p,
    realLinearized F U dy dy p]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_dot {n : ℕ} {U : Set Base} {X Y : Field n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (fun p => X p ⬝ᵥ Y p) U := by
  exact ContDiffOn.sum fun i _ => (contDiffOn_pi.mp hX i).mul (contDiffOn_pi.mp hY i)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
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
open ClosedSurfaceR4.QuadraticMean (zeroPair derivativeAmplitude conjugate displacement
  doublePair crossPair realMode sumDisplacement quadraticMetric )
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)


def phaseZeroTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : SmallModes.Field n) :
    Base → PhaseMean.Tensor :=
  fun p i => zeroPair (derivativeAmplitude τ φ Z (firstDirection i) p)
    (derivativeAmplitude τ φ Z (secondDirection i) p)


def phaseDoubleTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : SmallModes.Field n) :
    SmallModes.Tensor :=
  fun p i => (derivativeAmplitude τ φ Z (firstDirection i) p ⬝ᵥ
    derivativeAmplitude τ φ Z (secondDirection i) p) / 2

def phasePlusTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : SmallModes.Field n) :
    SmallModes.Tensor :=
  fun p i => (derivativeAmplitude τ φ Z (firstDirection i) p ⬝ᵥ
    derivativeAmplitude τ ψ W (secondDirection i) p) / 2

def phaseMinusTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : SmallModes.Field n) :
    SmallModes.Tensor :=
  fun p i => (derivativeAmplitude τ φ Z (firstDirection i) p ⬝ᵥ
    conjugate (derivativeAmplitude τ ψ W (secondDirection i) p)) / 2

def zeroPhaseSum {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → SmallModes.Field n) : Base → PhaseMean.Tensor :=
  fun p => ∑ i, phaseZeroTensor τ (φ i) (Z i) p

def nonzeroPhaseSum {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → SmallModes.Field n) : Base → PhaseMean.Tensor :=
  fun p => (∑ i, displacement τ (fun q => 2 * φ i q) (phaseDoubleTensor τ (φ i) (Z i)) p) +
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      (displacement τ (fun q => φ i q - φ j q) (phaseMinusTensor τ (φ i) (φ j) (Z i) (Z j)) p +
        displacement τ (fun q => φ i q + φ j q) (phasePlusTensor τ (φ i) (φ j) (Z i) (Z j)) p)



end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.QuadraticMean
open ClosedSurfaceR4.SmallModes (coordDeriv)
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RealModes (contDiffOn_dot)

lemma contDiffOn_derivativeAmplitude {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ : Base → ℝ} {Z : Base → CVec n} (hφ : ContDiffOn ℝ ∞ φ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) (v : Base) :
    ContDiffOn ℝ ∞ (derivativeAmplitude τ φ Z v) U := by
  have hdφ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hφ v
  have hdZ := ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU hZ v
  have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn hdφ
  change ContDiffOn ℝ ∞ (fun p => fderiv ℝ Z p v +
    (Complex.I / (τ : ℂ) * ((fderiv ℝ φ p v : ℝ) : ℂ)) • Z p) U
  exact hdZ.add (((contDiffOn_const (c := Complex.I / (τ : ℂ))).mul hc).smul hZ)

end ClosedSurfaceR4.QuadraticMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude conjugate)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_phasePlusTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (phasePlusTensor τ φ ψ Z W) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact (contDiffOn_dot (QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ _)
    (QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ _)).div_const 2

lemma contDiffOn_phaseMinusTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {φ ψ : Base → ℝ} {Z W : Field n} (hφ : ContDiffOn ℝ ∞ φ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : ContDiffOn ℝ ∞ W U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (phaseMinusTensor τ φ ψ Z W) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact (contDiffOn_dot (QuadraticMean.contDiffOn_derivativeAmplitude hU hφ hZ τ _)
    (QuadraticMean.contDiffOn_conjugate
      (QuadraticMean.contDiffOn_derivativeAmplitude hU hψ hW τ _))).div_const 2



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_FreeAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates Set
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude zeroPair)


def chartLeadingTensor (b : Base → ℝ) (χ : Base → Base) : Base → PhaseMean.Tensor :=
  fun p => pullbackField χ p
    (fun i => b (χ p) ^ 2 * (firstDirection i).1 * (secondDirection i).1)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JetBounds
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




namespace LowJet
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma contDiffAt_dot {F G : E → Ambient n} {p : E}
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p) :
    ContDiffAt ℝ ∞ (fun q => F q ⬝ᵥ G q) p := by
  unfold dotProduct
  exact ContDiffAt.sum fun i _ => (contDiffAt_pi.mp hF i).mul (contDiffAt_pi.mp hG i)

lemma contDiffAt_gramDet {X Y : E → Ambient n} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) :
    ContDiffAt ℝ ∞ (fun q => gramDet (X q) (Y q)) p :=
  ((contDiffAt_dot hX hX).mul (contDiffAt_dot hY hY)).sub ((contDiffAt_dot hX hY).pow 2)

lemma contDiffAt_liftX {X Y : E → Ambient n} {ux uy : E → ℂ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftX (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hY hY).mul hx).sub ((contDiffAt_dot hX hY).mul hy))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_liftY {X Y : E → Ambient n} {ux uy : E → ℂ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => liftY (X q) (Y q) (ux q) (uy q)) p :=
  contDiffAt_cdiv (((contDiffAt_dot hX hX).mul hy).sub ((contDiffAt_dot hX hY).mul hx))
    (contDiffAt_gramDet hX hY) hD

lemma contDiffAt_tangentLift {X Y : E → Ambient n} {ux uy : E → ℂ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p)
    (hx : ContDiffAt ℝ ∞ ux p) (hy : ContDiffAt ℝ ∞ uy p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => tangentLift (X q) (Y q) (ux q) (uy q)) p :=
  ((contDiffAt_liftX hX hY hx hy hD).smul hX).add ((contDiffAt_liftY hX hY hx hy hD).smul hY)

lemma contDiffAt_normalPart {X Y W : E → Ambient n} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hY : ContDiffAt ℝ ∞ Y p) (hW : ContDiffAt ℝ ∞ W p)
    (hD : gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => normalPart (X q) (Y q) (W q)) p :=
  hW.sub (contDiffAt_tangentLift hX hY (contDiffAt_dot hX hW) (contDiffAt_dot hY hW) hD)



end LowJet

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set






structure LocalBounds (U V : Set Base) (s r ρ R : ℝ) (reference : Base → Tensor)
    (F : RField 4) (ψ : Base → ℝ) (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) : Prop where
  openU : IsOpen U
  smoothF : ContDiff ℝ ∞ F
  domain : RealModeDomain F V
  smoothPsi : ContDiffOn ℝ ∞ ψ V
  smoothQ : ContDiffOn ℝ ∞ Q V
  smoothChi : ContDiffOn ℝ ∞ χ U
  smoothInv : ContDiffOn ℝ ∞ e V
  chiInto : MapsTo χ U V
  invInto : MapsTo e V U
  smoothPullback : ContDiffOn ℝ ∞ (pullbackField χ) U
  margin : ∀ p ∈ V, ρ + ‖Q p‖ * r ≤ coefficient Q e reference p ∧
    coefficient Q e reference p ≤ R - ‖Q p‖ * r



structure Budgets (U V : Set Base) (s : ℝ) (F : RField 4) (ψ : Base → ℝ)
    (Q : Base → Tensor →L[ℝ] ℝ) (χ e : Base → Base) where
  inv : ℕ → ℝ
  chi : ℕ → ℝ
  psi : ℕ → ℝ
  forms : ℕ → ℝ
  pull : ℕ → ℝ
  normal : ℕ → ℝ
  mode : ℕ → ℝ
  inv_pos : ∀ m, 1 ≤ inv m
  chi_pos : ∀ m, 1 ≤ chi m
  psi_pos : ∀ m, 1 ≤ psi m
  forms_pos : ∀ m, 1 ≤ forms m
  pull_pos : ∀ m, 1 ≤ pull m
  normal_pos : ∀ m, 1 ≤ normal m
  mode_pos : ∀ m, 1 ≤ mode m
  inv_bound : ∀ m j, 1 ≤ j → j ≤ m → ∀ p ∈ V, ‖iteratedFDerivWithin ℝ j e V p‖ ≤ inv m
  chi_bound : ∀ m j, 1 ≤ j → j ≤ m → ∀ p ∈ U, ‖iteratedFDerivWithin ℝ j χ U p‖ ≤ chi m
  psi_bound : ∀ m, WeightedBound V s m (psi m) ψ
  forms_bound : ∀ m, WeightedBound V s m (forms m) Q
  pull_bound : ∀ m, WeightedBound U s m (pull m) (pullbackField χ)
  normal_bound : ∀ m, WeightedBound V s m (normal m) (freeNormal F)
  mode_bound : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) V s m (mode m)

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}


def inputFactor (d : Budgets U V s F ψ Q χ e) (m : ℕ) : ℝ :=
  2 ^ m * d.forms m * (m.factorial : ℝ) * d.inv m ^ m

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates ClosedSurfaceR4.FiniteMean
open Set
variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

def outputFactor (d : Budgets U V s F ψ Q χ e) (m : ℕ) : ℝ :=
  2 ^ m * d.pull m * (m.factorial : ℝ) * d.chi m ^ m

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
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

def normalFromJet (J : RealTwoJet) : RVec 4 :=
  NormalFrame.unitPerp (J 0) (J 1) (realNormalPart (J 0) (J 1) (J 4))

structure RealJetDomain (Ω : Set RealTwoJet) : Prop where
  isOpen : IsOpen Ω
  determinant : ∀ J ∈ Ω, NormalFrame.gramDet (J 0) (J 1) ≠ 0
  good : ∀ J ∈ Ω, realNormalPart (J 0) (J 1) (J 4) ≠ 0

lemma contDiffAt_realNormalPart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X Y W : E → RVec 4} {p : E} (hX : ContDiffAt ℝ ∞ X p)
    (hY : ContDiffAt ℝ ∞ Y p) (hW : ContDiffAt ℝ ∞ W p)
    (hD : NormalFrame.gramDet (X p) (Y p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => realNormalPart (X q) (Y q) (W q)) p := by
  have hx := (complexifyCLM 4).contDiff.contDiffAt.comp p hX
  have hy := (complexifyCLM 4).contDiff.contDiffAt.comp p hY
  have hw := (complexifyCLM 4).contDiff.contDiffAt.comp p hW
  have hd : gramDet (complexify (X p)) (complexify (Y p)) ≠ 0 := by
    rw [complexify_gram]; exact Complex.ofReal_ne_zero.mpr hD
  have hh := LowJet.contDiffAt_normalPart hx hy hw hd
  apply contDiffAt_pi.mpr
  intro i
  have hi := Complex.reCLM.contDiff.contDiffAt.comp p (contDiffAt_pi.mp hh i)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  exact congrArg Complex.re (congrFun (complexify_normalPart (X q) (Y q) (W q)) i)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseStock
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



abbrev PhaseInput (n : ℕ) := (Fin 3 → RVec n) × PhaseMean.Tensor

end ClosedSurfaceR4.PhaseGeometry

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

def secondJetTriple (F : RField 4) (p : Base) : Fin 3 → RVec 4 :=
  ![coordDeriv dx (coordDeriv dx F) p,
    coordDeriv dx (coordDeriv dy F) p,
    coordDeriv dy (coordDeriv dy F) p]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticSupport
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
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



lemma derivativeAmplitude_zero_of_notMem {n : ℕ} {Z : Field n} {p : Base}
    (hp : p ∉ tsupport Z) (τ : ℝ) (φ : Base → ℝ) (v : Base) :
    derivativeAmplitude τ φ Z v p = 0 := by
  simp [derivativeAmplitude, fderiv_of_notMem_tsupport ℝ hp, image_eq_zero_of_notMem_tsupport hp]

lemma phasePlusTensor_tsupport {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : Field n) :
    tsupport (phasePlusTensor τ φ ψ Z W) ⊆ tsupport Z ∩ tsupport W := by
  apply closure_minimal _ ((isClosed_tsupport Z).inter (isClosed_tsupport W))
  intro p hp
  constructor
  · by_contra hn
    exact hp (by ext i; simp [phasePlusTensor, derivativeAmplitude_zero_of_notMem hn])
  · by_contra hn
    exact hp (by ext i; simp [phasePlusTensor, derivativeAmplitude_zero_of_notMem hn])

lemma phaseMinusTensor_tsupport {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ) (Z W : Field n) :
    tsupport (phaseMinusTensor τ φ ψ Z W) ⊆ tsupport Z ∩ tsupport W := by
  apply closure_minimal _ ((isClosed_tsupport Z).inter (isClosed_tsupport W))
  intro p hp
  constructor
  · by_contra hn
    exact hp (by ext i; simp [phaseMinusTensor, derivativeAmplitude_zero_of_notMem hn])
  · by_contra hn
    exact hp (by ext i; simp [phaseMinusTensor, derivativeAmplitude_zero_of_notMem hn,
      conjugate, dotProduct])

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

def coordDet (A : Base →L[ℝ] Base) : ℝ :=
  (A dx).1*(A dy).2-(A dx).2*(A dy).1

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

lemma pairWeight_smooth (i j : A.centers) : ContDiff ℝ ∞ (A.pairWeight i j) :=
  localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (A.outer_smooth j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.sectionTensorNormed
local instance sectionTensorSpace_r3832e2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorDecode_smooth {f : Base → A.centers → TensorFiber} (hf : ContDiff ℝ ∞ f) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.tensorDecode f x)) := by
  apply ContMDiff.sum_section
  intro i _
  exact A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i (contDiff_pi.mp hf i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
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

variable [FiniteDimensional ℝ P] [CompleteSpace E]

def primitiveOn (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) : P → C(Period, E) :=
  bundleOn (fun z : P × ℝ => PeriodicPrimitive.primitive (fun t => F z.1 (t : Period)) z.2)
    S hS (PeriodicPrimitive.contDiffOn_primitive_joint hS hF)
    (fun p hp => PeriodicPrimitive.primitive_periodic
      ((F p).continuous.comp (AddCircle.continuous_mk' 1)) (periodic_lift F p)
      ((PeriodicPrimitive.integral_lift_eq_haar (F p)).trans (hm p hp)))

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

def order : MixedExpression → ℕ
  | .coeff _ => 2
  | .atom _ w _ e => max w.length e.order
  | .add e f => max e.order f.order

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ModulatedJetScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaling each oscillatory amplitude independently. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.ModulatedJets
open WeightedEstimates MixedExpression

def scaleDirections (H : DirectionFields) (c : Fin 3 → ℝ) : DirectionFields :=
  fun j p => c j • H j p

end ClosedSurfaceR4.JetPolynomial.ModulatedJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ConjugatedPolynomialOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The oscillatory estimates apply to the actual conjugated polynomial
linearization on supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

def singleDirection (H : Base → Fin 4 → ℂ) : DirectionFields := ![H, 0, 0]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SupportedMeanError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual zero-phase metric error is bilinear in the free seeds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial

variable {n : ℕ} {K : Compacts Base}

def seedMeanError (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w p : Base) : ℝ :=
  QuadraticMean.zeroPair (gradientAmplitude τ (T V) v p) (gradientAmplitude τ (T W) w p) -
    QuadraticMean.zeroPair (leadingDerivative τ V v p) (leadingDerivative τ W w p)

lemma seedMeanError_smooth (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w : Base) :
    ContDiff ℝ ∞ (seedMeanError τ T V W v w) := by
  apply contDiffOn_univ.mp
  exact (QuadraticMean.contDiffOn_zeroPair
    (contDiffOn_gradientAmplitude isOpen_univ (T V).contDiff.contDiffOn τ v)
    (contDiffOn_gradientAmplitude isOpen_univ (T W).contDiff.contDiffOn τ w)).sub
    (QuadraticMean.contDiffOn_zeroPair (contDiffOn_leadingDerivative τ V.contDiff.contDiffOn v)
      (contDiffOn_leadingDerivative τ W.contDiff.contDiffOn w))

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedNormalSeed
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

lemma freeSeed_tsupport (δ τ : ℝ) (b : Base → ℝ) (F : RField 4) :
    tsupport (freeSeed δ τ b F) ⊆ tsupport b := by
  apply closure_mono
  intro p hp
  by_contra hn
  have hb : b p = 0 := by simpa only [Function.mem_support, not_not] using hn
  exact hp (by simp only [freeSeed, hb, mul_zero, Complex.ofReal_zero, zero_smul])

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate operator used in the finite parametrix really is the
linearization of the polynomial perturbation on real oscillatory fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open ModulatedJets

/-- Polynomial first variation in the product coordinates of the metric solver. -/
def coordinateRealLinearized {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) (t : ℝ) : SmallModes.Base → Fin 3 → ℝ :=
  fun p i => linearized (P i) ε G (X ∘ planeCoordinateIsometry) t (planeCoordinateIsometry.symm p)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinateLinearizedResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact realization of the full perturbed linear residual in real fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open SmallModes

/-- The actual metric derivative plus the actual polynomial derivative,
written in the coordinates used by the finite solver. -/
def coordinateFullLinearized {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) : SmallModes.Base → Fin 3 → ℝ :=
  RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
    coordinateRealLinearized P ε G X 0


end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealQuadraticVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real quadratic variation is the sum of its zero and double phases. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

def realDirectionJets (J : DirectionJets) : DirectionJets := fun w a p => (J w a p).re

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialZeroPhaseExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the actual polynomial Hessian into its zero-phase part and
explicit doubled and mixed phases. Ordered pairs retain all multiplicities. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets
namespace Perturbation

def quadraticOscillation {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) : ℝ :=
  (∑ i, ∑ j, (phase τ (fun x => φ i x + φ j x) p *
    quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re) +
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (phase τ (fun x => φ i x - φ j x) p *
      quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
        (H i) (starField (H j)) τ t p).re

end Perturbation
end ClosedSurfaceR4.JetPolynomial

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

def coordinateQuadraticPolynomial {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) (t : ℝ) : SmallModes.Base → Fin 3 → ℝ :=
  fun p k => ∑ l, ε ^ (l.val + 1) * ((1 / 2 : ℝ) * ((P k l).variations 1).eval
    ![G, X ∘ planeCoordinateIsometry, X ∘ planeCoordinateIsometry, 0] (planeCoordinateIsometry.symm p,t))

def coordinateQuadraticMean {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) :
    SmallModes.Base → Fin 3 → ℝ :=
  fun p k => ∑ i, quadraticMeanCoefficient (P k) ε G (φ i) (H i) τ t (planeCoordinateIsometry.symm p)

def coordinateQuadraticCoefficient {n : ℕ} {ι : Type*}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ)
    (l : RealModes.QuadraticLabel ι) : SmallModes.Tensor :=
  fun p k => quadraticFamilyCoefficient (P k) ε G φ H τ t l (planeCoordinateIsometry.symm p)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric and quantitative data for the already constructed finite
polynomial phase solver. The operator bound here is supplied by
`phaseChartPolynomialOperator_bounds`; it concerns the actual transported
polynomial derivative. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def norm (f : SupportedField (F := ComplexTensor) (modeSupport K)) (m : ℕ) : ℝ :=
  supportedWeightedSeminorm (chartSupport c.e (modeSupport K) c.supportChart) s m
    (tensorChartPush c.e c.smoothInverse (modeSupport K) c.supportChart f)

def κ (m : ℕ) : ℝ := max (SmallModes.errorConstant m (c.C m))
  (c.D m * SmallModes.initialConstant 4 (m + tensorOrder P) (c.C (m + tensorOrder P)))

def size (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ) * (2 ^ m * (SmallModes.forcedModeBudget 4 (tensorOrder P) c.C c.D q m *
    c.norm f (m + (q + 1) * (tensorOrder P + 1)))) * c.J m ^ m

def residual (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q m : ℕ) : ℝ :=
  tensorChartBudget m (c.J m) (c.J (m + 1)) *
    (2 ^ m * ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ
        (fun r => c.κ r * c.norm f (r + (tensorOrder P + 1))) q m))

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeSeed
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The free geometric amplitude in the original coordinates. The same
actual polynomial operator is conjugated into the phase chart, and the
resulting amplitude is transported back with controlled derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma RealModeDomain.of_complex {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : ModeDomain (fun p => complexify (F p)) U) :
    RealModeDomain F U := by
  refine ⟨h.isOpen, ?_, ?_⟩
  · intro p hp hz
    have hd := h.determinant p hp
    rw [coordDeriv_complexify (hF.differentiable (by simp) p),
      coordDeriv_complexify (hF.differentiable (by simp) p), complexify_gram, hz,
      Complex.ofReal_zero] at hd
    exact hd rfl
  · intro p hp hz
    have hg := h.good p hp
    rw [← complexify_realSecond hF, hz] at hg
    simp only [complexify, map_zero, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hg
    exact hg rfl

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

abbrev chartCompact : Compacts SmallModes.Base := chartSupport c.e (modeSupport K) c.supportChart

abbrev realMap : RealModes.RField 4 := (G ∘ planeCoordinateIsometry.symm) ∘ c.e.symm

theorem realDomain : RealModeDomain c.realMap c.e.target := RealModeDomain.of_complex c.smoothMap c.domain

def operator : SupportedField (F := SmallModes.Ambient 4) c.chartCompact →ₗ[ℝ]
    SupportedField (F := PhaseMean.ComplexTensor) c.chartCompact :=
  phaseChartPolynomialOperator c.openO c.openU P c.smoothP hG c.mapsG K c.supportU c.smoothPhase
    τ ε c.e c.smoothForward c.smoothInverse c.supportChart

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedZeroMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual zero phase of a transported free amplitude. The metric
part transforms as a covariant tensor through the phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes
open SmallModes (gradientAmplitude)
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def leadingInChart (b : SupportedField (F := ℝ) c.chartCompact) : SmallModes.Base → Tensor :=
  fun y k => b y ^ 2 * (firstDirection k).1 * (secondDirection k).1

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CombinedMeanGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact mean identity, support and global smoothness for the combined mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial

lemma seedMeanError_zero_outside {n : ℕ} (τ : ℝ) (K : Compacts Base)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w p : Base) (hp : p ∉ (K : Set Base)) :
    seedMeanError τ T V W v w p = 0 := by
  have hV : p ∉ tsupport V := fun hx => hp (V.tsupport_subset hx)
  have hTV : p ∉ tsupport (T V) := fun hx => hp ((T V).tsupport_subset hx)
  have hd : gradientAmplitude τ (T V) v p = 0 := by
    simp only [gradientAmplitude, coordDeriv, fderiv_of_notMem_tsupport ℝ hTV,
      zero_apply, image_eq_zero_of_notMem_tsupport hTV, smul_zero, add_zero]
  have hl : leadingDerivative τ V v p = 0 := by
    simp only [leadingDerivative, image_eq_zero_of_notMem_tsupport hV, smul_zero]
  simp only [seedMeanError, hd, hl, QuadraticMean.zeroPair, zero_dotProduct, Complex.zero_re,
    zero_div, sub_self]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedCombinedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The combined mean of the actual transported free amplitude, with the
polynomial evaluated in the original coordinates and the metric transformed
as a two-tensor. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def leadingFieldInChart (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) c.chartCompact :=
  ⟨c.leadingInChart b,
    contDiff_pi.mpr (fun k => ((b.contDiff.pow 2).mul contDiff_const).mul contDiff_const),
    fun x hx => by
      ext k
      change b x ^ 2 * _ * _ = 0
      have hb : b x = (0 : ℝ) := b.zero_on_compl hx
      simp only [hb, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]⟩

def leadingField (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Tensor) (modeSupport K) :=
  realTensorChartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.leadingFieldInChart b)

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedRootAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual cutoff square-root amplitudes as supported smooth fields. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates RootMean
open JetPolynomial (SupportedField supportedWeightedSeminorm )

lemma phaseAmplitude_tsupport (ψ u : Base → ℝ) :
    tsupport (phaseAmplitude ψ u) ⊆ tsupport ψ := by
  apply closure_mono
  intro p hp
  by_contra hn
  have hψ : ψ p = 0 := by simpa only [Function.mem_support, not_not] using hn
  exact hp (by simp only [phaseAmplitude, hψ, zero_mul])

def supportedRootAmplitude {U : Set Base} (hU : IsOpen U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (ψ : SupportedField (F := ℝ) K)
    (u : Base → ℝ) (hu : ContDiffOn ℝ ∞ u U) (hpos : ∀ p ∈ U, 0 < u p) :
    SupportedField (F := ℝ) K :=
  let hs := (phaseAmplitude_tsupport ψ u).trans ψ.tsupport_subset
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset hU (hs.trans hKU)
      (contDiffOn_phaseAmplitude ψ.contDiff.contDiffOn hu hpos))
    (subset_closure.trans hs)

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

def trialAmplitude (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) :
    SupportedField (F := ℝ) c.chartCompact := by
  classical
  exact if ha : ContDiffOn ℝ ∞ A c.e.source ∧ InTrialBall c.e.source reference r A then
    supportedRootAmplitude h.domain.isOpen c.chartCompact
      (chartSupport_subset c.e (modeSupport K) c.supportChart) ψ (coefficient Q c.e.symm A)
      (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto ha.1)
      (fun _ hp => hρ.trans_le (coefficient_trial_range h.invInto h.margin ha.2 hp).1)
    else 0

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and jet bounds for the actual mean map of one phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

structure ChartedMeanData {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)
    (r ρ R : ℝ) (reference : SmallModes.Base → Tensor) where
  cutoff : SupportedField (F := ℝ) c.chartCompact
  form : SmallModes.Base → Tensor →L[ℝ] ℝ
  localBounds : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap cutoff form c.e c.e.symm
  budgets : Budgets c.e.source c.e.target s c.realMap cutoff form c.e c.e.symm
  compactJets : Set LowJet
  compact : IsCompact compactJets
  subsetDomain : compactJets ⊆ c.O
  mapsJets : Set.MapsTo (lowJet G) c.U compactJets
  B : ℕ → ℝ
  F : ℕ → ℝ
  oneLEB : ∀ m, 1 ≤ B m
  nonnegF : ∀ m, 0 ≤ F m
  jetsBound : ∀ m, WeightedBound c.U s (m + tensorOrder P) (B m) (lowJet G)
  phaseBound : ∀ m v, WeightedBound c.U s (m + tensorOrder P) (F m)
    (fun x => fderiv ℝ φ x (coordinateVector v))

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

def amplitude (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) : SupportedField (F := ℝ) c.chartCompact :=
  c.trialAmplitude d.cutoff d.form d.localBounds hρ A

def leading (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  c.leadingField (d.amplitude hρ A)

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSupportedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas cutoffs as actual compactly supported fields, and their
transport to a phase chart with the required inverse-frequency factor. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseWeightCutoff (i : A.centers)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e.symm e.target)
    (hK : (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ e.source)
    (w : ℝ) : SupportedField (F := ℝ) (chartSupport e (modeSupport (A.chartWeightCompact i)) hK) :=
  w⁻¹ • chartPush e he (modeSupport (A.chartWeightCompact i)) hK (A.supportedPlaneWeight i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorPlaneRestore
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore coordinate-plane vector fields to a smooth global displacement,
with a fixed-atlas weighted estimate and no derivative loss. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def vectorPlaneRestore (f : A.centers → SmallModes.Base → V) : M → V :=
  ∑ i : A.centers, restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance metricTensorFiberNormed_r3832e2_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_r3832e2_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace
local instance metricTensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

local instance metricTensorDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_r3832e2_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_r3832e2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def linearMetricTensor (F U : M → Space) (p : M) : CovariantTwoTensor p :=
  metricPairTensor F U p + metricPairTensor U F p

lemma inducedTensor_symmetric (F : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    inducedTensor F p v w = inducedTensor F p w v := by
  change inner ℝ (surfaceDifferential F p v) (surfaceDifferential F p w) =
    inner ℝ (surfaceDifferential F p w) (surfaceDifferential F p v)
  exact real_inner_comm _ _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RestoredMetricTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring a compactly supported Euclidean displacement restores its
actual metric tensor, with no extra terms from the outer atlas cutoff. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance restoredMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredLinearizedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact globalization of the actual metric linearization. The local
base map is the constructed smooth representative of the global map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
local instance restoredLinearFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredLinearFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredLinearDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialDiagonalVariations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual parameter derivatives of a polynomial along a
map variation are its mixed variations with all directions equal. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ParameterTaylor SmoothPeriodicCalculus

namespace Expression

def affinePolynomial (e : Expression) (G H : Base → Space) (θ : ℝ) : Base × ℝ → ℝ :=
  fun z => (ofExpression e).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTaylorIdentity
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

def coordinateFullQuadratic {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  RealModes.realMetricTensor X + coordinateQuadraticPolynomial P ε G X 0

def coordinateTaylorRemainder {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  fun p k => ∑ l, ε ^ (l.val + 1) *
    (P k l).taylorRemainder G (X ∘ planeCoordinateIsometry) 0 (planeCoordinateIsometry.symm p)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_QuadraticInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the mixed and pure terms introduced by the second, forced
correction from the quadratic tensor of the first, free correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def coordinateQuadraticInteraction {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X Y : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  fun p k => RealModes.realLinearizedTensor X Y p k + RealModes.realMetricTensor Y p k +
    (∑ l, ε ^ (l.val + 1) * (1 / 2 : ℝ) *
      (((P k l).variations 1).eval ![G, X ∘ planeCoordinateIsometry, Y ∘ planeCoordinateIsometry, 0]
        (planeCoordinateIsometry.symm p,0) +
       ((P k l).variations 1).eval ![G, Y ∘ planeCoordinateIsometry, X ∘ planeCoordinateIsometry, 0]
        (planeCoordinateIsometry.symm p,0))) +
    coordinateQuadraticPolynomial P ε G Y 0 p k

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSolveFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the finite input norm and the small residual power from the
geometric solver constants. The input order is explicit. -/
noncomputable section
open scoped NNReal ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def sizeFactor (q m : ℕ) : ℝ :=
  (m.factorial : ℝ) * 2 ^ m * SmallModes.forcedModeBudget 4 (tensorOrder P) c.C c.D q m * c.J m ^ m

def residualFactor (q m : ℕ) : ℝ :=
  tensorChartBudget m (c.J m) (c.J (m + 1)) * 2 ^ m *
    FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ c.κ q m

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasJetCoordinateRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized atlas maps on a coordinate overlap.  The transition
scalar is the square of the outer cutoff.  A nonzero partition weight gives
the needed equality of germs without any extra plateau hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def transitionScalar (i j : A.centers) (x : Base) : ℝ :=
  (A.outer j ((chart (i : M)).symm x)) ^ 2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Project a global ambient field to the normal bundle using the fixed
finite atlas. No orientation or global tangent frame is chosen. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def localizedNormalField (i : A.centers) (n : M → Space) : RField 4 :=
  spaceCoordinates ∘ localize (i : M) (A.weight i) n ∘ planeCoordinateIsometry.symm

def localProjectedNormal (i : A.centers) (F n : M → Space) : RField 4 := fun x =>
  realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (A.localizedNormalField i n x)

def projectedNormalField (F n : M → Space) : M → Space :=
  A.vectorPlaneRestore (fun i => spaceCoordinates.symm ∘ A.localProjectedNormal i F n)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityNormalNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The old second derivative has a nonzero normal component after changing velocity. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def leadingTangent (X Y C V : Vec) : Vec := X - realNormalPart Y C X + V

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ActualSecondFormFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual orthonormal normal frame and the Gauss-constrained coordinates
of the second fundamental form of a smooth surface in four-space. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

structure SecondFormFrame (F : RField 4) (p : Base) (k : ℝ) where
  n : Vec
  m : Vec
  S : ℝ
  D : ℝ
  N : ℝ
  L : ℝ
  size_pos : 0 < S
  unit_n : n ⬝ᵥ n = 1
  unit_m : m ⬝ᵥ m = 1
  orthogonal : n ⬝ᵥ m = 0
  tangent_n : coordDeriv dx F p ⬝ᵥ n = 0 ∧ coordDeriv dy F p ⬝ᵥ n = 0
  tangent_m : coordDeriv dx F p ⬝ᵥ m = 0 ∧ coordDeriv dy F p ⬝ᵥ m = 0
  xx : realSecondForm F dx dx p = ((k+D^2+N^2)/S) • n+L • m
  xy : realSecondForm F dx dy p = D • n+N • m
  yy : realSecondForm F dy dy p = S • n

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactNormalTriple
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

def tripleNormal (J : NormalTriple) : Vec := realNormalPart (J 0) (J 1) (J 2)

end ClosedSurfaceR4.VelocityFrame

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

def profilePreferred (J : BoundaryProfile) : Vec :=
  VelocityFrame.normalize (profileNormalPart J)

def profileComplement (J : BoundaryProfile) : Vec :=
  unitPerp (J 0) (J 1) (profilePreferred J)

def regularBoundaryProfiles : Set BoundaryProfile :=
  {J | gramDet (J 0) (J 1) ≠ 0 ∧ profileNormalPart J ≠ 0}

/-- The coordinates are `S`, `D`, `N`, and `z L`. The xx entry in the input
has already been multiplied by the fast scale. -/
def profileCoefficients (J : BoundaryProfile) : Fin 4 → ℝ :=
  ![Real.sqrt (profileNormalPart J ⬝ᵥ profileNormalPart J),
    J 3 ⬝ᵥ profilePreferred J, J 3 ⬝ᵥ profileComplement J,
    J 4 ⬝ᵥ profileComplement J]

def profileGeometry (J : BoundaryProfile) : (Vec × Vec) × (Fin 4 → ℝ) :=
  ((profilePreferred J,profileComplement J),profileCoefficients J)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas projection is a convex sum of the actual pointwise normal
projections. Local exterior estimates therefore pass to the global field. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def chartProjectedNormal (i : A.centers) (F n : M → Space) (p : M) : Space :=
  spaceCoordinates.symm (realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) (spaceCoordinates (n p)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual charted free amplitudes and their zero-phase tensors. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

def chartedFamilyLeading (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) :
    SmallModes.Base → Tensor := fun x => ∑ i, (d i).leading hρ A x

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real displacement of the actual charted free amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

def freeSizeFactor (q m : ℕ) (N : ℝ) : ℝ :=
  (m.factorial : ℝ) * 2 ^ m * correctedSeedBudget (tensorOrder P) c.C c.D q m N * c.J m ^ m

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedFreeResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual free displacement solves the full metric/polynomial
linearization to arbitrary finite order, in the original coordinates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

def freeInitialFactor (m : ℕ) : ℝ := max (SmallModes.fullErrorConstant 4 m (c.C m))
  (c.D m * SmallModes.initialConstant 4 (m + tensorOrder P) (c.C (m + tensorOrder P)))

def freeChartResidualFactor (q m : ℕ) (N : ℝ) : ℝ :=
  FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ c.freeInitialFactor q m *
    (Real.sqrt 2 * 2 ^ (inputOrder (P := P) q m) * N)

def freeResidualFactor (q m : ℕ) (N : ℝ) : ℝ :=
  tensorChartBudget m (c.J m) (c.J (m + 1)) * 2 ^ m * c.freeChartResidualFactor q m N

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical and compact geometric data kept fixed while scales and maps
vary in the small-increment construction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

structure ChartedMeanProfile {n : ℕ} (P : Fin 3 → Fin n → Expression) where
  U : Set Base
  O : Set LowJet
  Q : Set LowJet
  V : Set SmallModes.Base
  openU : IsOpen U
  openO : IsOpen O
  openV : IsOpen V
  compact : IsCompact Q
  subsetDomain : Q ⊆ O
  smoothP : ∀ k l, (P k l).SmoothCoeffs O
  C : ℕ → ℝ
  D : ℕ → ℝ
  J : ℕ → ℝ
  inv : ℕ → ℝ
  forms : ℕ → ℝ
  psi : ℕ → ℝ
  normal : ℕ → ℝ
  B : ℕ → ℝ
  F : ℕ → ℝ
  nonnegC : ∀ m, 0 ≤ C m
  oneLEJ : ∀ m, 1 ≤ J m
  oneLEInv : ∀ m, 1 ≤ inv m
  oneLEForms : ∀ m, 1 ≤ forms m
  oneLEPsi : ∀ m, 1 ≤ psi m
  oneLENormal : ∀ m, 1 ≤ normal m
  oneLEB : ∀ m, 1 ≤ B m
  nonnegF : ∀ m, 0 ≤ F m

namespace ChartedMeanProfile
variable {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ε τ : ℝ} {s : ℝ≥0}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ} {K : Compacts Base}
    {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

structure Fits (d : ChartedMeanData c r ρ R reference) : Prop where
  domain : c.U = p.U
  coefficients : c.C = p.C
  perturbation : c.D = p.D
  coordinates : c.J = p.J
  target : c.e.target = p.V
  inverse : d.budgets.inv = p.inv
  forms : d.budgets.forms = p.forms
  cutoff : d.budgets.psi = p.psi
  normal : d.budgets.normal = p.normal
  jets : d.B = p.B
  phase : d.F = p.F
  range : d.compactJets = p.Q

end ChartedMeanProfile
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamilyData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite charted phase family with its actual solvers and amplitudes,
packaged for assembling different coordinate patches on one surface. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

structure ChartedMeanFamilyData {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε τ : ℝ) (s : ℝ≥0) (r ρ R : ℝ) (reference : SmallModes.Base → Tensor) where
  G : Base → Space
  smoothG : ContDiff ℝ ∞ G
  phase : Fin 3 → Base → ℝ
  support : Fin 3 → Compacts Base
  solver : ∀ j, PolynomialSolveData P ε G smoothG (phase j) (support j) τ s
  data : ∀ j, ChartedMeanData (solver j) r ρ R reference

namespace ChartedMeanFamilyData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ} {s : ℝ≥0}
  {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def Fits (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (p : Fin 3 → ChartedMeanProfile P) : Prop := ∀ j, (p j).Fits (d.data j)

end ChartedMeanFamilyData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalFreeModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free correction is an actual sum of globally smooth phase modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

/-- The outer cutoff makes the original local phase a globally smooth scalar. -/
def freeGlobalPhase
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (i : A.centers) (j : Fin 3) : M → ℝ :=
  restore (i : M) (A.outer i) ((d i).phase j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredQuadratureMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual zero Fourier coefficient through supported atlas restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

local instance restoredMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QuadraticPhaseCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All quadratic phases generated by a fixed finite stock remain in one
fixed finite stock, independently of the number of repeated grid labels. -/
noncomputable section
open scoped BigOperators ContDiff
namespace ClosedSurfaceR4.RealModes

def quadraticPhaseCatalog (Γ : Finset (SmallModes.Base → ℝ)) :
    Finset (SmallModes.Base → ℝ) := by
  classical
  exact Γ.image (fun f x => 2*f x) ∪
    (Γ.product Γ).image (fun p x => p.1 x-p.2 x) ∪
    (Γ.product Γ).image (fun p x => p.1 x+p.2 x)

end ClosedSurfaceR4.RealModes

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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberSpace
local instance finiteAtlasFreeDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberNormed
local instance finiteAtlasFreeSectionNormed_r3832e2_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace_r3832e2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance finiteAtlasIndexDecidable : DecidableEq (Σ i, ι i) := Classical.decEq _

def finiteGlobalPhase (i : A.centers) (j : ι i) : M → ℝ :=
  restore (i : M) (A.outer i) (φ i j)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite catalogs for the actual restored global grid phases and
their readings in every atlas chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def linearPhaseCatalog (V : Finset SmallModes.Base) : Finset (M → ℝ) := by
  classical
  exact Finset.univ.biUnion fun i : A.centers => V.image fun v =>
    restore (i : M) (A.outer i) (phaseLinear v ∘ planeCoordinateIsometry)

def localQuadraticPhaseCatalog (V : Finset SmallModes.Base) (k : A.centers) :
    Finset (SmallModes.Base → ℝ) := by
  classical
  exact RealModes.quadraticPhaseCatalog ((A.linearPhaseCatalog V).image (A.vectorPlaneRead k))

end SmoothingAtlas
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

local instance transitionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

/-- The chain rule differentiates smooth low-jet coefficients and introduces
one additional actual jet factor. -/
def slow (v : Fin 2) : Expression → Expression
  | .coeff c => sumList Finset.univ.toList (fun i : LowIndex =>
      (lowFactor v i).mul (.coeff (slowDerivative c (lowBasis i))))
  | .atom w a e => .add (.atom (v :: w) a e) (.atom w a (slow v e))
  | .add e f => .add (slow v e) (slow v f)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetPullbackExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate derivatives in a second chart, expressed by finite jet
polynomials in the first chart. Only the surface and four-space dimensions
used in the primitive construction are considered. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial

def jetPullback (T S : Base → Base) : List (Fin 2) → Fin 4 → Expression
  | [],a => .coeff (fun z => z.1 (.inr (0,a)))
  | i::w,a => Expression.sumList Finset.univ.toList (fun k : Fin 2 =>
      (Expression.coeff (inverseCoordinateCoefficient T S i k)).mul ((jetPullback T S w a).slow k))


namespace Expression

/-- Pull back a finite expression through a fixed coordinate change. The
low-jet substitution is supplied by the finite-dimensional chain rule. -/
def coordinatePullback (T S : Base → Base) (K : LowJet → LowJet) : Expression → Expression
  | .coeff c => .coeff (fun z => c (K z.1,z.2))
  | .atom w a e => (jetPullback T S w a).mul (coordinatePullback T S K e)
  | .add e f => .add (coordinatePullback T S K e) (coordinatePullback T S K f)

end Expression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate pullback of a finite jet polynomial, with the low-jet
substitution and inverse differential proved from the actual local inverse.
No compatibility of the polynomial values is assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

/-- Transport through a smooth local inverse, including the coefficient
dependence on all positional order-two jets. -/
def localCoordinatePullback (e : Expression) (T S : Base → Base) : Expression :=
  e.coordinatePullback T S (coordinateLowJetSubstitution T S)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialFullCorrector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial construction for every component of the complete periodic
corrector. Only the transverse derivative increases the highest jet order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Expression

def spanTerm (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression) : Expression :=
  Expression.add ((Expression.coeff (spanCoefficient Y C L (1, 0))).mul H)
    ((Expression.coeff (spanCoefficient Y C L (0, 1))).mul K)

def angularSource (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K e : Expression) : Expression :=
  e.sub (Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
    ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K.angle)).fluct

def fullComponent (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (q : LowJet → ℝ) (L : E →L[ℝ] ℝ) (v : Fin 2) (h j e : Expression) : Expression :=
  let H := h.primitive
  let K := (H.slow v).sub j
  Expression.add (spanTerm Y C L H K) ((angularSource Y C X₀ V h K e).covariance V q L).primitive

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion SmoothPeriodicCalculus

abbrev VectorExpression := Fin 4 → Expression

namespace VectorExpression

def SmoothCoeffs (O : Set LowJet) (R : VectorExpression) : Prop :=
  ∀ i, (R i).SmoothCoeffs O

def add (R T : VectorExpression) : VectorExpression := fun i => .add (R i) (T i)
def slow (R : VectorExpression) (v : Fin 2) : VectorExpression := fun i => (R i).slow v
def angle (R : VectorExpression) : VectorExpression := fun i => (R i).angle
def mean (R : VectorExpression) : VectorExpression := fun i => (R i).mean
def primitive (R : VectorExpression) : VectorExpression := fun i => (R i).primitive

def dot (R T : VectorExpression) : Expression :=
  Expression.sumList Finset.univ.toList (fun i : Fin 4 => (R i).mul (T i))

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

def sumFinset {ι : Type*} (s : Finset ι) (f : ι → Expression) : Expression :=
  sumList s.toList f

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTensorPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pullback of finite tensor expressions under fixed coordinate changes.
The Jacobian factors, coefficient substitution, and higher jet atoms are
all constructed, so the evaluation identity assumes no tensor covariance. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Matrix Topology

namespace ClosedSurfaceR4.JetPolynomial

abbrev TensorExpression := Fin 3 → Expression

/-- The derivative of the coordinate map in the real pair coordinates
used by the three-component tensor representation. -/
def tensorCoordinateDerivative (T : Base → Base) (x : Base) :
    SmallModes.Base →L[ℝ] SmallModes.Base :=
  planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((fderiv ℝ T x).comp
      planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Covariant pullback of a symmetric tensor by the actual derivative. -/
def tensorCoordinatePullbackValue (T : Base → Base) (x : Base) :
    PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
  PhaseMean.pullback (tensorCoordinateDerivative T x)

/-- The three Jacobian coefficients of one pulled-back tensor component. -/
def tensorCoordinateJacobian (T : Base → Base) (k l : Fin 3) (x : Base) : ℝ :=
  let u := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.firstDirection k))
  let v := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.secondDirection k))
  ![u 0 * v 0,u 0 * v 1 + u 1 * v 0,u 1 * v 1] l

/-- Store a Jacobian factor as an actual smooth positional coefficient. -/
def tensorJacobianCoefficient (T : Base → Base) (k l : Fin 3) : LowJet × ℝ → ℝ :=
  fun z => tensorCoordinateJacobian T k l (lowPosition z.1)

namespace TensorExpression

/-- Evaluation in the original coordinate chart. -/
def eval (E : TensorExpression) (G : Base → Space) (z : Base × ℝ) : PhaseMean.Tensor :=
  fun k => (E k).eval G z

/-- Pull back both the scalar jet expressions and their tensor basis. -/
def coordinatePullback (E : TensorExpression) (T S : Base → Base) : TensorExpression :=
  fun k => Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorJacobianCoefficient T k l)).mul ((E l).localCoordinatePullback T S))

end TensorExpression

namespace Perturbation

/-- Apply the tensor coordinate transformation coefficient by coefficient
to a finite polynomial in the perturbation parameter. -/
def tensorPolynomialCoordinatePullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (T S : Base → Base) : Fin 3 → Fin n → Expression :=
  fun k r => TensorExpression.coordinatePullback (fun l => P l r) T S k

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarJetTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite jet-polynomial transport under multiplication by a fixed
smooth scalar function. This accounts for the atlas outer cutoffs before
coordinate transport. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

/-- Every ordered derivative of the scalar product is a finite expression.
Repeated formal slow differentiation supplies the exact Leibniz expansion. -/
def scalarProductAtom (a : Base → ℝ) : List (Fin 2) → Fin 4 → Expression
  | [],k => .atom [] k (.coeff (fun z => a (lowPosition z.1)))
  | v::w,k => (scalarProductAtom a w k).slow v

namespace Expression

/-- Substitute the complete finite jet polynomial of the fixed scalar
product, including positional low-jet coefficients. -/
def scalarProductPullback (a : Base → ℝ) : Expression → Expression
  | .coeff c => .coeff (fun z => c (scalarLowJetSubstitution a z.1,z.2))
  | .atom w k e => (scalarProductAtom a w k).mul (scalarProductPullback a e)
  | .add e f => .add (scalarProductPullback a e) (scalarProductPullback a f)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LocalizedCoordinatePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pullback of a polynomial through a local coordinate change and the
actual scalar localization of its input map. -/
noncomputable section
open Set
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.JetPolynomial
namespace Expression

def localizedCoordinatePullback (e : Expression) (T S : Base → Base)
    (a : Base → ℝ) : Expression :=
  (e.localCoordinatePullback T S).scalarProductPullback a

end Expression
namespace Perturbation

def localizedPolynomialPullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (T S : Base → Base) (a : Base → ℝ) : Fin 3 → Fin n → Expression :=
  fun k r => (P k r).localizedCoordinatePullback T S a

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorExpressionLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth changes of tensor trivialization act on finite jet
polynomials by finite linear combinations with positional coefficients. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial

namespace TensorExpression

def mapLinear (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (E : TensorExpression) : TensorExpression := fun k =>
  Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorLinearCoefficient L k l)).mul (E l))

end TensorExpression

namespace Perturbation

def mapTensorPolynomial {n : ℕ} (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (P : Fin 3 → Fin n → Expression) : Fin 3 → Fin n → Expression :=
  fun k r => TensorExpression.mapLinear L (fun l => P l r) k

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialRestoredRead
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
local instance restoredReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasRestoredPolynomialRepresentation
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
local instance restoredPolyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredPolyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredPolyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial families can be padded to a common degree and added
without changing their values or their smooth-coefficient property. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

namespace Perturbation

/-- Higher unused powers have the actual zero expression as coefficient. -/
def padTensorPolynomial {n N : ℕ} (P : Fin 3 → Fin n → Expression) :
    Fin 3 → Fin N → Expression :=
  fun k r => if h : r.val < n then P k ⟨r.val,h⟩ else .coeff (fun _ => 0)

/-- Add the coefficient expressions after padding every member to the
same degree. No map or perturbation parameter enters this construction. -/
def sumTensorPolynomials {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (P : (i : ι) → Fin 3 → Fin (n i) → Expression) :
    Fin 3 → Fin (polynomialFamilyDegree n) → Expression :=
  fun k r => Expression.sumFinset Finset.univ (fun i => padTensorPolynomial (P i) k r)

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit restricted linear chart used for a nonzero phase covector. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma linearPhaseChart_smooth (ξ : Base) (hξ : ξ ≠ 0) (U : Set Base) (hU : IsOpen U) :
    ContDiff ℝ ∞ (linearPhaseChart ξ hξ U hU) ∧
      ContDiff ℝ ∞ (linearPhaseChart ξ hξ U hU).symm :=
  ⟨(phaseEquiv ξ hξ).contDiff,(phaseEquiv ξ hξ).symm.contDiff⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseNeighborhood
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly contained local domains for actual noncritical good phases. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma continuous_phaseDerivative {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (phaseDerivative φ) := by
  exact ((hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).continuous.prodMk
    ((hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).continuous

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodPhaseCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite good phase charts covering the compact support of a correction. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

/-- All geometric data of one compactly bounded local phase chart. -/
structure GoodPhaseChart (F : RField 4) (φ : Base → ℝ) where
  chart : OpenPartialHomeomorph Base Base
  phase : ∀ x, (chart x).1 = φ x
  smooth : ContDiff ℝ ∞ chart
  smoothInverse : ContDiff ℝ ∞ chart.symm
  sourceCompact : Compacts Base
  targetCompact : Compacts Base
  domain : Set Base
  sourceBound : chart.source ⊆ sourceCompact
  targetBound : chart.target ⊆ targetCompact
  targetInside : (targetCompact : Set Base) ⊆ domain
  good : RealModeDomain (F ∘ chart.symm) domain

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactRealJetNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed compact admissible jet neighborhoods for nearby immersed maps. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates

def admissibleRealJets : Set RealTwoJet :=
  {J | NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ realNormalPart (J 0) (J 1) (J 4) ≠ 0}

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformGeometricMeanData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single geometric mean datum at unit slow scale supplies one fixed
profile and actual mean data at all admissible smaller scales. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open RealModes

theorem LocalBounds.atRadius {U V : Set SmallModes.Base} {s r r' ρ R : ℝ}
    {reference : SmallModes.Base → Tensor} {F : RField 4} {ψ : SmallModes.Base → ℝ}
    {Q : SmallModes.Base → Tensor →L[ℝ] ℝ} {χ e : SmallModes.Base → SmallModes.Base}
    (h : LocalBounds U V s r ρ R reference F ψ Q χ e) (hr : r' ≤ r) :
    LocalBounds U V s r' ρ R reference F ψ Q χ e := by
  refine { h with margin := ?_ }
  intro x hx
  have hm := h.margin x hx
  have hn : ‖Q x‖*r' ≤ ‖Q x‖*r := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
  constructor <;> linarith

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LinearPhaseMeanGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mean geometry for an actual linear good phase: the coefficient
margin is transported exactly, and the pullback operator is constant. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean

lemma pullbackField_linearPhaseChart {ξ : Base} (hξ : ξ ≠ 0) {U : Set Base} (hU : IsOpen U)
    (x : Base) : pullbackField (linearPhaseChart ξ hξ U hU) x =
      pullback (phaseEquiv ξ hξ).toContinuousLinearMap := by
  change pullback (fderiv ℝ (phaseEquiv ξ hξ) x) = _
  rw [ContinuousLinearEquiv.fderiv]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformLinearPhaseBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed numerical mean budgets for nearby immersions in a linear phase chart.
The chart, cut-off, coefficient form, and weighted two-jet profile are fixed
before the nearby immersion and slow scale are supplied. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes

def Budgets.profiles {U V : Set Base} {s : ℝ} {F : RField 4}
    {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}
    (d : Budgets U V s F ψ Q χ e) : BudgetProfiles where
  inv := d.inv
  chi := d.chi
  psi := d.psi
  forms := d.forms
  pull := d.pull
  normal := d.normal
  mode := d.mode
  inv_pos := d.inv_pos
  chi_pos := d.chi_pos
  psi_pos := d.psi_pos
  forms_pos := d.forms_pos
  pull_pos := d.pull_pos
  normal_pos := d.normal_pos
  mode_pos := d.mode_pos

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnperturbedGeometricSolver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unperturbed solvers require only compact good-mode geometry. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes

/-- The exact-correction stage has no polynomial perturbation. -/
def emptyMetricPolynomial : Fin 3 → Fin 0 → Expression := fun _ => Fin.elim0

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformLinearChartedMeanData
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual charted mean data with one profile for a nearby family. The
positional jet is read on a fixed bounded original-coordinate domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

@[simp] lemma tensorOrder_emptyMetricPolynomial : tensorOrder emptyMetricPolynomial = 0 := by
  simp [tensorOrder,order,emptyMetricPolynomial]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformLinearChartedMeanFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniformly profiled three-phase mean family for nearby immersions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

def ChartedMeanData.atRadius {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {S : Compacts Base}
    {c : PolynomialSolveData P ε G hG φ S τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference) (r' : ℝ) (hr : r' ≤ r) :
    ChartedMeanData c r' ρ R reference where
  cutoff := d.cutoff
  form := d.form
  localBounds := d.localBounds.atRadius hr
  budgets := d.budgets
  compactJets := d.compactJets
  compact := d.compact
  subsetDomain := d.subsetDomain
  mapsJets := d.mapsJets
  B := d.B
  F := d.F
  oneLEB := d.oneLEB
  nonnegF := d.nonnegF
  jetsBound := d.jetsBound
  phaseBound := d.phaseBound

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseSupportCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer compact phase supports between the two plane coordinate conventions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def onModeSupportLM (K : Compacts SmallModes.Base) :
    SupportedField (F := E) K →ₗ[ℝ] SupportedField (F := E) (modeSupport (jetSupport K)) where
  toFun := onModeSupport K
  map_add' _ _ := by apply DFunLike.ext; intro x; rfl
  map_smul' _ _ := by apply DFunLike.ext; intro x; rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Split an actual smooth compactly supported target using the finite smooth
phase partition.  Every piece is a supported smooth field on a compact subset
of its phase domain, and the sum of the pieces is the original target.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.PhasePartitions

open SmallModes (Base)
open JetPolynomial (SupportedField)
open PhaseMean (ComplexTensor)

namespace CompactPhasePartition

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- With the partition fixed, splitting is linear in the target. -/
def splitSupportedLM (P : CompactPhasePartition ι (K : Set Base) U) (i : ι) :
    SupportedField (F := F) K →ₗ[ℝ] SupportedField (F := F) (P.pieceSupport i) where
  toFun := fun A => P.splitSupported A i
  map_add' A B := by
    apply DFunLike.ext
    intro x
    change P.weight i x • (A x + B x) = P.weight i x • A x + P.weight i x • B x
    exact smul_add _ _ _
  map_smul' c A := by
    apply DFunLike.ext
    intro x
    change P.weight i x • (c • A x) = c • (P.weight i x • A x)
    exact smul_comm _ _ _

end CompactPhasePartition

end ClosedSurfaceR4.PhasePartitions

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SplitSupportedBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite-order bounds for the actual partition split.  A fixed partition has
bounded derivatives of every fixed order.  Consequently the split costs a
constant depending only on that partition and the order, uniformly over all
short scales at most one and linearly in the target seminorm.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

open SmallModes (Base)
open JetPolynomial (SupportedField supportedWeightedSeminorm
  )
open WeightedEstimates

variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

/-- Unit-scale derivatives of the fixed partition coefficient. -/
def weightSize (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) (i : ι) : ℝ :=
  supportedWeightedSeminorm (P.supportCompact i) 1 m (P.supportedWeight i)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A single constant works for every member of the finite partition. -/
def splitConstant (P : CompactPhasePartition ι (K : Set Base) U) (m : ℕ) : ℝ :=
  1 + ∑ i, 2 ^ m * P.weightSize m i

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the geometric charts when constructing the compact target split. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

structure CompactPhaseFamily (F : JetPolynomial.Base → JetPolynomial.Space)
    (φ : JetPolynomial.Base → ℝ) (K : Compacts SmallModes.Base) where
  centers : Finset K
  charts : centers → GoodPhaseChart (F ∘ planeCoordinateIsometry.symm) (coordinatePhase φ)
  partition : PhasePartitions.CompactPhasePartition centers K (fun i => (charts i).chart.source)

namespace CompactPhaseFamily
variable {F : JetPolynomial.Base → JetPolynomial.Space} {φ : JetPolynomial.Base → ℝ}
  {K : Compacts SmallModes.Base} (a : CompactPhaseFamily F φ K)

def support (i : a.centers) : Compacts JetPolynomial.Base :=
  jetSupport (a.partition.pieceSupport i)

def split (i : a.centers) : SupportedField (F := ComplexTensor) K →ₗ[ℝ]
    SupportedField (F := ComplexTensor) (modeSupport (a.support i)) :=
  (onModeSupportLM (a.partition.pieceSupport i)).comp (a.partition.splitSupportedLM i)

end CompactPhaseFamily
end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStepBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global weighted estimate for the concrete unsmoothed normalized-defect update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance stepBoundFiberNormed_r3832e2_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance stepBoundFiberSpace_r3832e2_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance stepBoundDualAdd_r3832e2_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance stepBoundDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance stepBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smoothStepFiberNormed
local instance smoothStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSelfTensorRead
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
open JetPolynomial
local instance selfReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance selfReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance selfReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorLocalBounds
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

local instance tensorLocalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorLocalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ParabolicPhaseChart
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit phase chart on an entire half-plane. This supplies one
chart on a disk uniformly over nearby linear phase parameters. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def parabolicPhaseMap (k : ℝ) (p : Base) : Base :=
  (p.1+(k/2)*(p.1^2+p.2^2),p.2)

def parabolicDiscriminant (k : ℝ) (p : Base) : ℝ :=
  1+2*k*p.1-k^2*p.2^2

def parabolicPhaseInverse (k : ℝ) (p : Base) : Base :=
  ((Real.sqrt (parabolicDiscriminant k p)-1)/k,p.2)

lemma parabolicDiscriminant_map (k : ℝ) (p : Base) :
    parabolicDiscriminant k (parabolicPhaseMap k p) = (1+k*p.1)^2 := by
  simp only [parabolicDiscriminant,parabolicPhaseMap]
  ring

lemma parabolicPhaseMap_smooth (k : ℝ) : ContDiff ℝ ∞ (parabolicPhaseMap k) := by
  unfold parabolicPhaseMap
  fun_prop

lemma parabolicDiscriminant_smooth (k : ℝ) : ContDiff ℝ ∞ (parabolicDiscriminant k) := by
  unfold parabolicDiscriminant
  fun_prop

lemma parabolicPhaseInverse_source {k : ℝ} (hk : k ≠ 0) {p : Base}
    (hp : 0 < parabolicDiscriminant k p) :
    0 < 1+k*(parabolicPhaseInverse k p).1 := by
  have he : 1+k*(parabolicPhaseInverse k p).1 = Real.sqrt (parabolicDiscriminant k p) := by
    dsimp [parabolicPhaseInverse]
    field_simp
    ring
  rw [he]
  exact Real.sqrt_pos.mpr hp

lemma parabolicPhaseInverse_left {k : ℝ} (hk : k ≠ 0) {p : Base}
    (hp : 0 < 1+k*p.1) : parabolicPhaseInverse k (parabolicPhaseMap k p) = p := by
  ext
  · simp only [parabolicPhaseInverse,parabolicDiscriminant_map,Real.sqrt_sq hp.le]
    field_simp
    ring
  · rfl

lemma parabolicPhaseInverse_right {k : ℝ} (hk : k ≠ 0) {p : Base}
    (hp : 0 < parabolicDiscriminant k p) :
    parabolicPhaseMap k (parabolicPhaseInverse k p) = p := by
  have hs := Real.sq_sqrt hp.le
  ext
  · dsimp [parabolicPhaseMap,parabolicPhaseInverse]
    field_simp
    dsimp [parabolicDiscriminant] at hs ⊢
    nlinarith
  · rfl

lemma parabolicPhaseInverse_smooth (k : ℝ) :
    ContDiffOn ℝ ∞ (parabolicPhaseInverse k) {p | 0 < parabolicDiscriminant k p} := by
  apply ContDiffOn.prodMk _ contDiffOn_snd
  exact (((parabolicDiscriminant_smooth k).contDiffOn.sqrt (fun _ hp => ne_of_gt hp)).sub
    contDiffOn_const).div_const k

def parabolicPhaseChart (k : ℝ) (hk : k ≠ 0) : OpenPartialHomeomorph Base Base where
  toFun := parabolicPhaseMap k
  invFun := parabolicPhaseInverse k
  source := {p | 0 < 1+k*p.1}
  target := {p | 0 < parabolicDiscriminant k p}
  map_source' := fun p hp => by
    change 0 < parabolicDiscriminant k (parabolicPhaseMap k p)
    rw [parabolicDiscriminant_map]
    exact sq_pos_of_pos hp
  map_target' := fun _ hp => parabolicPhaseInverse_source hk hp
  left_inv' := fun _ hp => parabolicPhaseInverse_left hk hp
  right_inv' := fun _ hp => parabolicPhaseInverse_right hk hp
  open_source := isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_fst))
  open_target := isOpen_lt continuous_const (parabolicDiscriminant_smooth k).continuous
  continuousOn_toFun := (parabolicPhaseMap_smooth k).continuous.continuousOn
  continuousOn_invFun := (parabolicPhaseInverse_smooth k).continuousOn

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredParabolicChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit nonlinear phase chart on a whole centered neighborhood. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def phaseCovectorSquare (ell : Base) : ℝ := ell.1^2+ell.2^2

lemma phaseCovectorSquare_pos {ell : Base} (hell : ell ≠ 0) : 0 < phaseCovectorSquare ell :=
  covector_length_sq_pos hell

def centeredPhaseCoordinates (ell : Base) (hell : ell ≠ 0) (c : Base) : Base ≃ₜ Base :=
  (Homeomorph.addRight (-c)).trans (phaseEquiv ell hell).toHomeomorph

def centeredParabolicChart (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0) (c : Base) :
    OpenPartialHomeomorph Base Base :=
  (centeredPhaseCoordinates ell hell c).transOpenPartialHomeomorph
    (parabolicPhaseChart (L/phaseCovectorSquare ell)
      (div_ne_zero hL (phaseCovectorSquare_pos hell).ne'))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasJetRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized jets can be transported between independently chosen atlases. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

def cross_transitionScalar (i : A.centers) (j : B.centers) (x : Base) : ℝ :=
  (B.outer j ((chart (i : M)).symm x)) ^ 2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorTransition
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

local instance crossTransitionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossTransitionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance crossTransitionDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance crossTransitionDualSmul_r3832e2_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

local instance crossTransitionSectionNormed_r3832e2_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace_r3832e2_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
def cross_pairSupport (i : A.centers) (j : B.centers) : Set Base :=
  (chart (i : M)) '' (tsupport (A.weight i) ∩ tsupport (B.outer j))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_EuclideanChartRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth Euclidean representatives agree with the actual chart map near
points where a partition weight is nonzero. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def euclideanChartRead (i : A.centers) (F : M → Space) : Plane → Space :=
  A.vectorChartRead i F ∘ EuclideanSpace.equiv (Fin 2) ℝ

end SmoothingAtlas
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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementDualSmul
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementSectionNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteIncrementFiberNormed
local instance finiteIncrementSectionSpace_r3832e2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance finiteIncrementIndexDecidable : DecidableEq (Σ i, ι i) := Classical.decEq _

end SmoothingAtlas

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearPhaseDerivativeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher derivatives of the selected linear phase charts need no
compactness constants. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseEquiv_norm_le (ξ : Base) (hξ : ξ ≠ 0) :
    ‖(phaseEquiv ξ hξ).toContinuousLinearMap‖ ≤ 2*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖phaseEquiv ξ hξ v‖ ≤ 2*‖ξ‖*‖v‖
  rw [phaseEquiv_apply, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
  have hξ1 : |ξ.1| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le ξ
  have hξ2 : |ξ.2| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le ξ
  have hv1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have hv2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  constructor
  · calc
      _ ≤ |ξ.1*v.1|+|ξ.2*v.2| := abs_add_le _ _
      _ ≤ ‖ξ‖*‖v‖+‖ξ‖*‖v‖ := by rw [abs_mul, abs_mul]; gcongr
      _ = _ := by ring
  · calc
      _ ≤ |(-ξ.2)*v.1|+|ξ.1*v.2| := abs_add_le _ _
      _ ≤ ‖ξ‖*‖v‖+‖ξ‖*‖v‖ := by rw [abs_mul, abs_neg, abs_mul]; gcongr
      _ = _ := by ring

lemma positive_order_linear_derivative_le (L : Base →L[ℝ] Base)
    {U : Set Base} (hU : IsOpen U) {j : ℕ} (hj : 1 ≤ j) {x : Base} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ j L U x‖ ≤ ‖L‖ := by
  rw [iteratedFDerivWithin_of_isOpen j hU hx]
  cases j with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ => L := funext fun _ => L.fderiv
    rw [he]
    cases j with
    | zero => rw [norm_iteratedFDeriv_zero]
    | succ j =>
      rw [iteratedFDeriv_succ_const]
      simpa only [Pi.zero_apply, norm_zero] using norm_nonneg L

lemma linearPhaseChart_derivative_bound {ξ : Base} (hξ : ξ ≠ 0)
    {U : Set Base} (hU : IsOpen U) {j : ℕ} (hj : 1 ≤ j) {x : Base} (hx : x ∈ U) :
    ‖iteratedFDerivWithin ℝ j (linearPhaseChart ξ hξ U hU) U x‖ ≤ 2*‖ξ‖ :=
  (positive_order_linear_derivative_le (phaseEquiv ξ hξ).toContinuousLinearMap hU hj hx).trans
    (phaseEquiv_norm_le ξ hξ)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NoncriticalPhaseCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact phase-chart geometry chosen independently of the immersion. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

structure NoncriticalPhaseChart (φ : Base → ℝ) where
  chart : OpenPartialHomeomorph Base Base
  phase : ∀ x, (chart x).1 = φ x
  smooth : ContDiff ℝ ∞ chart
  smoothInverse : ContDiff ℝ ∞ chart.symm
  sourceCompact : Compacts Base
  targetCompact : Compacts Base
  sourceBound : chart.source ⊆ sourceCompact
  targetBound : chart.target ⊆ targetCompact

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RestrictedPhasePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict a fixed partition to any smaller target support, preserving
its numerical derivative constants exactly. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PhasePartitions.CompactPhasePartition
open SmallModes
variable {ι : Type*} [Fintype ι] {K : Compacts Base} {U : ι → Set Base}

def restrictTarget (P : CompactPhasePartition ι (K : Set Base) U)
    (L : Compacts Base) (hL : (L : Set Base) ⊆ K) :
    CompactPhasePartition ι (L : Set Base) U where
  weight := P.weight
  smooth := P.smooth
  nonneg := P.nonneg
  le_one := P.le_one
  compact_support := P.compact_support
  subordinate := P.subordinate
  sum_eq_one := fun x hx => P.sum_eq_one x (hL hx)

end ClosedSurfaceR4.PhasePartitions.CompactPhasePartition

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMarginCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A relative normal-length margin places every relevant point in a fixed
compact noncritical region, before the immersion or its fast scale is selected. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def phaseMarginCompact {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) (ε : ℝ) : Compacts Base :=
  ⟨(K : Set Base) ∩ {x | ε ≤ 4*‖phaseDerivative φ x‖^2},
    K.isCompact.inter_right (isClosed_le continuous_const
      (continuous_const.mul ((continuous_phaseDerivative hφ).norm.pow 2)))⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RealPhaseChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual phase chart in the real pair coordinates used by curvature. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial

def realPhaseChart (e : OpenPartialHomeomorph Base Base) :
    OpenPartialHomeomorph SmallModes.Base SmallModes.Base :=
  (planeCoordinateIsometry.symm.toHomeomorph.transOpenPartialHomeomorph e).transHomeomorph
    planeCoordinateIsometry.toHomeomorph

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate polynomial expressions for the metric coefficients in
the finite oscillatory recursion. Index zero denotes the first correction. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

def xCoefficient (dx : Fin 2) (U : ℕ → VectorExpression) (i : ℕ) : VectorExpression :=
  ((U (i - 1)).slow dx).add (U i).angle

def yCoefficient (dy : Fin 2) (U : ℕ → VectorExpression) (i : ℕ) : VectorExpression :=
  (U (i - 1)).slow dy

def xxQuadratic (dx : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  Expression.sumFinset (Finset.Ico 1 r) (fun i =>
    (xCoefficient dx U i).dot (xCoefficient dx U (r - i)))

def xyQuadratic (dx dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  Expression.sumFinset (Finset.Ico 1 r) (fun i =>
    (xCoefficient dx U i).dot (yCoefficient dy U (r - i)))

def yyQuadratic (dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  Expression.sumFinset (Finset.Ico 1 r) (fun i =>
    (yCoefficient dy U i).dot (yCoefficient dy U (r - i)))

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right-hand sides of the finite triangular correction step are actual
higher-jet polynomials. Their maximal jet order is the preceding order plus one. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

def mixedForcing (X Y : VectorExpression) (dx dy : Fin 2) (U : ℕ → VectorExpression)
    (r : ℕ) : Expression :=
  .add (.add (X.dot (yCoefficient dy U r)) (Y.dot ((U (r - 1)).slow dx)))
    (xyQuadratic dx dy U r)

def longitudinalForcing (X : VectorExpression) (dx : Fin 2) (U : ℕ → VectorExpression)
    (r : ℕ) : Expression :=
  .add (X.dot ((U (r - 1)).slow dx)) ((xxQuadratic dx U r).scale (1 / 2))

def transverseForcing (dy : Fin 2) (U : ℕ → VectorExpression) (r : ℕ) : Expression :=
  yyQuadratic dy U (r + 1)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialJetRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite jet-order induction for the explicit periodic correction recursion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open Expression

def transverse (Y : LowJet → R4) : VectorExpression := fun a => .coeff (fun z => Y z.1 a)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-jet geometry and the initial primitive in the actual periodic family
are represented by the corresponding coordinate polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector

namespace VectorExpression

def sub (R T : VectorExpression) : VectorExpression := fun i => (R i).sub (T i)

end VectorExpression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jet-polynomial representations of every coefficient of the finite
pullback-metric remainder. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion

def finiteMetric (L r : ℕ) (X Y : ℕ → VectorExpression) : Expression :=
  Expression.sumFinset (Finset.range (L + 1)) (fun i =>
    Expression.sumFinset (Finset.range (L + 1)) (fun j =>
      if i + j = r then (X i).dot (Y j) else .coeff (fun _ => 0)))

def xTangent (X : VectorExpression) (dx : Fin 2) (U : ℕ → VectorExpression) (L i : ℕ) :
    VectorExpression :=
  if i = 0 then X else if i = L then (U (i - 1)).slow dx else xCoefficient dx U i

def yTangent (Y : VectorExpression) (dy : Fin 2) (U : ℕ → VectorExpression) (i : ℕ) :
    VectorExpression := if i = 0 then Y else yCoefficient dy U i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TangentMetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite-tail estimate to the actual two tangent expansions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

def tangentExpression (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (dx dy : Fin 2) (L : ℕ) (b : Bool) : ℕ → VectorExpression :=
  if b then xTangent X dx R L else yTangent Y dy R

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasSupportedPolynomialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of a globally defined polynomial in a chart-supported
direction is the restoration of that chart's actual local linearization. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance supportedVariationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance supportedVariationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance supportedVariationDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
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
local instance restoredDirectionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredDirectionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberSpace
local instance polynomialAssemblyDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundedCoefficientRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual supported metric-cancelling recursion with uniform fast-scale
estimates. All losses are determined by the finite symbolic recursion before
the slow map or its scales are chosen. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector WeightedEstimates

namespace VectorExpression

def finiteLoss (R : ℕ → VectorExpression) (L : ℕ) : ℕ :=
  (Finset.range L).sup (fun i => Finset.univ.sup (fun a => (R i a).loss))

end VectorExpression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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

lemma slot_smooth (i : Fin 7) : ContDiff ℝ ∞ (slot i) := by
  apply contDiff_pi.mpr
  intro a
  exact (ContinuousLinearMap.proj (.inr (i, a)) : LowJet →L[ℝ] ℝ).contDiff

lemma slot_y_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => slot 2 (lowJet G q)) p (coordinateVector 1) = slot 6 (lowJet G p) := by
  funext a
  have hs := (slot_smooth 2).comp (lowJet_smooth hG)
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector 1))
    (fderiv_apply (hs.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => lowJet G q (.inr (2, a))) p (coordinateVector 1) := he.symm
    _ = lowDerivative G 1 p (.inr (2, a)) := lowJet_coordinate_derivative G 1 _ p
    _ = slot 6 (lowJet G p) a := rfl

lemma tangential_part_perp (X Y C w : RVec 4)
    (hY : Y ⬝ᵥ w = 0) (hC : C ⬝ᵥ w = 0) :
    (X - realNormalPart Y C X) ⬝ᵥ w = 0 := by
  simp only [realNormalPart, sub_dotProduct, smul_dotProduct, hY, hC,
    smul_eq_mul, mul_zero, sub_zero, sub_self]

end ClosedSurfaceR4.JetVelocityCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
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
def tangent (J : LowJet) : RVec 4 := slot 1 J - normal J

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

include l in
lemma smoothNormal : ContDiffOn ℝ ∞ normal O := by
  intro J hJ
  exact (contDiffAt_realNormalPart (slot_smooth 2).contDiffAt
    (slot_smooth 6).contDiffAt (slot_smooth 1).contDiffAt (l.gram_ne J hJ)).contDiffWithinAt

include l in
lemma smoothTangent : ContDiffOn ℝ ∞ tangent O := (slot_smooth 1).contDiffOn.sub l.smoothNormal

def q (J : LowJet) : ℝ := normal J ⬝ᵥ normal J + l.amplitude J ^ 2

lemma smoothQ : ContDiffOn ℝ ∞ l.q O :=
  (VelocityFrame.dot_smoothOn l.smoothNormal l.smoothNormal).add (l.smoothAmplitude.pow 2)

lemma q_pos {J : LowJet} (hJ : J ∈ O) : 0 < l.q J := by
  exact Real.sqrt_pos.mp (VelocityFrame.velocityRadius_pos (l.nonzero J hJ))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyFiberSpace
local instance primitivePolyDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyFiberNormed
local instance primitivePolySectionNormed_r3832e2_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitivePolySectionSpace_r3832e2_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- A single primitive's mean polynomial in the fixed atlas. -/
def primitiveAtlasPolynomial {n : ℕ} (i : A.centers) (P : Fin 3 → Fin n → Expression)
    (j : A.centers) : Fin 3 → Fin n → Expression := by
  classical
  exact if j = i then P else fun _ _ => Expression.coeff (fun _ => 0)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CutoffTensorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positional cutoffs of the actual finite tensor polynomial. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def cutoffTensorPolynomial {n : ℕ} (χ : Base → ℝ)
    (P : Fin 3 → Fin n → Expression) : Fin 3 → Fin n → Expression :=
  fun k r => (Expression.coeff (fun z => χ (lowPosition z.1))).mul (P k r)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSurfaceCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical jet corrections on the actual surface. The disjoint
coordinate balls are chosen before restoring and normalizing the corrections. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def finiteSurfaceQuadratic (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) : M → Space := fun x => ∑ p : P,
  euclideanRestore (c p : M) (A.outer (c p))
    (scaledQuadraticCutoff (sphericalSecondFormCLM (A.euclideanChartRead (c p) F)
      (chartAt Plane (c p : M) p)) (chartAt Plane (c p : M) p) (r p)) x

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPullbackNorm
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A numerical operator norm bound for covariant two-tensor pullback. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma norm_evaluate_le (A : Tensor) (v w : Base) :
    ‖evaluate A v w‖ ≤ 4*‖A‖*‖v‖*‖w‖ := by
  have hA (i : Fin 3) : ‖A i‖ ≤ ‖A‖ := norm_le_pi_norm A i
  have hv1 := norm_fst_le v
  have hv2 := norm_snd_le v
  have hw1 := norm_fst_le w
  have hw2 := norm_snd_le w
  have hmid : ‖v.1*w.2+v.2*w.1‖ ≤ ‖v‖*‖w‖+‖v‖*‖w‖ := by
    calc
      _ ≤ ‖v.1*w.2‖+‖v.2*w.1‖ := norm_add_le _ _
      _ ≤ _ := by simp only [norm_mul]; gcongr
  have h0 : ‖A 0*v.1*w.1‖ ≤ ‖A‖*‖v‖*‖w‖ := by
    simp only [norm_mul]
    gcongr
    exact hA 0
  have h1 : ‖A 1*(v.1*w.2+v.2*w.1)‖ ≤ ‖A‖*(‖v‖*‖w‖+‖v‖*‖w‖) := by
    rw [norm_mul]
    exact mul_le_mul (hA 1) hmid (norm_nonneg _) (norm_nonneg _)
  have h2 : ‖A 2*v.2*w.2‖ ≤ ‖A‖*‖v‖*‖w‖ := by
    simp only [norm_mul]
    gcongr
    exact hA 2
  calc
    _ ≤ ‖A 0*v.1*w.1‖ + ‖A 1*(v.1*w.2+v.2*w.1)‖ + ‖A 2*v.2*w.2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖A‖*‖v‖*‖w‖ + ‖A‖*(‖v‖*‖w‖+‖v‖*‖w‖) + ‖A‖*‖v‖*‖w‖ :=
      add_le_add (add_le_add h0 h1) h2
    _ = _ := by ring

lemma norm_pullback_le (L : Base →L[ℝ] Base) : ‖pullback L‖ ≤ 4*‖L‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖evaluate A (L (firstDirection i)) (L (secondDirection i))‖ ≤ _
  have hv : ‖L (firstDirection i)‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left (firstDirection_norm i) (norm_nonneg L))
  have hw : ‖L (secondDirection i)‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left (secondDirection_norm i) (norm_nonneg L))
  calc
    _ ≤ 4*‖A‖*‖L (firstDirection i)‖*‖L (secondDirection i)‖ := norm_evaluate_le _ _ _
    _ ≤ 4*‖A‖*‖L‖*‖L‖ := by gcongr
    _ = _ := by ring

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LinearMeanBudgetsFromBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mean budgets in a linear phase chart, with all geometric
constants specified by operator norms and supplied field bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes PhaseGeometry WeightedEstimates

noncomputable def linearMeanBudgetsOfBounds
    {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
    (s : ℝ) (F : RField 4) (ψ : Base → ℝ) (Q : Tensor →L[ℝ] ℝ)
    (C N P : ℕ → ℝ) (hC : ∀ m, 1 ≤ C m) (hN : ∀ m, 1 ≤ N m) (hP : ∀ m, 1 ≤ P m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun x => complexify (F x))
      (linearPhaseChart ξ hξ U hU).target s m (C m))
    (hn : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (N m) (freeNormal F))
    (hψ : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ) :
    Budgets U (linearPhaseChart ξ hξ U hU).target s F ψ (fun _ => Q)
      (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm where
  inv := fun _ => max 1 ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖
  chi := fun _ => max 1 (2*‖ξ‖)
  forms := fun _ => max 1 ‖Q‖
  pull := fun _ => max 1 (16*‖ξ‖^2)
  psi := P
  normal := N
  mode := C
  inv_pos := fun _ => le_max_left _ _
  chi_pos := fun _ => le_max_left _ _
  forms_pos := fun _ => le_max_left _ _
  pull_pos := fun _ => le_max_left _ _
  psi_pos := hP
  normal_pos := hN
  mode_pos := hC
  inv_bound := by
    intro m j hj _ x hx
    exact (positive_order_linear_derivative_le (phaseEquiv ξ hξ).symm.toContinuousLinearMap
      (linearPhaseChart ξ hξ U hU).open_target hj hx).trans (le_max_right _ _)
  chi_bound := by
    intro m j hj _ x hx
    exact (linearPhaseChart_derivative_bound hξ hU hj hx).trans (le_max_right _ _)
  psi_bound := hψ
  normal_bound := hn
  mode_bound := hc
  forms_bound := fun m => (weightedBound_const _ s m Q).mono_const (le_max_right _ _)
  pull_bound := by
    intro m
    have hL := phaseEquiv_norm_le ξ hξ
    have hP : ‖pullback (phaseEquiv ξ hξ).toContinuousLinearMap‖ ≤ 16*‖ξ‖^2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg (phaseEquiv ξ hξ).toContinuousLinearMap) hL 2
      exact (norm_pullback_le _).trans (by nlinarith [hsq])
    have he : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [he]
    exact (weightedBound_const U s m _).mono_const (hP.trans (le_max_right _ _))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbationTaylorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite polynomial perturbation has a cubic nonlinear remainder with
one fixed scale loss. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ParameterTaylor WeightedEstimates

variable {n : ℕ}

def taylorRemainder (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space) (θ : ℝ) : Base → ℝ :=
  fun p => ∑ l, ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RealPolynomialVariationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for arbitrary real variations at the short scale. These are the
nonoscillatory estimates used for mixed terms and the Taylor remainder. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

def realVariation {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Fin 4 → Base → Space) (i : Fin 3) (t : ℝ) : Base → ℝ :=
  fun p => ∑ l, ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RealPolynomialQuadraticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear bounds for the mixed polynomial contribution of the free and
forced displacements. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

def quadraticCross {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G H K : Base → Space) (t : ℝ) : Base → ℝ :=
  fun p => (1 / 2 : ℝ) * (realVariation P ε ![G,H,K,0] 1 t p +
    realVariation P ε ![G,K,H,0] 1 t p)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRealVariationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common tensor bounds for the actual mixed quadratic term and cubic
Taylor remainder. The exponent does not depend on the correction depth. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def tensorQuadraticCross {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G H K : Base → Space) (t : ℝ) : Base → PhaseMean.Tensor :=
  fun p k => quadraticCross (P k) ε G H K t p

def tensorTaylorRemainder {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G H : Base → Space) (t : ℝ) : Base → PhaseMean.Tensor :=
  fun p k => taylorRemainder (P k) ε G H t p

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialInteractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only the polynomial part of the mixed free/forced quadratic error. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def coordinatePolynomialInteraction {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X Y : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  (tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry)
    (Y ∘ planeCoordinateIsometry) 0 ∘ planeCoordinateIsometry.symm)+
    coordinateQuadraticPolynomial P ε G Y 0

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredPolynomialModeMean
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
local instance restoredPolynomialMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredPolynomialMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredPolynomialMeanDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PerturbedSolverTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add a fixed polynomial perturbation to an existing geometric solver.
The polynomial bound is obtained uniformly from a fixed compact jet range
and fixed coordinate profiles, before the map and scales are supplied. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

namespace PolynomialSolveData

/-- Reuse all geometric and reconstruction data.  The uniform theorem below
provides the polynomial estimate required by this constructor. -/
def withPolynomial {n : ℕ} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    (c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (hGO : Set.MapsTo (lowJet G) c₀.U O) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z) :
    PolynomialSolveData P ε G hG φ K τ s where
  U := c₀.U
  O := O
  openU := c₀.openU
  openO := hO
  smoothP := hP
  mapsG := hGO
  supportU := c₀.supportU
  smoothPhase := c₀.smoothPhase
  e := c₀.e
  smoothForward := c₀.smoothForward
  smoothInverse := c₀.smoothInverse
  supportChart := c₀.supportChart
  phase := c₀.phase
  smoothMap := c₀.smoothMap
  domain := c₀.domain
  C := c₀.C
  D := D
  J := c₀.J
  nonnegC := c₀.nonnegC
  nonnegD := hD
  oneLEJ := c₀.oneLEJ
  coordinates := c₀.coordinates
  coefficients := c₀.coefficients
  polynomial := hpoly

end PolynomialSolveData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbedMeanTransfer
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer actual geometric mean data to a fixed polynomial perturbation.
The cutoff, form, local geometry and reconstruction budgets stay the same.
Only the polynomial profile and the required input-jet orders change. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

lemma empty_tensorOrder : tensorOrder emptyMetricPolynomial = 0 := by
  simp [tensorOrder,order,emptyMetricPolynomial]

def ChartedMeanProfile.withPolynomial {n : ℕ}
    (p₀ : ChartedMeanProfile emptyMetricPolynomial)
    (P : Fin 3 → Fin n → Expression) {O : Set LowJet} (hO : IsOpen O)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (hQO : p₀.Q ⊆ O) (D : ℕ → ℝ) :
    ChartedMeanProfile P where
  U := p₀.U
  O := O
  Q := p₀.Q
  V := p₀.V
  openU := p₀.openU
  openO := hO
  openV := p₀.openV
  compact := p₀.compact
  subsetDomain := hQO
  smoothP := hP
  C := p₀.C
  D := D
  J := p₀.J
  inv := p₀.inv
  forms := p₀.forms
  psi := p₀.psi
  normal := p₀.normal
  B := fun m => p₀.B (m + tensorOrder P)
  F := fun m => p₀.F (m + tensorOrder P)
  nonnegC := p₀.nonnegC
  oneLEJ := p₀.oneLEJ
  oneLEInv := p₀.oneLEInv
  oneLEForms := p₀.oneLEForms
  oneLEPsi := p₀.oneLEPsi
  oneLENormal := p₀.oneLENormal
  oneLEB := fun m => p₀.oneLEB (m + tensorOrder P)
  nonnegF := fun m => p₀.nonnegF (m + tensorOrder P)

namespace ChartedMeanData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    {c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def withPolynomial {n : ℕ} (d₀ : ChartedMeanData c₀ r ρ R reference)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (hGO : Set.MapsTo (lowJet G) c₀.U O) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z)
    (hQO : d₀.compactJets ⊆ O) :
    ChartedMeanData (c₀.withPolynomial P ε hO hP hGO D hD hpoly) r ρ R reference where
  cutoff := d₀.cutoff
  form := d₀.form
  localBounds := d₀.localBounds
  budgets := d₀.budgets
  compactJets := d₀.compactJets
  compact := d₀.compact
  subsetDomain := hQO
  mapsJets := d₀.mapsJets
  B := fun m => d₀.B (m + tensorOrder P)
  F := fun m => d₀.F (m + tensorOrder P)
  oneLEB := fun m => d₀.oneLEB (m + tensorOrder P)
  nonnegF := fun m => d₀.nonnegF (m + tensorOrder P)
  jetsBound := by
    intro m
    change WeightedBound c₀.U s (m + tensorOrder P)
      (d₀.B (m + tensorOrder P)) (lowJet G)
    simpa only [empty_tensorOrder,Nat.add_zero] using d₀.jetsBound (m + tensorOrder P)
  phaseBound := by
    intro m v
    change WeightedBound c₀.U s (m + tensorOrder P)
      (d₀.F (m + tensorOrder P)) (fun x => fderiv ℝ φ x (coordinateVector v))
    simpa only [empty_tensorOrder,Nat.add_zero] using d₀.phaseBound (m + tensorOrder P) v

end ChartedMeanData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformPolynomialSmallIncrement
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
local instance uniformPolynomialSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance uniformPolynomialSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance uniformPolynomialSmallDualAdd_r3832e2_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance uniformPolynomialSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MetricPolynomialSlowStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One uniform step of the finite slow-map construction. The derivative
profiles and the small parameter threshold precede the nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization
local instance slowPolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CovectorPullbackParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual pullback of phase covectors by a chart derivative. Its parameter
map is open when the chart determinant is nonzero. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def pullCovectorMap (A : CurvePlane →L[ℝ] CurvePlane) : CurvePlane →L[ℝ] CurvePlane :=
  (((A dx).1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    ((A dx).2 • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
  (((A dy).1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    ((A dy).2 • ContinuousLinearMap.snd ℝ ℝ ℝ))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothCircularRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth global radius field agrees with the actual squared coordinate
radius near every strictly smaller disk boundary. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def circularRadiusField (i : A.centers) : M → ℝ :=
  restore (i : M) (A.outer i)
    (circularRadiusSquared (coordinateChart (i : M) (i : M)) ∘ planeCoordinateIsometry)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the five-profile coefficient map with the genuine
second fundamental form of a smooth immersion. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def realBoundaryProfile (F : RField 4) (z : ℝ) (p : Base) : BoundaryProfile :=
  ![coordDeriv dx F p,coordDeriv dy F p,coordDeriv dy (coordDeriv dy F) p,
    coordDeriv dx (coordDeriv dy F) p,z • coordDeriv dx (coordDeriv dx F) p]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetSecondForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unscaled five-jets encode the actual second form and ordered crossings.
These expressions are used for exterior C2 stability. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetSecond (J : BoundaryProfile) (v w : Base) : Vec :=
  realNormalPart (J 0) (J 1)
    ((v.1*w.1) • J 4+(v.1*w.2+v.2*w.1) • J 3+(v.2*w.2) • J 2)

def boundaryJetCrossing (J : BoundaryProfile) (v w : Base) (κ : ℝ) : ℝ :=
  (boundaryJetSecond J v w ⬝ᵥ normalize (boundaryJetSecond J v v))^2+
    κ*NormalFrame.gramDet (v.1 • J 0+v.2 • J 1) (w.1 • J 0+w.2 • J 1)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior antipode exclusions are open conditions on the unscaled
second jet and the preferred normal. Compactness makes the tolerance uniform. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetAvoidance : Set (BoundaryProfile × (Vec × Base)) :=
  {a | NormalFrame.gramDet (a.1 0) (a.1 1) ≠ 0 ∧
    boundaryJetSecond a.1 a.2.2 a.2.2 ≠ 0 ∧
    a.2.1 ≠ -normalize (boundaryJetSecond a.1 a.2.2 a.2.2)}

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The induced Gaussian curvature is a continuous function of the unscaled
second jet on the immersion locus. This controls the new curvature in exterior estimates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame

def boundaryJetCurvature (J : BoundaryProfile) : ℝ :=
  (boundaryJetSecond J dx dx ⬝ᵥ boundaryJetSecond J dy dy -
    boundaryJetSecond J dx dy ⬝ᵥ boundaryJetSecond J dx dy) / gramDet (J 0) (J 1)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exterior preservation of the positive normal pairings. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetPositivity : Set (BoundaryProfile × (Vec × Base)) :=
  {a | NormalFrame.gramDet (a.1 0) (a.1 1) ≠ 0 ∧
    0 < boundaryJetSecond a.1 a.2.2 a.2.2 ⬝ᵥ a.2.1}

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryNormalMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform strict data for the interior/exterior normal interpolation.
The new canonical yy normal and the exterior normal both pair positively
with every later curve meeting the support boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryPreferredPairing : Set (BoundaryProfile × Base) :=
  {a | a.1 ∈ regularBoundaryProfiles ∧ 0 < boundaryJetSecond a.1 a.2 a.2 ⬝ᵥ profilePreferred a.1}

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CoefficientJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite first and second slow/angular coefficient jets needed by the
primitive's five leading derivative estimates share one fixed scale loss. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

def coefficientDerivative (R : VectorExpression) (k : Fin 3) : VectorExpression :=
  ![R.slow 0,R.slow 1,R.angle] k

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicFastEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chain rule for substituting a fast linear phase in a smooth periodic family. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Family

def fastValue (U : Family A E) (ℓ : A →L[ℝ] ℝ) (z : ℝ) (p : A) : E :=
  U.val p ((ℓ p / z : ℝ) : Period)

end Family
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicFiniteAnsatz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite oscillatory map and its actual first derivatives. -/

noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def finiteAnsatz (F : A → E) (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p : A) : E :=
  F p + ∑ i ∈ Finset.range L, z ^ (i + 1) • (U i).fastValue ℓ z p

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAnsatzAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact, fixed-coefficient asymptotics of the finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite polynomial before the extra factor of the fast scale. -/
def phaseSum (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p : A) : E :=
  ∑ i ∈ Finset.range L, z^i • (U i).fastValue ℓ z p

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactPositiveMetricJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed family of first metric jets with a fixed positive lower
bound is compact. It therefore fixes the connection bound before any
finite-point modification or choice of disk centers. -/
noncomputable section
open Set Metric
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes PhaseMean

def positiveMetricJetRegion (c B : ℝ) : Set MetricFirstJet :=
  {j | ‖j‖ ≤ B ∧ ∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v}

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitSplitCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-chart correction retains explicit coordinate, splitting and
cardinality factors. These factors can be bounded before a fast scale is chosen. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

 def splitInputBudget (q m : ℕ) (I S : ℕ → ℝ) : ℝ :=
  let k := PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m
  tensorChartBudget k (I k) (I (k+1))*S k

 def splitSizeBudget (q m : ℕ) (C J I S : ℕ → ℝ) : ℝ :=
  max 1 (metricForcedSizeBudget C J (fun _ => 1) q m)*splitInputBudget q m I S

 def splitResidualBudget (q m : ℕ) (C J I S : ℕ → ℝ) : ℝ :=
  max 1 (metricForcedResidualBudget C J (fun _ => 1) q m)*splitInputBudget q m I S

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularBoundaryProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar limits controlling the boundary argument for a circular
velocity, in the canonical normal frame read from the five profiles. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

def circularBoundaryProfile (X Y C W e₁ e₂ : Vec) (R α β : ℝ) : BoundaryProfile :=
  ![leadingTangent X Y C (R • direction e₁ e₂ α),Y,C,W,
    (R*β) • angularDirection e₁ e₂ α]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FrozenBoundaryCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical profile coefficients have the same fixed bounds and turn
mechanism as the explicit circular velocity used to construct the loop. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def circularSpatialProfile (Q X Y C : E → Vec) (R : E → ℝ)
    (e₁ e₂ : E → Vec) (α : E → ℝ) (β : ℝ) (x d : E) : BoundaryProfile :=
  circularBoundaryProfile (X x) (Y x) (C x)
    (fderiv ℝ (fun y => Q y+R y • direction (e₁ y) (e₂ y) (α y)) x d)
    (e₁ x) (e₂ x) (R x) (α x) β

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedTensorPullbackBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported tensor pullback has a fixed weighted norm on each finite order. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def localizedTensorPullback (T : Base → Base) (χ : Base → ℝ)
    (f : Base → PhaseMean.Tensor) (x : Base) : PhaseMean.Tensor :=
  χ x • tensorCoordinatePullbackValue T x (f (T x))

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricAcceleration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The negative tangential acceleration required by the velocity plane is
the actual Christoffel coefficient of the induced metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame PhaseGeometry

def inducedCoordinateMetric (F : RField 4) (p : Base) : PhaseMean.Tensor :=
  ![realMetric F dx dx p,realMetric F dx dy p,realMetric F dy dy p]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceTimeBlend
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual blend of surface time charts is regular at every common
axis point where their transverse transition is positive. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

def surfaceTimeBlend (c d : SurfaceTimeChart F) (χ : ℝ → ℝ) (x : M) : Base :=
  (1-χ (F x)) • c.coord x + χ (F x) • d.coord x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TimeBlendDomain
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An open domain for joining time charts using an exact scalar cutoff. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

def timeBlendDomain (c d : SurfaceTimeChart F) (l r : ℝ) : Set M :=
  (c.coord.source ∩ F ⁻¹' Iio l) ∪ (c.coord.source ∩ d.coord.source) ∪
    (d.coord.source ∩ F ⁻¹' Ioi r)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleLocusSmoothStructure
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transverse ordered double locus carries its actual smooth
one-dimensional manifold structure, built from the proved submersion charts. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3}

def transverseDoubleChart
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (p : surfaceDoublePairs f) : SmoothDoubleChart f :=
  (exists_smooth_double_chart hf p (hreg _ _ p.property.1 p.property.2)).choose

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

def transportedNormalFrame (φ : Base → ProjectionTarget 3) (a : FrameTarget)
    (d : ℝ → Base) (B : Base → Base →L[ℝ] FrameTarget) (x : Base) :
    Base →L[ℝ] FrameTarget :=
  (curveNormalLinear (transverseDerivative φ x) a).comp
    ((normalOutput (d (x 1))).comp ((B x).comp (longitudinalShear (longitudinalCoefficient φ a x))))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectedNormalLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normalization of the atlas projection on an exterior open set. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def unitProjectedNormalField (F n : M → Space) : M → Space :=
  SphericalJets.radialNormalize ∘ A.projectedNormalField F n

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShortMetricPath
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
local instance pathFiberNormed_r3832e2_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance pathFiberSpace_r3832e2_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance pathDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedLocalMetricDefect
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
local instance supportedLocalDefectFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance supportedLocalDefectFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance supportedLocalDefectDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance supportedLocalDefectDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance supportedLocalDefectSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the first two transverse derivatives of represented
periodic coefficients. Their common loss is fixed before the slow map. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

def transverse (R : VectorExpression) (second : Bool) : VectorExpression :=
  if second then (R.slow 1).slow 1 else R.slow 1

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformRemainderBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed C2 budget for starting maps gives one C1 remainder bound in
any fixed primitive atlas, before choosing finite modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance remainderBoundFiberNormed_r3832e2_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance remainderBoundFiberSpace_r3832e2_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance remainderBoundDualAdd_r3832e2_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance remainderBoundDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance remainderBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformStartingFamily
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The starting family for the global preparation, conditional only on
Whitney's published compact-surface immersion theorem. All uniform constants
are fixed before the boundary intersections are specified. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def PreferredNormal.const_smul {F : M → Space} (n : PreferredNormal F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ) : PreferredNormal (r • F) where
  vector := n.vector
  smooth := n.smooth
  unit := n.unit
  normal p v := by
    have hd := const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) r
    change inner ℝ (show Space from mfderiv planeModel spaceModel (r • F) p v) (n.vector p) = 0
    rw [hd]
    change inner ℝ (r • (show Space from mfderiv planeModel spaceModel F p v)) (n.vector p) = 0
    rw [real_inner_smul_left,n.normal,mul_zero]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnperturbedSolverFromBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual metric solver with specified numerical bounds.
No compactness choice of coefficients is used by this constructor. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes

noncomputable def unperturbedSolverOfBounds
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (hdom : RealModeDomain ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) e.target)
    (τ : ℝ) (s : ℝ≥0) (C J : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hJ : ∀ m, 1 ≤ J m)
    (hc : ∀ m, SmallModes.ReconstructionCoefficientBound
      (fun p => complexify (G (planeCoordinateIsometry.symm (e.symm p)))) e.target s (m+1) (C m))
    (hj : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m) :
    PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s where
  U := univ
  O := univ
  openU := isOpen_univ
  openO := isOpen_univ
  smoothP := fun _ l => Fin.elim0 l
  mapsG := mapsTo_univ _ _
  supportU := subset_univ _
  smoothPhase := hφ
  e := e
  smoothForward := he.contDiffOn
  smoothInverse := hi.contDiffOn
  supportChart := hKe
  phase := hphase
  smoothMap := (hG.comp planeCoordinateIsometry.symm.contDiff).comp hi
  domain := hdom.complexDomain ((hG.comp planeCoordinateIsometry.symm.contDiff).comp hi)
  C := C
  D := fun _ => 0
  J := J
  nonnegC := hC
  nonnegD := fun _ => le_rfl
  oneLEJ := hJ
  coordinates := hj
  coefficients := hc
  polynomial := by
    intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnperturbedSolverRestrictedDomain
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict the positional domain of an unperturbed supported solver.
Its phase chart, operator, and numerical coefficient budgets stay fixed. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

namespace PolynomialSolveData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}

def onSourceDomain (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (U : Set Base) (hU : IsOpen U) (hKU : (K : Set Base) ⊆ U) :
    PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s where
  U := U
  O := univ
  openU := hU
  openO := isOpen_univ
  smoothP := fun _ j => Fin.elim0 j
  mapsG := mapsTo_univ _ _
  supportU := hKU
  smoothPhase := c.smoothPhase
  e := c.e
  smoothForward := c.smoothForward
  smoothInverse := c.smoothInverse
  supportChart := c.supportChart
  phase := c.phase
  smoothMap := c.smoothMap
  domain := c.domain
  C := c.C
  D := fun _ => 0
  J := c.J
  nonnegC := c.nonnegC
  nonnegD := fun _ => le_rfl
  oneLEJ := c.oneLEJ
  coordinates := c.coordinates
  coefficients := c.coefficients
  polynomial := by
    intro m Z
    rw [phaseChartPolynomialOperator_zero]
    simp

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryJetCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both ordered boundary inequalities persist under small exterior C2 changes. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def boundaryJetCrossings : Set (BoundaryProfile × (Base × (Base × ℝ))) :=
  {a | NormalFrame.gramDet (a.1 0) (a.1 1) ≠ 0 ∧
    boundaryJetSecond a.1 a.2.1 a.2.1 ≠ 0 ∧
    boundaryJetSecond a.1 a.2.2.1 a.2.2.1 ≠ 0 ∧
    0 < boundaryJetCrossing a.1 a.2.1 a.2.2.1 a.2.2.2 ∧
    0 < boundaryJetCrossing a.1 a.2.2.1 a.2.1 a.2.2.2}

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFamilyProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five boundary profiles for a smooth family of circular velocities. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def circularFamilyProfile (Q X Y C : E → Vec) (R : E → ℝ)
    (e₁ e₂ : E → Vec) (α : E × ℝ → ℝ) (d : E) (z : E × ℝ) : BoundaryProfile :=
  circularBoundaryProfile (X z.1) (Y z.1) (C z.1)
    (fderiv ℝ (fun w : E × ℝ => Q w.1 + R w.1 • direction (e₁ w.1) (e₂ w.1) (α w)) z (d,0))
    (e₁ z.1) (e₂ z.1) (R z.1) (α z) (fderiv ℝ α z (0,1))

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IntrinsicExteriorCrossings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior C2 stability for both ordered crossings with the new
immersion's actual Gaussian curvature. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

def intrinsicBoundaryJetCrossings : Set (BoundaryProfile × (Base × Base)) :=
  {a | (a.1,a.2.1,a.2.2,boundaryJetCurvature a.1) ∈ boundaryJetCrossings}

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SecondCoefficientProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second coefficient derivatives agree with the local represented jets,
even when only their germs agree after the first derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector JetPolynomial

def globalCoefficientDerivative (W : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean)
    (k : Fin 3) : PeriodicExpansion.Family Base JetVelocityCoordinates.Euclidean :=
  ![W.slow (coordinateVector 0),W.slow (coordinateVector 1),W.angle] k

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformPrimitiveProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All five actual derivative profiles share a loss fixed before the slow
map. The leading profiles are the geometric velocity and its derivatives. -/
noncomputable section
open Set
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

def primitiveJetProfile (f : JetPolynomial.Base → Euclidean) (z : ℝ)
    (p : JetPolynomial.Base) : Fin 5 → Euclidean :=
  ![PeriodicExpansion.directionalMap f (coordinateVector 0) p,
    PeriodicExpansion.directionalMap f (coordinateVector 1) p,
    PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 1))
      (coordinateVector 1) p,
    PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
      (coordinateVector 1) p,
    z • PeriodicExpansion.directionalMap (PeriodicExpansion.directionalMap f (coordinateVector 0))
      (coordinateVector 0) p]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseCrossingTransversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent phase covectors give the nonzero first components of the
actual transported directions at every finite crossing. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SmallModes RealModes SurfaceJetCoordinates PhaseGeometry

namespace PhaseGeometry

def firstCoordinateCovector (L : Base →L[ℝ] Base) : Base := ((L dx).1,(L dy).1)

end PhaseGeometry

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the actual primitive support instead of enlarging it to the
whole atlas patch. The closure also works without a Hausdorff hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseSurfaceSupport (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (K : Set JetPolynomial.Base) : Set M :=
  closure ((chart (i : M)).symm '' (e.symm '' K))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transported primitive is the square of the actual first phase
covector, with its supported amplitude. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial

def firstPhaseCovector (T : Base → Base) (x : Base) : SmallModes.Base :=
  ((fderiv ℝ T x (coordinateVector 0)) 0,(fderiv ℝ T x (coordinateVector 1)) 0)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveTermC1Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primitive tensor terms have a uniform C1 bound from their scalar
amplitude and phase-covector coordinate bounds. All constants precede those
functions and every later cycle count. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance termBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance termBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance termBoundDualNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance termBoundDualSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance termBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance termBoundDualSmul_r3832e2_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance termBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end


