-- Prove2me | Definitions.Def_OAIQ231Rr000
-- name    : OAIQ231Rr000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:21:31.161199+00:00
-- url     : https://prove2.me/theorems/76b843f0-f459-4083-9c27-7ce9ad0d9679
-- title:
--   Definitions bundle OAIQ231Rr000 of the split of OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 454 declarations of OpenAI's Lean: 294 definitions, 8 inductive types or structures, 2 instances and 150 theorems. The definitions and types are `OAI.RieszRectifiability.ADRegular`, `OAI.RieszRectifiability.BadBetaDescendant`, `OAI.RieszRectifiability.BadSupportDescendant`, `OAI.RieszRectifiability.CappedLowerGrowth`, `OAI.RieszRectifiability.CellAnnulus`, `OAI.RieszRectifiability.CellAnnulus.transform`, `OAI.RieszRectifiability.CellHaarPair`, `OAI.RieszRectifiability.CellHaarPair.innerCell`, `OAI.RieszRectifiability.CellHaarPair.outerCell`, `OAI.RieszRectifiability.CellHaarPair.refl`, `OAI.RieszRectifiability.CellHaarPair.test`, `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.DyadicBoxIndex`, `OAI.RieszRectifiability.DyadicLipschitzFamily`, `OAI.RieszRectifiability.DyadicOscillationTests`, `OAI.RieszRectifiability.DyadicOscillationTests.normalized`, `OAI.RieszRectifiability.DyadicOscillationTests.weight`, `OAI.RieszRectifiability.ExcessBilateralConclusion`, `OAI.RieszRectifiability.GlobalBilateralLower`, `OAI.RieszRectifiability.GlobalSmoothAnnularBound`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.HasActiveCellInputChart`, `OAI.RieszRectifiability.HasActiveCellSurfaceChart`, `OAI.RieszRectifiability.HasActiveSurfaceCharts`, `OAI.RieszRectifiability.HasFlatBallAbove`, `OAI.RieszRectifiability.HasFlatCell`, `OAI.RieszRectifiability.HasFlatDescendant`, `OAI.RieszRectifiability.HasLargeCellAnnulus`, `OAI.RieszRectifiability.HasLargeSmoothAnnulusAbove`, `OAI.RieszRectifiability.HasSelectedRestartAssembly`, `OAI.RieszRectifiability.IsActiveRegionLimitModel`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.JetCoordinateIndex`, `OAI.RieszRectifiability.NoFlatDescendant`, `OAI.RieszRectifiability.OrderedSpanSeparated`, `OAI.RieszRectifiability.OriginalOscillationWitness`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.ScalarReflectionlessAt`, `OAI.RieszRectifiability.SelectedRestartSurfaceData`, `OAI.RieszRectifiability.SeparatedCover` and 262 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `RieszRectifiability_Flatness_AffineGraphPlane`, `RieszRectifiability_Flatness_AffinePlaneCoordinates`, `RieszRectifiability_Flatness_AffineTubeMass`, `RieszRectifiability_Flatness_AmbientAffineHeight`, `RieszRectifiability_Flatness_AssembledAffineHeight`, `RieszRectifiability_Flatness_BetaDescendantTotalMass`, `RieszRectifiability_Flatness_BilateralBeta`, `RieszRectifiability_Flatness_BlowupAffineGeometry`, `RieszRectifiability_Flatness_BoundedPlaneBoxes`, `RieszRectifiability_Flatness_FlatAnnularAlternativeEvents`, `RieszRectifiability_Flatness_FlatCellSeeds`, `RieszRectifiability_Flatness_FlatDescendantMass`, `RieszRectifiability_Flatness_JointPlaneGoodSet`, `RieszRectifiability_Flatness_OpenPlaneBoxes`, `RieszRectifiability_Flatness_PlaneDiskHausdorffMeasure`, `RieszRectifiability_Foundations_ADHoleDensity`, `RieszRectifiability_Foundations_AnnularBoundedTangents`, `RieszRectifiability_Foundations_BlowupMeasure`, `RieszRectifiability_Foundations_CappedLowerGrowth`, `RieszRectifiability_Foundations_CappedTestSymmetry`, `RieszRectifiability_Foundations_CappedTransform`, `RieszRectifiability_Foundations_DyadicLipschitzFamily`, `RieszRectifiability_Foundations_DyadicPropagationRadii`, `RieszRectifiability_Foundations_ExcessPropagationSchedule`, `RieszRectifiability_Foundations_FiniteNormalizedWeights`, `RieszRectifiability_Foundations_FinitePieceCoordinates`, `RieszRectifiability_Foundations_FiniteSupportRefinements`, `RieszRectifiability_Foundations_GeometricGramRows`, `RieszRectifiability_Foundations_GrowthVolumeDomination`, `RieszRectifiability_Foundations_ImmediateChildPartition`, `RieszRectifiability_Foundations_MeasureBounds`, `RieszRectifiability_Foundations_NeighboringFitErrors`, `RieszRectifiability_Foundations_NormalizedSetIndicators`, `RieszRectifiability_Foundations_OriginalDyadicTests`, `RieszRectifiability_Foundations_OriginalOscillationWitness`, `RieszRectifiability_Foundations_PlanarPullbackMeasure`, `RieszRectifiability_Foundations_PositiveNormalPotential`, `RieszRectifiability_Foundations_RegionRepresentativeGeometry`, `RieszRectifiability_Foundations_SeparatedParameterPatchGluing`, `RieszRectifiability_Foundations_SmoothAnnularWeights`, `RieszRectifiability_Foundations_TwoSidedIntrinsicDensity`, `RieszRectifiability_Foundations_UniformBilateralExcessPropagation`, `RieszRectifiability_Kernel_BoundedBoxContainment`, `RieszRectifiability_Kernel_BoundedRegionTests`, `RieszRectifiability_Kernel_CappedBilinearKernel`, `RieszRectifiability_Kernel_CappedEnergy`, `RieszRectifiability_Kernel_CappedRieszInterior`, `RieszRectifiability_Kernel_CappedRieszKernel`, `RieszRectifiability_Kernel_ClosedTailBounds`, `RieszRectifiability_Kernel_ComplexHeightPairing`, `RieszRectifiability_Kernel_CutoffError`, `RieszRectifiability_Kernel_DyadicAnnuli`, `RieszRectifiability_Kernel_DyadicBoxes`, `RieszRectifiability_Kernel_ExpandingSmoothCutoffs`, `RieszRectifiability_Kernel_FarKernelDifference`, `RieszRectifiability_Kernel_FarRieszTransform`, `RieszRectifiability_Kernel_FiniteRieszPairing`, `RieszRectifiability_Kernel_FiniteShellTail`, `RieszRectifiability_Kernel_FiniteStepLp`, `RieszRectifiability_Kernel_FiniteStepMoments`, `RieszRectifiability_Kernel_GradientRieszTestIdentity`, `RieszRectifiability_Kernel_HeightPairingRegions`, `RieszRectifiability_Kernel_InnerAnnuli`, `RieszRectifiability_Kernel_KernelBasic`, `RieszRectifiability_Kernel_KernelNear`, `RieszRectifiability_Kernel_KernelTails`, `RieszRectifiability_Kernel_LeastSquaredExcess`, `RieszRectifiability_Kernel_LipschitzTests`, `RieszRectifiability_Kernel_MeanZero`, `RieszRectifiability_Kernel_NearPairWeight`, `RieszRectifiability_Kernel_NormalCoordinateTests`, `RieszRectifiability_Kernel_NormalPairingEnergy`, `RieszRectifiability_Kernel_NormalizedBumpPairings`, `RieszRectifiability_Kernel_NormalizedEnergy`, `RieszRectifiability_Kernel_NormalizedExteriorPairing`, `RieszRectifiability_Kernel_NormalizedNormalCoordinates`, `RieszRectifiability_Kernel_OrderedSpanConditioning`, `RieszRectifiability_Kernel_OriginalTestCutoffError`, `RieszRectifiability_Kernel_OscillationEnergy`, `RieszRectifiability_Kernel_OscillationTests`, `RieszRectifiability_Kernel_PartitionEnergy`, `RieszRectifiability_Kernel_RenormalizedFarPairing`, `RieszRectifiability_Kernel_RieszPairingIdentification`, `RieszRectifiability_Kernel_ScalarRieszLocalBound`, `RieszRectifiability_Kernel_SchwartzNormDivision`, `RieszRectifiability_Kernel_SchwartzSecondDifference`, `RieszRectifiability_Kernel_ShrinkingSchwartzLocalization`, `RieszRectifiability_Kernel_ShrinkingSmoothCutoffs`, `RieszRectifiability_Kernel_SymmetricPairingSplit`, `RieszRectifiability_Kernel_TailBounds`, `RieszRectifiability_Kernel_UncenteredEnergy`, `RieszRectifiability_Kernel_UniformHeightTail`, `RieszRectifiability_Kernel_VectorKernelFarDifference`, `RieszRectifiability_Kernel_WeightedCentering`, `RieszRectifiability_Limits_CompactLipschitzAmplitude`, `RieszRectifiability_Limits_CompactRieszPairingTail`, `RieszRectifiability_Limits_CompactSmoothAnnularKernel`, `RieszRectifiability_Limits_CompactWeakConvergence`, `RieszRectifiability_Limits_CompactnessUnweighting`, `RieszRectifiability_Limits_CompactnessWeight`, `RieszRectifiability_Limits_CompactnessWeightIntegrals`, `RieszRectifiability_Limits_CompactnessWeightedMeasure`, `RieszRectifiability_Limits_OuterPairingLimit`, `RieszRectifiability_Limits_PolynomialLeadingLimit`, `RieszRectifiability_Limits_ScalarRieszTestLimit`, `RieszRectifiability_Limits_SignedKernelConvergence`, `RieszRectifiability_Limits_UniformNonflatLimits`, `RieszRectifiability_Limits_WeakRestriction`, `RieszRectifiability_Nets_AnnularCellGap`, `RieszRectifiability_Nets_AnnularLatticeScales`, `RieszRectifiability_Nets_BadCellTestFamily`, `RieszRectifiability_Nets_BoundaryCellGeometry`, `RieszRectifiability_Nets_CellAnnularWitnesses`, `RieszRectifiability_Nets_CellBadCountBounds`, `RieszRectifiability_Nets_CellChainComposition`, `RieszRectifiability_Nets_CellChainGeometry`, `RieszRectifiability_Nets_CellEnergy`, `RieszRectifiability_Nets_CellVariance`, `RieszRectifiability_Nets_ClosedNetCellCover`, `RieszRectifiability_Nets_ConstructedSupportCells`, `RieszRectifiability_Nets_CountableCellMultiplicity`, `RieszRectifiability_Nets_ExteriorCellMeans`, `RieszRectifiability_Nets_FiniteCoverCutoff`, `RieszRectifiability_Nets_LatticeDescendantGeometry`, `RieszRectifiability_Nets_NestedSeparatedNets`, `RieszRectifiability_Nets_NetAncestorForcing`, `RieszRectifiability_Nets_NetAncestors`, `RieszRectifiability_Nets_NetDeepCores`, `RieszRectifiability_Nets_NetDescendantCells`, `RieszRectifiability_Nets_RegularLatticeScales`, `RieszRectifiability_Nets_ScaledBallBumps`, `RieszRectifiability_Nets_SeparatedNetParents`, `RieszRectifiability_Nets_SeparatedSupportNets`, `RieszRectifiability_Nets_SmoothAnnularCellComparison`, `RieszRectifiability_Nets_SupportCellOverlaps`, `RieszRectifiability_Nets_SupportCellRoot`, `RieszRectifiability_Packing_ADInteractionPacking`, `RieszRectifiability_Packing_CellHaarFunctions`, `RieszRectifiability_Packing_CellHaarPairGeometry`, `RieszRectifiability_Packing_HaarCellMassRatio`, `RieszRectifiability_Packing_HaarTopBallPacking`, `RieszRectifiability_Packing_LatticeMassPacking`, `RieszRectifiability_Packing_NoFlatDescendantPacking`, `RieszRectifiability_Packing_RieszOscillationPacking`, `RieszRectifiability_Packing_UniformSmallScalePacking`, `RieszRectifiability_Projections_FiniteProjectionAveraging`, `RieszRectifiability_Projections_NonemptyAffineProjection`, `RieszRectifiability_Projections_PlaneChangeProjectedMap`, `RieszRectifiability_Projections_ProjectionCells`, `RieszRectifiability_Projections_ProjectionConditionedRegions`, `RieszRectifiability_Projections_ProjectionDiskLift`, `RieszRectifiability_Projections_ProjectionRegionChildAssembly`, `RieszRectifiability_Projections_ProjectionRegionDepthCharts`, `RieszRectifiability_Restart_ActiveCellChildImageMass`, `RieszRectifiability_Restart_ActiveCellFinitePieceAssembly`, `RieszRectifiability_Restart_ActiveCellPieceSelection`, `RieszRectifiability_Restart_ActiveLevelCover`, `RieszRectifiability_Restart_ActiveLevelProjectionMaps`, `RieszRectifiability_Restart_ActiveLevelWeights`, `RieszRectifiability_Restart_ActiveProjectionGlobalLipschitz`, `RieszRectifiability_Restart_ActiveProjectionLocalComparison`, `RieszRectifiability_Restart_ActiveRegionAllRadiusLowerArea`, `RieszRectifiability_Restart_ActiveRegionCells`, `RieszRectifiability_Restart_ActiveRegionLargeRadiusLowerArea`, `RieszRectifiability_Restart_ActiveRegionLargeScaleArea`, `RieszRectifiability_Restart_ActiveRegionLimitModel`, `RieszRectifiability_Restart_ActiveRegionLocalUpperArea`, `RieszRectifiability_Restart_ActiveRegionPositiveLocalLowerArea`, `RieszRectifiability_Restart_ActiveRegionPositiveScaleArea`, `RieszRectifiability_Restart_ActiveRegionSmallRadiusLowerArea`, `RieszRectifiability_Restart_ActiveRegionSmallScaleArea`, `RieszRectifiability_Restart_ActiveRegionStopMassArea`, `RieszRectifiability_Restart_ActiveRegionStoppingScale`, `RieszRectifiability_Restart_ActiveRegionSurfaces`, `RieszRectifiability_Restart_ActiveRegionTransitions`, `RieszRectifiability_Restart_ActiveRegionUniformArea`, `RieszRectifiability_Restart_ActiveRegionZeroLocalArea`, `RieszRectifiability_Restart_ActiveRegionZeroSet`, `RieszRectifiability_Restart_ActiveRegionZeroSetArea`, `RieszRectifiability_Restart_ActiveSurfaceCharts`, `RieszRectifiability_Restart_BadBetaStopping`, `RieszRectifiability_Restart_CappedStoppingDistance`, `RieszRectifiability_Restart_CellRegionStopping`, `RieszRectifiability_Restart_CellRestartPacking`, `RieszRectifiability_Restart_CleanSupportPartition`, `RieszRectifiability_Restart_GoodRegionRestartAssembly`, `RieszRectifiability_Restart_OriginalADRestartCoverage`, `RieszRectifiability_Restart_ProjectionStopShadowMass`, `RieszRectifiability_Restart_RestartChartStepBounds`, `RieszRectifiability_Restart_RestartCoverageInduction`, `RieszRectifiability_Restart_SelectedRestartAssembly`, `RieszRectifiability_Restart_SelectedRestartBallChartData`, `RieszRectifiability_Restart_SelectedRestartTree`, `RieszRectifiability_Rigidity_FiniteFractionalHeightPairing`, `RieszRectifiability_Rigidity_FourierJetMoments`, `RieszRectifiability_Rigidity_FourierPhaseDifference`, `RieszRectifiability_Rigidity_FractionalBilinear`, `RieszRectifiability_Rigidity_FractionalFourierFubini`, `RieszRectifiability_Rigidity_FractionalGradientDomination`, `RieszRectifiability_Rigidity_FractionalSchwartzBounds`, `RieszRectifiability_Rigidity_FractionalSchwartzContinuity`, `RieszRectifiability_Rigidity_FractionalSchwartzKernel`, `RieszRectifiability_Rigidity_FractionalSpatialDecay`, `RieszRectifiability_Rigidity_FractionalSymbolBounds`, `RieszRectifiability_Rigidity_FractionalTestDilation`, `RieszRectifiability_Rigidity_FractionalTruncatedTests`, `RieszRectifiability_Rigidity_FractionalWeightedDecay`, `RieszRectifiability_Rigidity_HeightTemperedDistribution`, `RieszRectifiability_Rigidity_JetMomentPolynomial`, `RieszRectifiability_Rigidity_ReflectionlessAnnularBounds`, `RieszRectifiability_Rigidity_SchwartzJetCoordinates`, `RieszRectifiability_Rigidity_ShrinkingJetSeminorms`, `RieszRectifiability_Rigidity_TemperedHeightWeights`, `RieszRectifiability_Surfaces_BallChartPartialMap`, `RieszRectifiability_Surfaces_FiniteBallChartUnion`, `RieszRectifiability_Surfaces_FiniteChartParameterPacking`, `RieszRectifiability_Surfaces_ImmediateChildChartAssembly`, `RieszRectifiability_Surfaces_NativeCoreAreaFraction`, `RieszRectifiability_Surfaces_NativeSurfaceArea`, `RieszRectifiability_Surfaces_NativeSurfaceRegularity`, `RieszRectifiability_Surfaces_OriginalTopAreaCharges`, `RieszRectifiability_Surfaces_PlaneChartBallArea`, `RieszRectifiability_Surfaces_PlaneDiskLowerArea`, `RieszRectifiability_Surfaces_SurfaceBallCellCover`.
--
--   **Imports.** It imports the published bundle `Def_RieszQuantitative`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ231Rr002`; the statements `OAI.RieszRectifiability.activeRegionSurface_charts`, `OAI.RieszRectifiability.active_region_high_scale_local_ball_area_le`, `OAI.RieszRectifiability.active_region_limit_all_radius_ball_area_ge`, `OAI.RieszRectifiability.active_region_limit_area_le_original_top`, `OAI.RieszRectifiability.active_region_limit_local_ball_area_le`, `OAI.RieszRectifiability.active_region_positive_stopping_scale_local_ball_area_ge`, `OAI.RieszRectifiability.active_surface_successor_input_chart`, `OAI.RieszRectifiability.exists_active_region_high_matched_projection`, `OAI.RieszRectifiability.exists_active_region_limit_model`, `OAI.RieszRectifiability.exists_active_region_low_matched_projection`, `OAI.RieszRectifiability.exists_active_region_positive_matched_projection`, `OAI.RieszRectifiability.exists_common_height_with_fractional_equation`, `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy`, `OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit`, `OAI.RieszRectifiability.exists_dyadic_planar_measure_limit`, `OAI.RieszRectifiability.exists_dyadic_source_excess_limit`, `OAI.RieszRectifiability.exists_global_height_with_local_singular_limits`, `OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart`, `OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation`, `OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass`, `OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative`, `OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation`, `OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass`, `OAI.RieszRectifiability.normal_frame_source_data_on_ball`, `OAI.RieszRectifiability.planar_full_support_of_reflectionless`, `OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit`, `OAI.RieszRectifiability.quantitative_uniform_precision_area_models`, `OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces`, `OAI.RieszRectifiability.represented_fractional_height_ae_affine`, `OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing` and `OAI.RieszRectifiability.source_planar_density_compact_fractional_equation`; the proofs of `OAI.RieszRectifiability.activeRegionSurface_charts`, `OAI.RieszRectifiability.active_region_high_scale_local_ball_area_le`, `OAI.RieszRectifiability.active_region_limit_all_radius_ball_area_ge`, `OAI.RieszRectifiability.active_region_limit_area_le_original_top`, `OAI.RieszRectifiability.active_region_limit_local_ball_area_le`, `OAI.RieszRectifiability.active_region_positive_stopping_scale_local_ball_area_ge`, `OAI.RieszRectifiability.active_surface_successor_input_chart`, `OAI.RieszRectifiability.exists_active_region_high_matched_projection`, `OAI.RieszRectifiability.exists_active_region_limit_model`, `OAI.RieszRectifiability.exists_active_region_low_matched_projection`, `OAI.RieszRectifiability.exists_active_region_positive_matched_projection`, `OAI.RieszRectifiability.exists_common_height_with_fractional_equation`, `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy`, `OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit`, `OAI.RieszRectifiability.exists_dyadic_planar_measure_limit`, `OAI.RieszRectifiability.exists_dyadic_source_excess_limit`, `OAI.RieszRectifiability.exists_global_height_with_local_singular_limits`, `OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart`, `OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation`, `OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass`, `OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative`, `OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation`, `OAI.RieszRectifiability.exists_uniform_no_flat_descendant_total_mass`, `OAI.RieszRectifiability.normal_frame_source_data_on_ball`, `OAI.RieszRectifiability.planar_full_support_of_reflectionless`, `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, `OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit`, `OAI.RieszRectifiability.quantitative_uniform_precision_area_models`, `OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces`, `OAI.RieszRectifiability.represented_fractional_height_ae_affine`, `OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing` and `OAI.RieszRectifiability.source_planar_density_compact_fractional_equation`.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_RieszQuantitative

section
-- module Solutions.OAIQ231_RR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

def ADRegular {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r) ∧
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineGraphPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Function Metric

def affineGraphLinear {n q d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) :
    Ambient n →L[ℝ] Ambient d :=
  L.toContinuousLinearMap + δ • (N.toContinuousLinearMap.comp A)

def affineGraphPlane {n q d : ℕ} (a : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) :
    AffineSubspace ℝ (Ambient d) :=
  AffineSubspace.mk' (a + δ • N b) (affineGraphLinear L N A δ).toLinearMap.range

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffinePlaneCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine plane coordinates

A linear isometric embedding determines an affine plane parametrization and an
adjoint coordinate map. These maps are Lipschitz and recover every parameter on
the plane; their composition also gives a Lipschitz distance-to-plane function.
-/

namespace RieszRectifiability

noncomputable section

open Function WithLp
open scoped NNReal ENNReal

def affinePlaneSection {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (u : Fin n → ℝ) : EuclideanSpace ℝ (Fin d) := a + L (toLp 2 u)

def affinePlaneCoordinates {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  ofLp (L.toContinuousLinearMap.adjoint (x - a))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LeastSquaredExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Least-squared approximation by affine planes

The squared excess minimizes the radius-normalized quadratic distance over affine planes
of the prescribed dimension. Local finiteness ensures that these distance integrals exist
on balls.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

def IsAffineNPlane {d : ℕ} (n : ℕ) (S : AffineSubspace ℝ (Ambient d)) : Prop :=
  (S : Set (Ambient d)).Nonempty ∧ Module.finrank ℝ S.direction = n

def quadraticPlaneError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (S : AffineSubspace ℝ (Ambient d)) : ℝ :=
  (r ^ (n + 2))⁻¹ * ∫ x in ball a r, infDist x (S : Set (Ambient d)) ^ 2 ∂μ

def squaredExcess {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ S : AffineSubspace ℝ (Ambient d),
    IsAffineNPlane n S ∧ t = quadraticPlaneError n μ a r S}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedNormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric

def tangentPlaneProjection {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (x : Ambient d) : Ambient d :=
  a + L (L.toContinuousLinearMap.adjoint (x - a))

def normalizedNormalHeight {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (x : Ambient d) : Ambient q :=
  δ⁻¹ • N.toContinuousLinearMap.adjoint (x - a)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def GlobalUpperGrowth {d : ℕ} (n : ℕ) (C : ℝ) (μ : Measure (Ambient d)) : Prop :=
  0 ≤ C ∧ ∀ x : Ambient d, ∀ r : ℝ, 0 < r →
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

def inverseDistancePow {d : ℕ} (p : ℕ) (x y : Ambient d) : ℝ :=
  (dist x y ^ p)⁻¹

theorem inverseDistancePow_measurable {d : ℕ} (p : ℕ) (x : Ambient d) :
    Measurable (inverseDistancePow p x) := by
  unfold inverseDistancePow
  fun_prop

theorem inverseDistancePow_nonneg {d : ℕ} (p : ℕ) (x y : Ambient d) :
    0 ≤ inverseDistancePow p x y := by
  unfold inverseDistancePow
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineTubeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def affineTube {d : ℕ} (S : AffineSubspace ℝ (Ambient d)) (R δ : ℝ) : Set (Ambient d) :=
  closedBall 0 R ∩ {x | infDist x (S : Set (Ambient d)) < δ}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology

variable {ι : Type*} [Fintype ι]

def dyadicBoxPartition (I : Box ι) : ℕ → Prepartition I
  | 0 => ⊤
  | k + 1 => (dyadicBoxPartition I k).biUnion Prepartition.splitCenter

def boxWidthBound (I : Box ι) : ℝ := ∑ i, (I.upper i - I.lower i)

def DyadicBoxIndex (I : Box ι) (k : ℕ) := ↥(dyadicBoxPartition I k).boxes

instance instFintypeDyadicBoxIndex (I : Box ι) (k : ℕ) : Fintype (DyadicBoxIndex I k) := by
  classical
  unfold DyadicBoxIndex
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def dyadicBoxCell (I : Box ι) (k : ℕ) (J : DyadicBoxIndex I k) : Set (ι → ℝ) :=
  (J.val : Set (ι → ℝ))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measures on parametrized boxes

Restricting Lebesgue measure to a finite box and pushing it forward through a
parametrization defines the associated box-plane measure. Its finite-measure
packaging allows these parametrized cells to enter weak-convergence arguments.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

def boxPlaneMeasure (I : Box ι) (e : (ι → ℝ) → X) : Measure X :=
  (volume.restrict (I : Set (ι → ℝ))).map e

instance instIsFiniteMeasureBoxPlaneMeasure (I : Box ι) (e : (ι → ℝ) → X) : IsFiniteMeasure (boxPlaneMeasure I e) := by
  let : IsFiniteMeasure (volume.restrict (I : Set (ι → ℝ))) :=
    isFiniteMeasure_restrict.mpr (I.measure_coe_lt_top volume).ne
  unfold boxPlaneMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def boxPlaneFiniteMeasure (I : Box ι) (e : (ι → ℝ) → X) : FiniteMeasure X :=
  ⟨boxPlaneMeasure I e, inferInstance⟩

def dyadicProjectionCell (I : Box ι) (π : X → ι → ℝ) (k : ℕ)
    (J : DyadicBoxIndex I k) : Set X := π ⁻¹' dyadicBoxCell I k J

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_OpenPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Open projection boxes and coordinate-plane measures

Pulling back open boxes along continuous coordinates gives open subsets of the
ambient space. Coordinate-plane measures satisfy upper growth bounds, which
in turn imply finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

def coordinatePlaneMeasure {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) : Measure (Ambient d) := volume.map e

def openProjectionBox {ι X : Type*} (I : Box ι) (π : X → ι → ℝ) : Set X :=
  π ⁻¹' Box.Ioo I

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

def meanCorrection (μ : Measure X) (φ η : X → ℝ) : X → ℝ :=
  fun x => φ x - ((∫ y, φ y ∂μ) / (∫ y, η y ∂μ)) * η x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

def cellMean (μ : Measure X) (w : X → ℝ) : ℝ :=
  (∫ x, w x ∂μ) / μ.real univ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

variable [MetricSpace X]

def fractionalPairEnergy (m : ℕ) (w : X → ℝ) (x y : X) : ℝ :=
  (w x - w y) ^ 2 / dist x y ^ (m + 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PartitionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def partitionMean (μ : Measure X) (s : ι → Set X) (w : X → ℝ) : X → ℝ := by
  classical
  exact fun x => ∑ i, (s i).indicator (fun _ => cellMean (μ.restrict (s i)) w) x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Moments of finite-step functions

Finite sums of cell indicators reduce first and second moments to weighted cell masses.
For disjoint cells, convergence of the coefficients and masses gives convergence of the
second moments and vanishing squared approximation error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def finiteStep (s : ι → Set X) (a : ι → ℝ) : X → ℝ := by
  classical
  exact fun x => ∑ i, (s i).indicator (fun _ => a i) x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-step functions in L²

Finite-step functions on finite measures belong to L². Products are represented on
intersections of cells, expressing squared distances through cell masses and mixed moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem finiteStep_memLp (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) (a : ι → ℝ) :
    MemLp (finiteStep s a) 2 μ := by
  classical
  exact memLp_finsetSum _ (fun i _ => (memLp_const (a i)).indicator (hs i))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_InnerAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

def innerDyadicAnnulus {d : ℕ} (x : Ambient d) (r : ℝ) (k : ℕ) : Set (Ambient d) :=
  {y | r * (1 / 2 : ℝ) ^ (k + 1) < dist x y ∧ dist x y ≤ r * (1 / 2 : ℝ) ^ k}

theorem innerDyadicAnnulus_measurable {d : ℕ} (x : Ambient d) (r : ℝ) (k : ℕ) :
    MeasurableSet (innerDyadicAnnulus x r k) := by
  exact (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable).inter
    (measurableSet_le (continuous_const.dist continuous_id).measurable measurable_const)

theorem innerDyadicAnnulus_disjoint {d : ℕ} (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    Pairwise (Disjoint on innerDyadicAnnulus x r) := by
  have hsep {k l : ℕ} (hkl : k < l) : Disjoint (innerDyadicAnnulus x r k)
      (innerDyadicAnnulus x r l) := by
    apply Set.disjoint_left.mpr
    intro y hyk hyl
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ (k + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_of_lt hkl)
    have hm := mul_le_mul_of_nonneg_left hp hr.le
    exact (not_lt_of_ge (hyl.2.trans hm)) hyk.1
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hsep h
  · exact (hsep h).symm

theorem iUnion_innerDyadicAnnulus {d : ℕ} (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (⋃ k : ℕ, innerDyadicAnnulus x r k) = closedBall x r \ {x} := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hd : 0 < dist x y := lt_trans (by positivity) hk.1
    refine ⟨?_, ?_⟩
    · have h := hk.2.trans (mul_le_mul_of_nonneg_left hp hr.le)
      simpa only [mem_closedBall, dist_comm, mul_one] using! h
    · simpa only [mem_singleton_iff, ne_eq, eq_comm] using! (dist_pos.mp hd)
  · intro hy
    have hd : 0 < dist x y := dist_pos.mpr (by
      simpa only [mem_singleton_iff, ne_eq, eq_comm] using! hy.2)
    have hdist : dist x y ≤ r := by simpa only [mem_closedBall, dist_comm] using! hy.1
    have hratio : dist x y / r ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using! hdist)
    obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near_of_lt_one (div_pos hd hr) hratio
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
    · simpa only [mul_comm] using! (lt_div_iff₀ hr).mp hk₁
    · simpa only [mul_comm] using! (div_le_iff₀ hr).mp hk₂

theorem innerDyadicAnnulus_subset_ball {d : ℕ} (x : Ambient d) (r : ℝ)
    (hr : 0 < r) (k : ℕ) :
    innerDyadicAnnulus x r k ⊆ ball x (2 * (r * (1 / 2 : ℝ) ^ k)) := by
  intro y hy
  have hp : 0 < r * (1 / 2 : ℝ) ^ k := by positivity
  have ht : dist x y < 2 * (r * (1 / 2 : ℝ) ^ k) := by linarith [hy.2]
  simpa only [mem_ball, dist_comm] using! ht

theorem inverseDistancePow_bound_on_innerAnnulus {d : ℕ} (p : ℕ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) (k : ℕ)
    (y : Ambient d) (hy : y ∈ innerDyadicAnnulus x r k) :
    ‖inverseDistancePow p x y‖ ≤ ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ := by
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg p x y)]
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos (show 0 < r * (1 / 2 : ℝ) ^ (k + 1) by positivity) p)
      (pow_le_pow_left₀ (by positivity) hy.1.le p)

theorem inverseDistancePow_integrableOn_innerAnnulus {d : ℕ} (n p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    IntegrableOn (inverseDistancePow p x) (innerDyadicAnnulus x r k) μ := by
  have hfinite : μ (innerDyadicAnnulus x r k) < ∞ :=
    ((measure_mono (innerDyadicAnnulus_subset_ball x r hr k)).trans
      (hg.2 x _ (by positivity))).trans_lt ENNReal.ofReal_lt_top
  apply Measure.integrableOn_of_bounded hfinite.ne
    (inverseDistancePow_measurable p x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (innerDyadicAnnulus_measurable x r k)] with y hy
  exact inverseDistancePow_bound_on_innerAnnulus p x r hr k y hy

theorem singleton_null_of_globalGrowth {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ) (x : Ambient d) :
    μ {x} = 0 := by
  have hh : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (C * ((1 / 2 : ℝ) ^ k) ^ (p + 1)))
      atTop (𝓝 0) := by
    simpa using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hh.pow (p + 1)).const_mul C)
  apply le_antisymm _ (zero_le)
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro k
  apply (measure_mono _).trans (hg.2 x _ (by positivity))
  intro y hy
  have hyx : y = x := mem_singleton_iff.mp hy
  subst y
  simpa only [mem_ball, dist_self] using! (show (0 : ℝ) < (1 / 2 : ℝ) ^ k by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Near-field inverse-distance estimates

Inner dyadic annuli turn upper growth of order `p + 1` into a summable bound for
the inverse-distance power of order `p`. The center has zero measure, so the
annular estimates give integrability and a quantitative bound on the closed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

theorem dyadic_near_coefficient (p k : ℕ) (C r : ℝ) (hr : 0 < r) :
    ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ *
      (C * (2 * (r * (1 / 2 : ℝ) ^ k)) ^ (p + 1)) =
      (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k := by
  let b : ℝ := r * (1 / 2 : ℝ) ^ k
  have hb : b ≠ 0 := by dsimp [b] <;> positivity
  have hs : r * (1 / 2 : ℝ) ^ (k + 1) = b / 2 := by
    dsimp [b]
    rw [pow_succ]
    ring
  calc
    _ = (C * 2 ^ (p + 1) * 2 ^ p) * b := by
      rw [hs]
      change ((b / 2) ^ p)⁻¹ * (C * (2 * b) ^ (p + 1)) = _
      rw [div_pow, mul_pow 2 b (p + 1), inv_div, pow_succ b]
      field_simp
    _ = _ := by dsimp [b] <;> ring

theorem inverseDistancePow_inner_annular_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (∫ y in innerDyadicAnnulus x r k, ‖inverseDistancePow p x y‖ ∂μ) ≤
      (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k := by
  have hfinite : μ (innerDyadicAnnulus x r k) < ∞ :=
    ((measure_mono (innerDyadicAnnulus_subset_ball x r hr k)).trans
      (hg.2 x _ (by positivity))).trans_lt ENNReal.ofReal_lt_top
  have hmeasure : μ.real (innerDyadicAnnulus x r k) ≤
      C * (2 * (r * (1 / 2 : ℝ) ^ k)) ^ (p + 1) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (innerDyadicAnnulus_subset_ball x r hr k)).trans
        (hg.2 x _ (by positivity)))
  calc
    _ = ‖∫ y in innerDyadicAnnulus x r k, ‖inverseDistancePow p x y‖ ∂μ‖ :=
      (Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)).symm
    _ ≤ ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ * μ.real (innerDyadicAnnulus x r k) :=
      norm_setIntegral_le_of_norm_le_const hfinite fun y hy => by
        rw [norm_norm]
        exact inverseDistancePow_bound_on_innerAnnulus p x r hr k y hy
    _ ≤ ((r * (1 / 2 : ℝ) ^ (k + 1)) ^ p)⁻¹ *
        (C * (2 * (r * (1 / 2 : ℝ) ^ k)) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left hmeasure (by positivity)
    _ = _ := dyadic_near_coefficient p k C r hr

theorem inverseDistancePow_near_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (inverseDistancePow p x) (closedBall x r) μ ∧
      (∫ y in closedBall x r, ‖inverseDistancePow p x y‖ ∂μ) ≤
        2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in innerDyadicAnnulus x r k, ‖inverseDistancePow p x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun k => inverseDistancePow_inner_annular_bound p C μ hg x r hr k) hgeo
  have hiu : IntegrableOn (inverseDistancePow p x) (⋃ k, innerDyadicAnnulus x r k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_innerAnnulus (p + 1) p C μ hg x r hr k) hs
  have heq : (⋃ k, innerDyadicAnnulus x r k) =ᵐ[μ] closedBall x r := by
    rw [iUnion_innerDyadicAnnulus x r hr]
    exact sdiff_ae_eq_self.mpr
      (measure_mono_null inter_subset_right (singleton_null_of_globalGrowth p C μ hg x))
  refine ⟨(integrableOn_congr_set_ae heq).mp hiu, ?_⟩
  rw [← Measure.restrict_congr_set heq,
    integral_iUnion (innerDyadicAnnulus_measurable x r) (innerDyadicAnnulus_disjoint x r hr) hiu.norm]
  calc
    _ ≤ ∑' k : ℕ, (C * 2 ^ (p + 1) * 2 ^ p * r) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_inner_annular_bound p C μ hg x r hr k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

theorem inverseDistancePow_near_integral_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (∫ y in closedBall x r, inverseDistancePow p x y ∂μ) ≤
      2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  simpa only [Real.norm_of_nonneg (inverseDistancePow_nonneg p x _)] using!
    (inverseDistancePow_near_integrable_and_bound p C μ hg x r hr).2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearPairWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def nearPairSet {d : ℕ} (r : ℝ) : Set (Ambient d × Ambient d) :=
  {q | q.2 ∈ closedBall q.1 r}

def nearPairWeight {d : ℕ} (p : ℕ) (r : ℝ) : Ambient d × Ambient d → ℝ :=
  (nearPairSet r).indicator (fun q => inverseDistancePow p q.1 q.2)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function
open scoped NNReal

variable {d : ℕ}

def fractionalBilinear (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) : ℝ :=
  ((w x - w y) * (ψ x - ψ y)) / dist x y ^ (m + 1)

def weightedDifference (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) : ℝ :=
  (w x - w y) / Real.sqrt (dist x y ^ (m + 1))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CutoffError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted fractional cutoff errors

The cutoff error weights the fractional pair energy at both endpoints. Symmetry of the
near-pair weight supports integrability and bounds for the contribution of nearby pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def cutoffError {d : ℕ} (m : ℕ) (w χ : Ambient d → ℝ) (x y : Ambient d) : ℝ :=
  w x * w y * fractionalPairEnergy m χ x y

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def dyadicAnnulus {d : ℕ} (x : Ambient d) (ε : ℝ) (k : ℕ) : Set (Ambient d) :=
  {y | ε * 2 ^ k ≤ dist x y ∧ dist x y < ε * 2 ^ (k + 1)}

theorem dyadicAnnulus_measurable {d : ℕ} (x : Ambient d) (ε : ℝ) (k : ℕ) :
    MeasurableSet (dyadicAnnulus x ε k) := by
  exact (measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable).inter
    (measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const)

theorem dyadicAnnulus_subset_ball {d : ℕ} (x : Ambient d) (ε : ℝ) (k : ℕ) :
    dyadicAnnulus x ε k ⊆ ball x (ε * 2 ^ (k + 1)) := by
  intro y hy
  simpa only [mem_ball, dist_comm] using! hy.2

theorem exterior_subset_iUnion_dyadicAnnulus {d : ℕ} (x : Ambient d)
    (ε : ℝ) (hε : 0 < ε) :
    {y | ε < dist x y} ⊆ ⋃ k : ℕ, dyadicAnnulus x ε k := by
  intro y hy
  have hratio : 1 ≤ dist x y / ε := (le_div_iff₀ hε).2 (by simpa using! hy.le)
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
  refine mem_iUnion.mpr ⟨k, ?_⟩
  exact ⟨by simpa [mul_comm] using! (le_div_iff₀ hε).mp hk₁,
    by simpa [mul_comm] using! (div_lt_iff₀ hε).mp hk₂⟩

theorem dyadicAnnulus_measure_lt_top {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    μ (dyadicAnnulus x ε k) < ∞ :=
  ((measure_mono (dyadicAnnulus_subset_ball x ε k)).trans
    (hg.2 x _ (by positivity))).trans_lt ENNReal.ofReal_lt_top

theorem inverseDistancePow_bound_on_annulus {d : ℕ} (p : ℕ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (y : Ambient d) (hy : y ∈ dyadicAnnulus x ε k) :
    ‖inverseDistancePow p x y‖ ≤ ((ε * 2 ^ k) ^ p)⁻¹ := by
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg p x y)]
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos (show 0 < ε * 2 ^ k by positivity) p)
      (pow_le_pow_left₀ (show 0 ≤ ε * 2 ^ k by positivity) hy.1 p)

theorem inverseDistancePow_integrableOn_annulus {d : ℕ} (n p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    IntegrableOn (inverseDistancePow p x) (dyadicAnnulus x ε k) μ := by
  apply Measure.integrableOn_of_bounded (dyadicAnnulus_measure_lt_top n C μ hg x ε hε k).ne
    (inverseDistancePow_measurable p x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable x ε k)] with y hy
  exact inverseDistancePow_bound_on_annulus p x ε hε k y hy

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem dyadic_tail_coefficient (n k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ((ε * 2 ^ k) ^ (n + 1))⁻¹ * (C * (ε * 2 ^ (k + 1)) ^ n) =
      (C * 2 ^ n / ε) * (1 / 2 : ℝ) ^ k := by
  have hr : ε * (2 : ℝ) ^ k ≠ 0 := by positivity
  calc
    _ = C * 2 ^ n / (ε * 2 ^ k) := by
      rw [show ε * (2 : ℝ) ^ (k + 1) = (ε * 2 ^ k) * 2 by rw [pow_succ]; ring,
        mul_pow, pow_succ]
      field_simp
      simp only [mul_pow, pow_succ]
      ring
    _ = _ := by
      rw [div_pow, one_pow]
      field_simp

theorem inverseDistancePow_annular_integral_bound {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    (∫ y in dyadicAnnulus x ε k, ‖inverseDistancePow (n + 1) x y‖ ∂μ) ≤
      (C * 2 ^ n / ε) * (1 / 2 : ℝ) ^ k := by
  have hfinite := dyadicAnnulus_measure_lt_top n C μ hg x ε hε k
  have hmeasure : μ.real (dyadicAnnulus x ε k) ≤ C * (ε * 2 ^ (k + 1)) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (dyadicAnnulus_subset_ball x ε k)).trans
        (hg.2 x _ (by positivity)))
  calc
    _ = ‖∫ y in dyadicAnnulus x ε k, ‖inverseDistancePow (n + 1) x y‖ ∂μ‖ :=
      (Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)).symm
    _ ≤ ((ε * 2 ^ k) ^ (n + 1))⁻¹ * μ.real (dyadicAnnulus x ε k) :=
      norm_setIntegral_le_of_norm_le_const hfinite fun y hy => by
        rw [norm_norm]
        exact inverseDistancePow_bound_on_annulus (n + 1) x ε hε k y hy
    _ ≤ ((ε * 2 ^ k) ^ (n + 1))⁻¹ * (C * (ε * 2 ^ (k + 1)) ^ n) :=
      mul_le_mul_of_nonneg_left hmeasure (by positivity)
    _ = _ := dyadic_tail_coefficient n k C ε hε

theorem inverseDistancePow_integrableOn_exterior {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (inverseDistancePow (n + 1) x) {y | ε < dist x y} μ := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ n / ε) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus x ε k, ‖inverseDistancePow (n + 1) x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound n C μ hg x ε hε k) hgeo
  exact (integrableOn_iUnion_of_summable_integral_norm
    (fun k => inverseDistancePow_integrableOn_annulus n (n + 1) C μ hg x ε hε k) hs).mono_set
      (exterior_subset_iUnion_dyadicAnnulus x ε hε)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem lipschitz_const_mul_real {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (c : ℝ) :
    LipschitzWith (‖c‖₊ * K) (fun x => c * f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (c * f x) (c * f y) = |c| * dist (f x) (f y) := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    _ ≤ |c| * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (abs_nonneg c)
    _ = ((‖c‖₊ * K : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarKernelDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem inverse_pow_difference_le (q : ℕ) (a b r : ℝ)
    (hr : 0 < r) (ha : r ≤ a) (hb : r ≤ b) :
    |(a ^ (q + 1))⁻¹ - (b ^ (q + 1))⁻¹| ≤
      (q + 1 : ℝ) * |a - b| * (r ^ (q + 2))⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le hr ha
  have hb0 : 0 < b := lt_of_lt_of_le hr hb
  have hInv : |a⁻¹ - b⁻¹| ≤ |a - b| / r ^ 2 := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hr)
    simpa only [pow_two] using! mul_le_mul ha hb hr.le ha0.le
  have hmax : max |a⁻¹| |b⁻¹| ≤ r⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr ha0), abs_of_pos (inv_pos.mpr hb0)]
    exact max_le (by simpa only [one_div] using! one_div_le_one_div_of_le hr ha)
      (by simpa only [one_div] using! one_div_le_one_div_of_le hr hb)
  calc
    _ = |(a⁻¹) ^ (q + 1) - (b⁻¹) ^ (q + 1)| := by rw [inv_pow, inv_pow]
    _ ≤ |a⁻¹ - b⁻¹| * (q + 1 : ℝ) * max |a⁻¹| |b⁻¹| ^ q := by
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using!
        abs_pow_sub_pow_le (a⁻¹) (b⁻¹) (q + 1)
    _ ≤ (|a - b| / r ^ 2) * (q + 1 : ℝ) * (r⁻¹) ^ q := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hInv (by positivity)
      · exact pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax q
      · positivity
      · positivity
    _ = _ := by
      rw [pow_add, inv_pow]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem dyadicAnnulus_disjoint {d : ℕ} (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    Pairwise (Disjoint on dyadicAnnulus x r) := by
  have hsep {k l : ℕ} (hkl : k < l) : Disjoint (dyadicAnnulus x r k) (dyadicAnnulus x r l) := by
    apply Set.disjoint_left.mpr
    intro y hyk hyl
    have hp : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hkl)
    have hm := mul_le_mul_of_nonneg_left hp hr.le
    exact (not_lt_of_ge (hm.trans hyl.1)) hyk.2
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hsep h
  · exact (hsep h).symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ClosedTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def closedExterior {d : ℕ} (a : Ambient d) (R : ℝ) : Set (Ambient d) :=
  {y | R ≤ dist a y}

theorem closedExterior_subset_iUnion_dyadicAnnulus {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    closedExterior a R ⊆ ⋃ k : ℕ, dyadicAnnulus a R k := by
  intro y hy
  have hratio : 1 ≤ dist a y / R := (le_div_iff₀ hR).mpr (by simpa using! hy)
  obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine mem_iUnion.mpr ⟨k, ?_, ?_⟩
  · simpa only [mul_comm] using! (le_div_iff₀ hR).mp hk₁
  · simpa only [mul_comm] using! (div_lt_iff₀ hR).mp hk₂

theorem iUnion_dyadicAnnulus_closedExterior {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    (⋃ k : ℕ, dyadicAnnulus a R k) = closedExterior a R := by
  apply Set.Subset.antisymm _ (closedExterior_subset_iUnion_dyadicAnnulus a R hR)
  intro y hy
  obtain ⟨k, hk⟩ := mem_iUnion.mp hy
  have hlow : R ≤ R * (2 : ℝ) ^ k := by
    simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  exact hlow.trans hk.1

theorem inverseDistancePow_closedExterior_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (inverseDistancePow (m + 1) a) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ) ≤ 2 * (C * 2 ^ m / R) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ m / R) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus a R k, ‖inverseDistancePow (m + 1) a y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound m C μ hg a R hR k) hgeo
  have hiu : IntegrableOn (inverseDistancePow (m + 1) a) (⋃ k, dyadicAnnulus a R k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_annulus m (m + 1) C μ hg a R hR k) hs
  refine ⟨by simpa only [iUnion_dyadicAnnulus_closedExterior a R hR] using! hiu, ?_⟩
  calc
    _ = ∑' k, ∫ y in dyadicAnnulus a R k, ‖inverseDistancePow (m + 1) a y‖ ∂μ := by
      rw [← iUnion_dyadicAnnulus_closedExterior a R hR,
        integral_iUnion (dyadicAnnulus_measurable a R) (dyadicAnnulus_disjoint a R hR) hiu]
      simp only [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    _ ≤ ∑' k : ℕ, (C * 2 ^ m / R) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_annular_integral_bound m C μ hg a R hR k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteShellTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted height bounds on dyadic shells

Square-integrable height bounds on each shell control integrals weighted by
inverse powers of distance. The dyadic coefficient identity expresses these
estimates in the geometric form needed for tail bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def finiteShellRegion {d : ℕ} (a : Ambient d) (R : ℝ) (N : ℕ) : Set (Ambient d) :=
  ⋃ k ∈ Finset.range N, dyadicAnnulus a R k

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RenormalizedFarPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def renormalizedNormalIntegrand {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a : Ambient d) (q : Ambient d × Ambient d) : ℝ :=
  φ q.1 * (w q.1 * inverseDistancePow (m + 1) q.1 q.2 -
    w q.2 * (inverseDistancePow (m + 1) q.1 q.2 - inverseDistancePow (m + 1) a q.2))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalPairingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal cutoff pairings and local energy

The normal pairing splits into a symmetric interaction inside a ball and a
renormalized exterior term. Bounds on the pairing, cutoff moments, and exterior
interaction control the local fractional energy together with its cutoff error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def normalCutoffPairing {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R : ℝ) (w χ : Ambient d → ℝ) : ℝ :=
  let ν := μ.restrict (ball a R)
  (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
    fractionalBilinear m w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂ν.prod ν) +
    ∫ q, renormalizedNormalIntegrand m w (fun x => χ x ^ 2 * w x) a q
      ∂ν.prod (μ.restrict (closedExterior a R))

def normalExteriorEstimate (m : ℕ) (C M H R δ Z : ℝ) : ℝ :=
  2 ^ (m + 1) * ((M * δ ^ 2) * (2 * (C * 2 ^ m / R))) +
    ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * ((M * δ) * Z)

def localCutoffErrorCoefficient (p : ℕ) (C : ℝ) (L : ℝ≥0) (R : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * R)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszPairingIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar Riesz pairings and affine normal heights

Pairing the Riesz kernel with a fixed normal identifies its interior contribution
with the fractional bilinear form. For mean-zero tests, the exterior correction
integrates to zero, identifying the scalar Riesz pairing with the normal cutoff pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def affineNormalHeight {d : ℕ} (e z : Ambient d) (b : ℝ) (x : Ambient d) : ℝ :=
  inner ℝ e (x - z) - b

def rieszInteriorIntegrand {d : ℕ} (m : ℕ) (e : Ambient d) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  inner ℝ e (kernel m q.1 q.2) * (φ q.1 - φ q.2)

def rieszFarIntegrand {d : ℕ} (m : ℕ) (e : Ambient d) (φ : Ambient d → ℝ)
    (a : Ambient d) (q : Ambient d × Ambient d) : ℝ :=
  φ q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)

def rieszScalarPairing {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) : ℝ :=
  let ν := μ.restrict (ball a R)
  (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) +
    ∫ q, rieszFarIntegrand m e φ a q ∂ν.prod (μ.restrict (closedExterior a R))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-measure truncated Riesz pairings

The scalar truncated kernel is measurable and bounded away from its singularity.
Symmetrization expresses finite-measure pairings as interior double integrals,
whose integrability yields convergence as the truncation scale tends to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

def scalarTruncatedKernel {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  if ε < dist q.1 q.2 then inner ℝ e (kernel m q.1 q.2) else 0

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricPairingSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

def rieszRawCrossIntegrand {d : ℕ} (m : ℕ) (e : Ambient d) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ := φ q.1 * inner ℝ e (kernel m q.1 q.2)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_TemperedHeightWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

def polynomialDecay {d : ℕ} (q : ℕ) (x : Ambient d) : ℝ := ((1 + ‖x‖) ^ q)⁻¹

theorem polynomialDecay_measurable {d : ℕ} (q : ℕ) :
    Measurable (polynomialDecay (d := d) q) := by
  unfold polynomialDecay
  fun_prop

theorem polynomialDecay_nonneg {d : ℕ} (q : ℕ) (x : Ambient d) : 0 ≤ polynomialDecay q x := by
  unfold polynomialDecay
  positivity

theorem polynomialDecay_eq_rpow {d : ℕ} (q : ℕ) (x : Ambient d) :
    polynomialDecay q x = (1 + ‖x‖) ^ (-(q : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_HeightTemperedDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tempered distributions associated with heights

Polynomially weighted integrability makes the positive and negative height
measures temperate. Their difference defines a tempered distribution whose action
on a Schwartz test function is integration against the signed height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal

def positiveHeightMeasure {d : ℕ} (μ : Measure (Ambient d)) (f : Ambient d → ℝ) :
    Measure (Ambient d) := μ.withDensity (fun x => (Real.toNNReal (f x) : ℝ≥0∞))

theorem positive_height_measure_temperate {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ) :
    (positiveHeightMeasure μ f).HasTemperateGrowth := by
  have hg : Measurable (fun x => Real.toNNReal (f x)) := hf.real_toNNReal
  have hi : Integrable (fun x => (Real.toNNReal (f x) : ℝ) * polynomialDecay q x) μ := by
    apply hweight.mono'
      (((NNReal.continuous_coe.measurable.comp hg).mul (polynomialDecay_measurable q)).aestronglyMeasurable)
    apply Eventually.of_forall
    intro x
    change ‖(Real.toNNReal (f x) : ℝ) * polynomialDecay q x‖ ≤ |f x| * polynomialDecay q x
    rw [Real.norm_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (polynomialDecay_nonneg q x))]
    exact mul_le_mul_of_nonneg_right (Real.coe_toNNReal_le _) (polynomialDecay_nonneg q x)
  refine ⟨⟨q, ?_⟩⟩
  change Integrable (fun x => (1 + ‖x‖) ^ (-(q : ℝ)))
    (μ.withDensity (fun x => (Real.toNNReal (f x) : ℝ≥0∞)))
  apply (integrable_withDensity_iff_integrable_coe_smul hg).mpr
  simpa only [smul_eq_mul, ← polynomialDecay_eq_rpow] using! hi

def heightTemperedDistribution {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ) : 𝓢'(Ambient d, ℂ) := by
  letI := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  letI := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  exact (positiveHeightMeasure μ f).toTemperedDistribution -
    (positiveHeightMeasure μ (fun x => -f x)).toTemperedDistribution

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AmbientAffineHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ambient extensions of affine plane heights

The adjoint of a linear isometric embedding extends an affine height from plane
coordinates to the ambient space. Its operator norms give a Lipschitz bound,
and the pullback identity transfers almost-everywhere affine agreement to the
coordinate plane measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

def ambientAffineHeight {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : ℝ) (M : Ambient n →L[ℝ] ℝ)
    (x : Ambient d) : ℝ := c + M (L.toContinuousLinearMap.adjoint (x - a))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AssembledAffineHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Assembling affine height coordinates

Coordinatewise continuous linear maps assemble into a Euclidean-valued map. Their affine
extensions give an ambient vector-valued affine map, whose Lipschitz constant is bounded by the
operator norm of its linear part.
-/

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

def assembleCoordinateLinear {n q : ℕ} (M : Fin q → Ambient n →L[ℝ] ℝ) :
    Ambient n →L[ℝ] Ambient q :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi M)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PlanarPullbackMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def planarPullbackMeasure {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) : Measure (Ambient n) := ν.map L.toContinuousLinearMap.adjoint

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BlowupMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rescaled measures and their growth bounds

The blowup at a center and positive scale pushes a measure forward by translation
and dilation, then normalizes by the scale to the power `n`. Exact ball formulas
transport the support and preserve global upper and lower growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def blowupMeasure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) : Measure (Ambient d) :=
  ENNReal.ofReal ((r ^ n)⁻¹) • μ.map (fun y => r⁻¹ • (y - a))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak convergence on continuity sets

Weak convergence of finite measures controls the masses of sets with null boundary.
Weighting by bounded continuous nonnegative functions transfers this control to restricted
integrals, providing continuity-set versions of the weak convergence estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

def restrictedFiniteMeasure {d : ℕ} (μ : FiniteMeasure (Ambient d)) (s : Set (Ambient d)) :
    FiniteMeasure (Ambient d) := ⟨(μ : Measure (Ambient d)).restrict s, inferInstance⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction CompactlySupported

def CompactTestConvergence {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) : Prop :=
  ∀ f : C_c(Ambient d, ℝ), Tendsto (fun j => ∫ x, f x ∂μ j) atTop (𝓝 (∫ x, f x ∂ν))

def compactWeightedFiniteMeasure {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) : FiniteMeasure (Ambient d) := by
  refine ⟨μ.withDensity (fun x => (f x : ℝ≥0∞)), ?_⟩
  have hf : Integrable (fun x => (f x : ℝ)) μ :=
    (NNReal.continuous_coe.comp f.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_left (g := ((↑) : ℝ≥0 → ℝ)) rfl)
  simpa only [ENNReal.ofReal_coe_nnreal] using!
    isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral

theorem relativelyCompact_restrict_finite {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (s : Set (Ambient d)) (hc : IsCompact (closure s)) :
    IsFiniteMeasure (μ.restrict s) :=
  isFiniteMeasure_restrict.mpr (ne_of_lt ((measure_mono subset_closure).trans_lt hc.measure_lt_top))

def relativelyCompactFiniteMeasure {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (s : Set (Ambient d)) (hc : IsCompact (closure s)) :
    FiniteMeasure (Ambient d) := ⟨μ.restrict s, relativelyCompact_restrict_finite μ s hc⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BoundedPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

def exhaustionBox (ι : Type*) (H : ℕ) : Box ι where
  lower := fun _ => -((H : ℝ) + 1)
  upper := fun _ => (H : ℝ) + 1
  lower_lt_upper := by
    intro i
    have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    linarith

def planeBoxOuterRadius (K : ℝ≥0) (H : ℕ) : ℝ := ((K : ℝ) + 1) * ((H : ℝ) + 1)

def boundedProjectionRegion {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) : Set (Ambient d) :=
  openProjectionBox (exhaustionBox ι H) π ∩ ball a (planeBoxOuterRadius K H)

theorem boundedProjectionRegion_finite {ι : Type*} {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsFiniteMeasure (μ.restrict (boundedProjectionRegion π a K H)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  apply (measure_mono (show boundedProjectionRegion π a K H ⊆
    closedBall a (planeBoxOuterRadius K H) from fun _ hx => mem_closedBall.mpr hx.2.le)).trans_lt
  exact (isCompact_closedBall a (planeBoxOuterRadius K H)).measure_lt_top

def boundedProjectionFiniteMeasure {ι : Type*} {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) : FiniteMeasure (Ambient d) :=
  ⟨μ.restrict (boundedProjectionRegion π a K H), boundedProjectionRegion_finite μ π a K H⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedLowerGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def CappedLowerGrowth {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d)) : Prop :=
  ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ H → ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def compactnessWeight {d : ℕ} (n : ℕ) (x : Ambient d) : ℝ :=
  ((1 + ‖x‖) ^ (n + 1))⁻¹

theorem compactnessWeight_pos {d : ℕ} (n : ℕ) (x : Ambient d) : 0 < compactnessWeight n x := by
  dsimp only [compactnessWeight]
  positivity

theorem compactnessWeight_continuous {d : ℕ} (n : ℕ) :
    Continuous (compactnessWeight n : Ambient d → ℝ) :=
  ((continuous_const.add continuous_norm).pow (n + 1)).inv₀ (fun x => by
    change (1 + ‖x‖) ^ (n + 1) ≠ 0
    positivity)

theorem compactnessWeight_le_one {d : ℕ} (n : ℕ) (x : Ambient d) : compactnessWeight n x ≤ 1 := by
  have hp : (1 : ℝ) ≤ (1 + ‖x‖) ^ (n + 1) := one_le_pow₀ (by linarith [norm_nonneg x])
  simpa only [compactnessWeight, one_div, inv_one] using!
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp

theorem compactnessWeight_le_inverseDistance {d : ℕ} (n : ℕ) (x : Ambient d) (hx : x ≠ 0) :
    compactnessWeight n x ≤ inverseDistancePow (n + 1) (0 : Ambient d) x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simpa only [compactnessWeight, inverseDistancePow, dist_zero_left, one_div] using!
    one_div_le_one_div_of_le (pow_pos hn (n + 1))
      (pow_le_pow_left₀ hn.le (by linarith : ‖x‖ ≤ 1 + ‖x‖) (n + 1))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeightIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of the compactness weight

Local finiteness controls the weight on closed balls, while polynomial upper growth controls
its exterior integral. Together these give global integrability and a quantitative mass bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

theorem compactnessWeight_integrableOn_closedBall {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (R : ℝ) :
    IntegrableOn (compactnessWeight n) (closedBall (0 : Ambient d) R) μ := by
  have : IsFiniteMeasure (μ.restrict (closedBall (0 : Ambient d) R)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (isCompact_closedBall (0 : Ambient d) R).measure_lt_top)
  apply (integrable_const (1 : ℝ)).mono' (compactnessWeight_continuous n).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_of_nonneg (compactnessWeight_pos n x).le] using! compactnessWeight_le_one n x)

theorem compactnessWeight_integrableOn_exterior {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (compactnessWeight n) {x | R < dist (0 : Ambient d) x} μ := by
  apply (inverseDistancePow_integrableOn_exterior n C μ hg 0 R hR).mono'
    (compactnessWeight_continuous n).aestronglyMeasurable
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  filter_upwards [ae_restrict_mem (μ := μ) hs] with x hx
  rw [Real.norm_of_nonneg (compactnessWeight_pos n x).le]
  exact compactnessWeight_le_inverseDistance n x (dist_pos.mp (hR.trans hx)).symm

theorem compactnessWeight_integrable {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) : Integrable (compactnessWeight n) μ := by
  have hi := compactnessWeight_integrableOn_closedBall n μ 1
  have ho := compactnessWeight_integrableOn_exterior n μ C hg 1 zero_lt_one
  have heq : {x | (1 : ℝ) < dist (0 : Ambient d) x} = (closedBall (0 : Ambient d) 1)ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  rw [heq] at ho
  have h := hi.union ho
  rw [union_compl_self] at h
  exact integrableOn_univ.mp h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeightedMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite measures obtained from the compactness weight

The positive decaying compactness weight turns a globally growing measure into a finite
measure. Integral formulas give quantitative tail control and transfer a lower mass bound
on the unit ball to a lower bound for the weighted total mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

def compactnessWeightedMeasure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) :
    Measure (Ambient d) := μ.withDensity (fun x => ENNReal.ofReal (compactnessWeight n x))

theorem compactnessWeightedMeasure_apply {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    {s : Set (Ambient d)} (hs : MeasurableSet s)
    (hi : IntegrableOn (compactnessWeight n) s μ) :
    compactnessWeightedMeasure n μ s = ENNReal.ofReal (∫ x in s, compactnessWeight n x ∂μ) := by
  rw [compactnessWeightedMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => (compactnessWeight_pos n x).le))).symm

theorem compactnessWeightedMeasure_finite {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) : IsFiniteMeasure (compactnessWeightedMeasure n μ) := by
  refine ⟨?_⟩
  rw [compactnessWeightedMeasure_apply n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn]
  exact ENNReal.ofReal_lt_top

def compactnessFiniteMeasure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (C : ℝ) (hg : GlobalUpperGrowth n C μ) : FiniteMeasure (Ambient d) :=
  ⟨compactnessWeightedMeasure n μ, compactnessWeightedMeasure_finite n μ C hg⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessUnweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

def compactnessUnweightedMeasure {d : ℕ} (n : ℕ) (ν : Measure (Ambient d)) :
    Measure (Ambient d) := ν.withDensity (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BilateralBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def directedBallDeviation {d : ℕ} (s t : Set (Ambient d)) (a : Ambient d) (r : ℝ) : ℝ :=
  sSup ((fun x => infDist x t) '' (ball a r ∩ s))

def bilateralPlaneError {d : ℕ} (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ)
    (S : AffineSubspace ℝ (Ambient d)) : ℝ :=
  (directedBallDeviation μ.support (S : Set (Ambient d)) a r +
    directedBallDeviation (S : Set (Ambient d)) μ.support a r) / r

def bilateralBeta {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧ t = bilateralPlaneError μ a r S}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BlowupAffineGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

def physicalAffine {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Ambient d ≃ᵃ[ℝ] Ambient d where
  toEquiv :=
    { toFun := fun x => a + r • x
      invFun := fun y => r⁻¹ • (y - a)
      left_inv := by
        intro x
        change r⁻¹ • ((a + r • x) - a) = x
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      right_inv := by
        intro y
        change a + r • (r⁻¹ • (y - a)) = y
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        abel }
  linear := LinearEquiv.smulOfNeZero ℝ (Ambient d) r hr.ne'
  map_vadd' := by
    intro x v
    change a + r • (v + x) = r • v + (a + r • x)
    rw [smul_add]
    abel

def physicalHomeomorph {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Ambient d ≃ₜ Ambient d where
  toEquiv := (physicalAffine a r hr).toEquiv
  continuous_toFun := by change Continuous (fun x => a + r • x); fun_prop
  continuous_invFun := by change Continuous (fun y => r⁻¹ • (y - a)); fun_prop

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_UniformNonflatLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def GlobalBilateralLower {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (ε : ℝ) : Prop :=
  ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r → ε ≤ bilateralBeta n μ a r

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedSupportNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Maximal separated extensions give covering nets. Positive separation also gives discreteness,
countability in separable spaces, and finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

theorem exists_separated_cover_extension {X : Type*} [MetricSpace X]
    (E A : Set X) (r : ℝ) (hr : 0 < r) (hAE : A ⊆ E)
    (hA : A.Pairwise fun x y => r ≤ dist x y) :
    ∃ N : Set X, A ⊆ N ∧ N ⊆ E ∧
      N.Pairwise (fun x y => r ≤ dist x y) ∧ ∀ x ∈ E, ∃ z ∈ N, dist x z < r := by
  let S : Set (Set X) := {N | N ⊆ E ∧ N.Pairwise fun x y => r ≤ dist x y}
  obtain ⟨N, hAN, hm⟩ := zorn_subset_nonempty S (by
    intro C hCS hC _
    refine ⟨⋃₀ C, ⟨sUnion_subset (fun B hB => (hCS hB).1), ?_⟩,
      fun B hB => subset_sUnion_of_mem hB⟩
    exact hC.pairwise_sUnion.mpr (fun B hB => (hCS hB).2)) A ⟨hAE, hA⟩
  refine ⟨N, hAN, hm.1.1, hm.1.2, ?_⟩
  intro x hx
  by_contra hcover
  have hfar : ∀ z ∈ N, r ≤ dist x z := by
    intro z hz
    by_contra h
    exact hcover ⟨z, hz, lt_of_not_ge h⟩
  have hins : insert x N ∈ S := by
    refine ⟨insert_subset hx hm.1.1, ?_⟩
    let : Std.Symm (fun a b : X => r ≤ dist a b) :=
      ⟨fun a b h => by simpa only [dist_comm] using! h⟩
    apply (pairwise_insert_of_symm (r := fun a b : X => r ≤ dist a b)).mpr
    exact ⟨hm.1.2, fun z hz _ => hfar z hz⟩
  have hxN : x ∈ N := (hm.2 hins (subset_insert x N)) (mem_insert x N)
  have hh := hfar x hxN
  rw [dist_self] at hh
  linarith

theorem separated_set_discrete {X : Type*} [MetricSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : IsDiscrete N := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  refine ⟨ball x r, isOpen_ball, ?_⟩
  ext y
  constructor
  · rintro ⟨hyball, hyN⟩
    apply mem_singleton_iff.mpr
    by_contra hyx
    exact (not_lt_of_ge (hsep hyN hx hyx)) hyball
  · intro hy
    rw [mem_singleton_iff.mp hy]
    exact ⟨mem_ball_self hr, hx⟩

theorem separated_set_finite_inter_compact {X : Type*} [MetricSpace X]
    (N K : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) (hK : IsCompact K) :
    (N ∩ K).Finite := by
  have hclosed : IsClosed N := isClosed_of_pairwise_le_dist hr hsep
  have hcompact : IsCompact (N ∩ K) := hK.inter_left hclosed
  exact hcompact.finite (separated_set_discrete (N ∩ K) r hr (hsep.mono inter_subset_left))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PositiveNormalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

def positiveNormalHeight {d : ℕ} (e x : Ambient d) : ℝ := max 0 (inner ℝ e x)

def positiveNormalPotential {d : ℕ} (n : ℕ) (e x : Ambient d) : ℝ :=
  positiveNormalHeight e x / ‖x‖ ^ (n + 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth annular and exterior weights

Differences of smooth ball cutoffs localize functions to annular regions.
Subtracting a cutoff from a finite-measure set indicator gives an exterior
weight with controlled size, square integrability, and distance from the center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def annularSmoothBallCutoff {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    ContDiffBump a := ⟨r, 2 * r, hr, by linarith⟩

def smoothAnnularWeight {d : ℕ} (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (x : Ambient d) : ℝ := annularSmoothBallCutoff a R hR x - annularSmoothBallCutoff a r hr x

def smoothExteriorWeight {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (S : Set (Ambient d)) (x : Ambient d) : ℝ :=
  S.indicator (fun _ => 1) x - annularSmoothBallCutoff a R hR x

theorem annularSmoothBallCutoff_basic {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Measurable (annularSmoothBallCutoff a r hr) ∧
    (∀ x, |annularSmoothBallCutoff a r hr x| ≤ 1) ∧
    (∀ x, dist x a ≤ r → annularSmoothBallCutoff a r hr x = 1) ∧
    (∀ x, 2 * r ≤ dist x a → annularSmoothBallCutoff a r hr x = 0) := by
  refine ⟨((annularSmoothBallCutoff a r hr).contDiff (n := ⊤)).continuous.measurable, ?_, ?_, ?_⟩
  · intro x
    rw [abs_of_nonneg (annularSmoothBallCutoff a r hr).nonneg]
    exact (annularSmoothBallCutoff a r hr).le_one
  · intro x hx
    exact (annularSmoothBallCutoff a r hr).one_of_mem_closedBall hx
  · intro x hx
    exact (annularSmoothBallCutoff a r hr).zero_of_le_dist hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_VectorKernelFarDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def vectorKernelFarConstant (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * 2 ^ (n + 2) + 2 ^ (n + 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ExteriorCellMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Means of exterior hard-truncated fields

For bounded data supported outside a ball, the far-kernel estimate controls the
directional oscillation of the hard-truncated transform near the ball's center.
Averaging this estimate over a measurable set of finite positive mass gives the
same bound for the difference between its cell mean and the central value.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def exteriorCellMeanConstant (n : ℕ) (G M : ℝ) : ℝ :=
  M * vectorKernelFarConstant n * G * 2 ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SmoothAnnularCellComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def smoothAnnularTransform {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) : Ambient d :=
  ∫ y, smoothAnnularWeight a r R hr hR y • kernel n a y ∂μ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_UniformHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def heightTailLinearCoefficient (m : ℕ) (C B R b : ℝ) (K : ℝ≥0) (W : ℝ) : ℝ :=
  (B / R) / (1 - b / 2) + ((K : ℝ) + W / R) * (2 * (C * 2 ^ m))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def normalizedEnergyCoefficient (p : ℕ) (C M H R A J : ℝ) (L : ℝ≥0) : ℝ :=
  2 * (A + 2 ^ (p + 1 + 1) * (M * (2 * (C * 2 ^ (p + 1) / R))) +
    ((p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2) * H) * (M * J)) +
    localCutoffErrorCoefficient p C L R * M

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_WeightedCentering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

def cutoffMean (ν : Measure X) (u χ : X → ℝ) : ℝ :=
  (∫ x, χ x ^ 2 * u x ∂ν) / (∫ x, χ x ^ 2 ∂ν)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_UncenteredEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Subtracting the cutoff mean reduces an uncentered height test to the normalized energy
estimate. Centered moment and tail bounds determine the resulting quantitative coefficient.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def uncenteredEnergyCoefficient (p : ℕ) (C B M c H R β W A : ℝ) (K L : ℝ≥0) : ℝ :=
  normalizedEnergyCoefficient p C (2 * (1 + M / c) * M) H R A
    (heightTailLinearCoefficient (p + 1) C (2 * (1 + M / c) * B) R β K
      (W + Real.sqrt (M / c))) L

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OuterPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

def outerPairRadius (R : ℝ) (k : ℕ) : ℝ := R + (k : ℝ) + 1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OscillationTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def ScalarOscillationBound {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (A v : ℝ) : Prop :=
  ∀ (e : Ambient d), ‖e‖ ≤ 1 → ∀ φ : Ambient d → ℝ,
    LipschitzWith 1 φ → tsupport φ ⊆ ball a A → (∫ x, φ x ∂μ) = 0 →
      |rieszScalarPairing m μ a (2 * A) e φ| ≤ v

theorem rieszInteriorIntegrand_const_mul {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (c : ℝ) (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e (fun x => c * φ x) q = c * rieszInteriorIntegrand m e φ q := by
  unfold rieszInteriorIntegrand
  ring

theorem rieszFarIntegrand_const_mul {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (a : Ambient d) (c : ℝ) (q : Ambient d × Ambient d) :
    rieszFarIntegrand m e (fun x => c * φ x) a q = c * rieszFarIntegrand m e φ a q := by
  unfold rieszFarIntegrand
  ring

theorem rieszScalarPairing_const_mul {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) (c : ℝ) :
    rieszScalarPairing m μ a R e (fun x => c * φ x) = c * rieszScalarPairing m μ a R e φ := by
  unfold rieszScalarPairing
  dsimp only
  simp_rw [rieszInteriorIntegrand_const_mul, rieszFarIntegrand_const_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function
open scoped NNReal

def cappedInverseDistancePow {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) : ℝ :=
  ((max ε (dist q.1 q.2)) ^ m)⁻¹

theorem cappedInverseDistancePow_nonneg {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) : 0 ≤ cappedInverseDistancePow m ε q := by
  unfold cappedInverseDistancePow
  exact inv_nonneg.mpr (pow_nonneg (le_trans dist_nonneg (le_max_right _ _)) _)

theorem cappedInverseDistancePow_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (q : X × X) :
    |cappedInverseDistancePow m ε q| ≤ (ε ^ m)⁻¹ := by
  rw [abs_of_nonneg (cappedInverseDistancePow_nonneg m ε q)]
  unfold cappedInverseDistancePow
  exact inv_anti₀ (pow_pos hε _) (pow_le_pow_left₀ hε.le (le_max_left _ _) _)

theorem cappedInverseDistancePow_lipschitz {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹))
      (cappedInverseDistancePow (m + 1) ε : X × X → ℝ) := by
  have hmax : LipschitzWith 2 (fun q : X × X => max ε (dist q.1 q.2)) :=
    LipschitzWith.dist.const_max ε
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹)]
  have hd : |max ε (dist q.1 q.2) - max ε (dist r.1 r.2)| ≤ 2 * dist q r := by
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using! hmax.dist_le_mul q r
  calc
    _ ≤ (m + 1 : ℝ) * |max ε (dist q.1 q.2) - max ε (dist r.1 r.2)| * (ε ^ (m + 2))⁻¹ :=
      inverse_pow_difference_le m _ _ ε hε (le_max_left _ _) (le_max_left _ _)
    _ ≤ (m + 1 : ℝ) * (2 * dist q r) * (ε ^ (m + 2))⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
    _ = _ := by ring

def cappedTestKernel {d : ℕ} (m : ℕ) (ε : ℝ) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  (φ q.1 - φ q.2) * cappedInverseDistancePow (m + 1) ε q

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SignedKernelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of signed weighted kernel integrals

Finite step approximations in the second variable reduce weighted product
integrals to sums of weighted moments and cell masses. Integrable absolute
weights and Lipschitz kernel bounds control the approximation error, allowing
convergence of these finite sums to pass to the original kernel integrals.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable [Fintype ι]

def secondVariableStep (s : ι → Set Y) (z : ι → Y) (F : X × Y → ℝ) : X × Y → ℝ :=
  fun q => finiteStep s (fun i => F (q.1, z i)) q.2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def cappedRieszInterior {d : ℕ} (m : ℕ) (ε : ℝ) (e : Ambient d)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) : ℝ :=
  inner ℝ e (q.1 - q.2) * (φ q.1 - φ q.2) * cappedInverseDistancePow (m + 1) ε q

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Capped Riesz kernels

Capping the radial singularity gives a continuous bounded vector kernel agreeing
with the Riesz kernel away from the cap. The scalar difference from hard truncation
is controlled by a symmetric weight supported on close pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

def cappedRieszKernel {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) : Ambient d :=
  cappedInverseDistancePow (m + 1) ε q • (q.1 - q.2)

theorem cappedRieszKernel_continuous {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (cappedRieszKernel (d := d) m ε) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have hc := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  exact hc.smul (continuous_fst.sub continuous_snd)

theorem cappedRieszKernel_eq_kernel {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) (hq : ε ≤ dist q.1 q.2) :
    cappedRieszKernel m ε q = kernel m q.1 q.2 := by
  unfold cappedRieszKernel cappedInverseDistancePow
  rw [max_eq_right hq]
  simp only [kernel, dist_eq_norm]

def scalarCappedRieszKernel {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) : ℝ := inner ℝ e (cappedRieszKernel m ε q)

def closedNearCapWeight {d : ℕ} (m : ℕ) (ε : ℝ) : Ambient d × Ambient d → ℝ :=
  (nearPairSet ε).indicator (fun _ => (ε ^ m)⁻¹)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactSmoothAnnularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported smooth annular kernel tests

Annular cutoffs remove the Riesz singularity and give compact support. Agreement
with a capped kernel proves continuity, so pairing with a fixed normal produces
a compactly supported continuous scalar test for weak limits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped CompactlySupported

def smoothAnnularKernel {d : ℕ} (n : ℕ) (a : Ambient d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (x : Ambient d) : Ambient d :=
  smoothAnnularWeight a r R hr hR x • kernel n a x

theorem smoothAnnularKernel_eq_capped {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (x : Ambient d) :
    smoothAnnularKernel n a r R hr (hr.trans_le hrR) x =
      smoothAnnularWeight a r R hr (hr.trans_le hrR) x • cappedRieszKernel n r (a, x) := by
  by_cases hx : r ≤ dist a x
  · rw [cappedRieszKernel_eq_kernel n r (a, x) hx]
    rfl
  · have hd : dist x a ≤ r := by rw [dist_comm]; exact (lt_of_not_ge hx).le
    have hw : smoothAnnularWeight a r R hr (hr.trans_le hrR) x = 0 := by
      rw [smoothAnnularWeight,
        (annularSmoothBallCutoff_basic a R (hr.trans_le hrR)).2.2.1 x (hd.trans hrR),
        (annularSmoothBallCutoff_basic a r hr).2.2.1 x hd, sub_self]
    simp only [smoothAnnularKernel, hw, zero_smul]

theorem smoothAnnularKernel_continuous {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Continuous (smoothAnnularKernel n a r R hr (hr.trans_le hrR)) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have hw : Continuous (smoothAnnularWeight a r R hr (hr.trans_le hrR)) :=
    (annularSmoothBallCutoff a R (hr.trans_le hrR)).continuous.sub
      (annularSmoothBallCutoff a r hr).continuous
  have hk : Continuous (fun x : Ambient d => cappedRieszKernel n r (a, x)) :=
    (cappedRieszKernel_continuous n r hr).comp (continuous_const.prodMk continuous_id)
  have heq : smoothAnnularKernel n a r R hr (hr.trans_le hrR) =
      fun x => smoothAnnularWeight a r R hr (hr.trans_le hrR) x • cappedRieszKernel n r (a, x) := by
    funext x
    exact smoothAnnularKernel_eq_capped n a r R hr hrR x
  rw [heq]
  exact hw.smul hk

theorem smoothAnnularKernel_hasCompactSupport {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    HasCompactSupport (smoothAnnularKernel n a r R hr hR) := by
  exact ((annularSmoothBallCutoff a R hR).hasCompactSupport.sub
    (annularSmoothBallCutoff a r hr).hasCompactSupport).smul_right

def scalarSmoothAnnularTest {d : ℕ} (n : ℕ) (e a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) : C_c(Ambient d, ℝ) :=
  ⟨⟨fun x => inner ℝ e (smoothAnnularKernel n a r R hr (hr.trans_le hrR) x),
    continuous_const.inner (smoothAnnularKernel_continuous n a r R hr hrR)⟩,
    (smoothAnnularKernel_hasCompactSupport n a r R hr (hr.trans_le hrR)).comp_left
      (g := fun v => inner ℝ e v) (by simp)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_AnnularBoundedTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tangents with global smooth annular bounds

The global smooth annular bound is stable under blowups and compact-test limits.
This stability preserves the bound when extracting a nonzero tangent supported on a
proper hyperplane, so that the dimension-reduction argument can be iterated.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def GlobalSmoothAnnularBound {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (B : ℝ) : Prop :=
  ∀ a ∈ μ.support, ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
    ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ ≤ B

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatAnnularAlternativeEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def HasFlatBallAbove {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap ε : ℝ) : Prop :=
  ∃ a ∈ μ.support, a ∈ U ∧ ∃ r : ℝ, 0 < r ∧ ρ ≤ r ∧ r < cap ∧ bilateralBeta n μ a r < ε

def HasLargeSmoothAnnulusAbove {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap B : ℝ) : Prop :=
  ∃ a ∈ μ.support, a ∈ U ∧ ∃ r R : ℝ, ∃ hr : 0 < r, ∃ hrR : r ≤ R,
    ρ ≤ r ∧ R < cap ∧ B < ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GeometricGramRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem finite_geometric_two_sum_le (s : Finset ℕ) : ∑ k ∈ s, (1 / 2 : ℝ) ^ k ≤ 2 := by
  have h := summable_geometric_two.sum_le_tsum s (fun k _ => by positivity)
  simpa only [tsum_geometric_two] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NestedSeparatedNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

structure SeparatedCover {X : Type*} [MetricSpace X] (E : Set X) (r : ℝ) where
  points : Set X
  subset : points ⊆ E
  separated : points.Pairwise (fun x y => r ≤ dist x y)
  covers : ∀ x ∈ E, ∃ z ∈ points, dist x z < r

def extendSeparatedCover {X : Type*} [MetricSpace X]
    (E A : Set X) (r : ℝ) (hr : 0 < r) (hAE : A ⊆ E)
    (hA : A.Pairwise fun x y => r ≤ dist x y) : SeparatedCover E r :=
  let h := exists_separated_cover_extension E A r hr hAE hA
  { points := h.choose
    subset := h.choose_spec.2.1
    separated := h.choose_spec.2.2.1
    covers := h.choose_spec.2.2.2 }

theorem subset_extendSeparatedCover {X : Type*} [MetricSpace X]
    (E A : Set X) (r : ℝ) (hr : 0 < r) (hAE : A ⊆ E)
    (hA : A.Pairwise fun x y => r ≤ dist x y) :
    A ⊆ (extendSeparatedCover E A r hr hAE hA).points :=
  (exists_separated_cover_extension E A r hr hAE hA).choose_spec.1

def nestedSeparatedCovers {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k) :
    (k : ℕ) → SeparatedCover E (r k)
  | 0 => extendSeparatedCover E ∅ (r 0) (hr 0) (empty_subset _) (pairwise_empty _)
  | k + 1 =>
    let N := nestedSeparatedCovers E r hr hstep k
    extendSeparatedCover E N.points (r (k + 1)) (hr (k + 1)) N.subset
      (N.separated.mono' (fun _ _ h => (hstep k).trans h))

theorem nestedSeparatedCovers_step_subset {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k)
    (k : ℕ) :
    (nestedSeparatedCovers E r hr hstep k).points ⊆
      (nestedSeparatedCovers E r hr hstep (k + 1)).points := by
  exact subset_extendSeparatedCover E _ (r (k + 1)) (hr (k + 1))
    (nestedSeparatedCovers E r hr hstep k).subset
    ((nestedSeparatedCovers E r hr hstep k).separated.mono' (fun _ _ h => (hstep k).trans h))

theorem nestedSeparatedCovers_monotone {X : Type*} [MetricSpace X]
    (E : Set X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hstep : ∀ k, r (k + 1) ≤ r k) :
    Monotone (fun k => (nestedSeparatedCovers E r hr hstep k).points) :=
  monotone_nat_of_le_succ (nestedSeparatedCovers_step_subset E r hr hstep)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedNetParents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The parent map chooses a covering net point, preferring a point within half the separation radius.
Separation makes this preferred choice unique.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def SeparatedCover.parent {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (x : E) : E := by
  classical
  by_cases h : ∃ z ∈ N.points, dist (x : X) z < r / 2
  · exact ⟨h.choose, N.subset h.choose_spec.1⟩
  · exact ⟨(N.covers x x.property).choose, N.subset (N.covers x x.property).choose_spec.1⟩

theorem SeparatedCover.parent_mem {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (x : E) : (N.parent x : X) ∈ N.points := by
  classical
  unfold SeparatedCover.parent
  split_ifs with h
  · exact h.choose_spec.1
  · exact (N.covers x x.property).choose_spec.1

theorem SeparatedCover.parent_dist {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (hr : 0 < r) (x : E) : dist (x : X) (N.parent x : X) < r := by
  classical
  unfold SeparatedCover.parent
  split_ifs with h
  · exact h.choose_spec.2.trans (by linarith)
  · exact (N.covers x x.property).choose_spec.2

theorem SeparatedCover.parent_forced {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (x : E) (z : X) (hz : z ∈ N.points)
    (hxz : dist (x : X) z < r / 2) : (N.parent x : X) = z := by
  classical
  have h : ∃ y ∈ N.points, dist (x : X) y < r / 2 := ⟨z, hz, hxz⟩
  have hp : dist (x : X) (N.parent x : X) < r / 2 := by
    unfold SeparatedCover.parent
    rw [dite_eq_left h]
    exact h.choose_spec.2
  by_contra hne
  have hsep := N.separated (N.parent_mem x) hz hne
  have ht := dist_triangle (N.parent x : X) (x : X) z
  rw [dist_comm (N.parent x : X) (x : X)] at ht
  linarith

theorem SeparatedCover.parent_self {X : Type*} [MetricSpace X] {E : Set X} {r : ℝ}
    (N : SeparatedCover E r) (hr : 0 < r) (x : E) (hx : (x : X) ∈ N.points) :
    N.parent x = x := by
  apply Subtype.ext
  exact N.parent_forced x x hx (by rw [dist_self]; positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetAncestors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

def netAncestor {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) : ℕ → E → E
  | 0, x => x
  | t + 1, x => netAncestor N k t ((N (k + t)).parent x)

theorem netAncestor_zero {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (x : E) : netAncestor N k 0 x = x := rfl

theorem netAncestor_succ {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (x : E) :
    netAncestor N k (t + 1) x = netAncestor N k t ((N (k + t)).parent x) := rfl

theorem netAncestor_add {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k u v : ℕ) (x : E) :
    netAncestor N k (u + v) x = netAncestor N k u (netAncestor N (k + u) v x) := by
  induction v generalizing x with
  | zero => rfl
  | succ v ih =>
      rw [Nat.add_succ, netAncestor_succ, netAncestor_succ, ← Nat.add_assoc, ih]

theorem netAncestor_first_parent {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (x : E) :
    netAncestor N k (t + 1) x = (N k).parent (netAncestor N (k + 1) t x) := by
  rw [show t + 1 = 1 + t by omega, netAncestor_add]
  rfl

theorem netAncestor_mem {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (x : E) :
    (netAncestor N k (t + 1) x : X) ∈ (N k).points := by
  rw [netAncestor_first_parent]
  exact (N k).parent_mem _

theorem netAncestor_self_of_mem {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hr : ∀ k, 0 < r k)
    (hmono : Monotone (fun k => (N k).points)) (k t : ℕ) (x : E)
    (hx : (x : X) ∈ (N k).points) : netAncestor N k t x = x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [netAncestor_succ, (N (k + t)).parent_self (hr (k + t)) x
        (hmono (Nat.le_add_right k t) hx), ih]

theorem netAncestor_dist_le_sum {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hr : ∀ k, 0 < r k)
    (k t : ℕ) (x : E) :
    dist (x : X) (netAncestor N k t x : X) ≤ ∑ j ∈ Finset.range t, r (k + j) := by
  induction t generalizing x with
  | zero => simp only [netAncestor_zero, dist_self, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ t ih =>
      rw [netAncestor_succ, Finset.sum_range_succ]
      have ht := dist_triangle (x : X) ((N (k + t)).parent x : X)
        (netAncestor N k t ((N (k + t)).parent x) : X)
      have hp := (N (k + t)).parent_dist (hr (k + t)) x
      have hi := ih ((N (k + t)).parent x)
      linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_RegularLatticeScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

def latticeRadius (R : ℝ) (k : ℕ) : ℝ := R * (1 / 64 : ℝ) ^ k

theorem latticeRadius_pos (R : ℝ) (hR : 0 < R) (k : ℕ) : 0 < latticeRadius R k := by
  unfold latticeRadius
  positivity

theorem latticeRadius_succ (R : ℝ) (k : ℕ) : latticeRadius R (k + 1) = latticeRadius R k / 64 := by
  unfold latticeRadius
  rw [pow_succ]
  ring

theorem latticeRadius_add (R : ℝ) (k t : ℕ) :
    latticeRadius R (k + t) = latticeRadius R k * (1 / 64 : ℝ) ^ t := by
  simp only [latticeRadius, pow_add, mul_assoc]

theorem latticeRadius_antitone (R : ℝ) (hR : 0 ≤ R) : Antitone (latticeRadius R) := by
  intro k l hkl
  unfold latticeRadius
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl) hR

theorem latticeRadius_tendsto_zero (R : ℝ) : Tendsto (latticeRadius R) atTop (𝓝 0) := by
  simpa only [mul_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
      (by norm_num : (1 / 64 : ℝ) < 1)).const_mul R

theorem latticeRadius_sum_le (R : ℝ) (hR : 0 ≤ R) (k t : ℕ) :
    ∑ j ∈ Finset.range t, latticeRadius R (k + j) ≤ 2 * latticeRadius R k := by
  simp_rw [latticeRadius_add]
  rw [← Finset.mul_sum]
  have hpow : (∑ j ∈ Finset.range t, (1 / 64 : ℝ) ^ j) ≤ 2 :=
    (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (by norm_num) (by norm_num) j)).trans
      (finite_geometric_two_sum_le (Finset.range t))
  have hk : 0 ≤ latticeRadius R k := by unfold latticeRadius; positivity
  simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hpow hk

theorem netAncestor_dist_le_latticeRadius {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x : E) : dist (x : X) (netAncestor N k t x : X) ≤ 2 * latticeRadius R k :=
  (netAncestor_dist_le_sum N (latticeRadius_pos R hR) k t x).trans
    (latticeRadius_sum_le R hR.le k t)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularLatticeScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem exists_annular_lattice_depth (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ t : ℕ, latticeRadius R (k + t) ≤ r / 8 := by
  obtain ⟨t, ht⟩ := ((latticeRadius_tendsto_zero (latticeRadius R k)).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < r / 8))).exists
  refine ⟨t, ?_⟩
  rw [latticeRadius_add]
  exact ht.le

def annularLatticeDepth (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) : ℕ := by
  classical
  exact Nat.find (exists_annular_lattice_depth R k r hr)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ADHoleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
AD lower bounds and global upper growth quantify the density lost to a ball-shaped hole.
Persistent holes at vanishing scales force a measurable set to have zero measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

def ballHoleDensityDefect (n : ℕ) (C G : ℝ) : ℝ := 1 / (C * G * 3 ^ n * 4 ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetAncestorForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netAncestor_forced_near_center {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x z : E) (hz : (z : X) ∈ (N k).points)
    (hxz : dist (x : X) (z : X) < latticeRadius R k / 4) :
    netAncestor N k (t + 1) x = z := by
  rw [netAncestor_first_parent]
  apply Subtype.ext
  apply (N k).parent_forced _ _ hz
  have hb := netAncestor_dist_le_latticeRadius R hR N (k + 1) t x
  rw [latticeRadius_succ] at hb
  have ht := dist_triangle (netAncestor N (k + 1) t x : X) (x : X) (z : X)
  rw [dist_comm (netAncestor N (k + 1) t x : X) (x : X)] at ht
  have hp := latticeRadius_pos R hR k
  linarith

theorem netAncestor_consistent_on_net {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x : E) (hx : (x : X) ∈ (N (k + t)).points) :
    (netAncestor N k t x : X) ∈ (N k).points := by
  cases t with
  | zero => simpa only [Nat.add_zero, netAncestor_zero] using! hx
  | succ t => exact netAncestor_mem N k t x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetDescendantCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

def netDescendants {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : Set X :=
  {x | ∃ t : ℕ, ∃ hx : x ∈ E, x ∈ (N (k + t)).points ∧ netAncestor N k t ⟨x, hx⟩ = z}

def closedNetCell {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : Set X :=
  closure (netDescendants N k z)

theorem center_mem_netDescendants {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E)
    (hz : (z : X) ∈ (N k).points) : (z : X) ∈ netDescendants N k z :=
  ⟨0, z.property, by simpa only [Nat.add_zero] using! hz, rfl⟩

theorem closedNetCell_subset_closedBall {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k : ℕ) (z : E) : closedNetCell N k z ⊆ closedBall (z : X) (2 * latticeRadius R k) := by
  apply isClosed_closedBall.closure_subset_iff.mpr
  rintro x ⟨t, hx, _, ha⟩
  have hb := netAncestor_dist_le_latticeRadius R hR N k t ⟨x, hx⟩
  rw [ha] at hb
  exact hb

theorem netDescendants_nested {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (z w : E)
    (ha : netAncestor N k t w = z) :
    netDescendants N (k + t) w ⊆ netDescendants N k z := by
  rintro x ⟨u, hx, hnet, hanc⟩
  refine ⟨t + u, hx, ?_, ?_⟩
  · exact (congrArg (fun l : ℕ => x ∈ (N l).points) (Nat.add_assoc k t u)).mp hnet
  · rw [netAncestor_add, hanc, ha]

theorem closedNetCell_nested {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (z w : E)
    (ha : netAncestor N k t w = z) : closedNetCell N (k + t) w ⊆ closedNetCell N k z :=
  closure_mono (netDescendants_nested N k t z w ha)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ClosedNetCellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Covering by closed net cells

The geometric decay of lattice radii lets fine net points approximate every point of the
underlying set. Ancestor forcing places relative balls inside their closed cells, while
properness reduces nearby ancestors to finitely many choices and yields a closed-cell cover.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

theorem exists_latticeRadius_tail_lt (R : ℝ) (hR : 0 < R) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, latticeRadius R (k + t + 1) < ε := by
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (latticeRadius_pos R hR (k + 1))) (by norm_num : (1 / 64 : ℝ) < 1)
  refine ⟨t, ?_⟩
  rw [show k + t + 1 = (k + 1) + t by omega, latticeRadius_add]
  simpa only [mul_comm] using! (lt_div_iff₀ (latticeRadius_pos R hR (k + 1))).mp ht

theorem relative_ball_subset_closedNetCell {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k : ℕ) (z : E) (hz : (z : X) ∈ (N k).points) :
    E ∩ ball (z : X) (latticeRadius R k / 8) ⊆ closedNetCell N k z := by
  rintro y ⟨hyE, hyball⟩
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨t, ht⟩ := exists_latticeRadius_tail_lt R hR k ε hε
  obtain ⟨x, hxN, hyx⟩ := (N (k + t + 1)).covers y hyE
  have hxE := (N (k + t + 1)).subset hxN
  have hscale : latticeRadius R (k + t + 1) ≤ latticeRadius R k / 64 := by
    rw [← latticeRadius_succ]
    exact latticeRadius_antitone R hR.le (by omega)
  have hxz : dist x (z : X) < latticeRadius R k / 4 := by
    have hd := dist_triangle x y (z : X)
    rw [dist_comm x y] at hd
    change dist y (z : X) < latticeRadius R k / 8 at hyball
    have hp := latticeRadius_pos R hR k
    linarith
  refine ⟨x, ⟨t + 1, hxE, ?_, netAncestor_forced_near_center R hR N k t ⟨x, hxE⟩ z hz hxz⟩,
    hyx.trans ht⟩
  simpa only [Nat.add_succ] using! hxN

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ConstructedSupportCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def supportLatticeNets {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : SeparatedCover μ.support (latticeRadius R k) :=
  nestedSeparatedCovers μ.support (latticeRadius R) (latticeRadius_pos R hR)
    (fun j => latticeRadius_antitone R hR.le (Nat.le_succ j)) k

def supportLatticeCenter {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : μ.support :=
  ⟨z, (supportLatticeNets μ R hR k).subset z.property⟩

def supportLatticeCell {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : Set (Ambient d) :=
  closedNetCell (supportLatticeNets μ R hR) k (supportLatticeCenter μ R hR k z)

def supportLatticeAncestor {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR (k + t)).points) :
    (supportLatticeNets μ R hR k).points :=
  ⟨netAncestor (supportLatticeNets μ R hR) k t (supportLatticeCenter μ R hR (k + t) z),
    netAncestor_consistent_on_net R (supportLatticeNets μ R hR) k t _ z.property⟩

theorem supportLatticeNets_monotone {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) :
    Monotone (fun k => (supportLatticeNets μ R hR k).points) :=
  nestedSeparatedCovers_monotone μ.support (latticeRadius R) (latticeRadius_pos R hR)
    (fun j => latticeRadius_antitone R hR.le (Nat.le_succ j))

theorem supportLatticeCell_bounds {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8) ⊆ supportLatticeCell μ R hR k z ∧
      supportLatticeCell μ R hR k z ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) := by
  constructor
  · exact relative_ball_subset_closedNetCell R hR (supportLatticeNets μ R hR) k
      (supportLatticeCenter μ R hR k z) z.property
  · exact closedNetCell_subset_closedBall R hR (supportLatticeNets μ R hR) k
      (supportLatticeCenter μ R hR k z)

theorem supportLatticeCell_nested {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR (k + t)).points) :
    supportLatticeCell μ R hR (k + t) z ⊆
      supportLatticeCell μ R hR k (supportLatticeAncestor μ R hR k t z) :=
  closedNetCell_nested _ k t _ _ rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetDeepCores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netAncestor_forced_near_net_point {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x z : E) (hx : (x : X) ∈ (N (k + t)).points)
    (hz : (z : X) ∈ (N k).points)
    (hxz : dist (x : X) (z : X) < latticeRadius R k / 4) : netAncestor N k t x = z := by
  cases t with
  | zero =>
      change x = z
      by_contra hne
      have hs := (N k).separated (by simpa only [Nat.add_zero] using! hx) hz
        (fun h => hne (Subtype.ext h))
      have hp := latticeRadius_pos R hR k
      linarith
  | succ t => exact netAncestor_forced_near_center R hR N k t x z hz hxz

theorem netDescendants_arbitrarily_deep {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hr : ∀ k, 0 < r k)
    (hmono : Monotone (fun k => (N k).points)) (k q : ℕ) (z : E) (x : X)
    (hx : x ∈ netDescendants N k z) :
    ∃ t : ℕ, ∃ hxE : x ∈ E,
      x ∈ (N (k + (q + t))).points ∧ netAncestor N k (q + t) ⟨x, hxE⟩ = z := by
  obtain ⟨t, hxE, hxN, ha⟩ := hx
  refine ⟨t, hxE, hmono (by omega) hxN, ?_⟩
  rw [show q + t = t + q by omega, netAncestor_add,
    netAncestor_self_of_mem N hr hmono (k + t) q ⟨x, hxE⟩ hxN]
  exact ha

theorem closedNetCell_avoids_deep_other_core {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (hmono : Monotone (fun k => (N k).points)) (k q : ℕ) (w z : E)
    (hz : (z : X) ∈ (N (k + q)).points) (hne : netAncestor N k q z ≠ w) :
    closedNetCell N k w ⊆ (ball (z : X) (latticeRadius R (k + q) / 4))ᶜ := by
  apply isOpen_ball.isClosed_compl.closure_subset_iff.mpr
  intro x hx hball
  obtain ⟨t, hxE, hxN, ha⟩ := netDescendants_arbitrarily_deep N (latticeRadius_pos R hR)
    hmono k q w x hx
  have hxN' : x ∈ (N ((k + q) + t)).points :=
    (congrArg (fun l : ℕ => x ∈ (N l).points) (Nat.add_assoc k q t)).mpr hxN
  have hf := netAncestor_forced_near_net_point R hR N (k + q) t ⟨x, hxE⟩ z hxN' hz hball
  rw [netAncestor_add, hf] at ha
  exact hne ha

theorem supportLatticeCell_avoids_deep_other_core {d : ℕ}
    (μ : MeasureTheory.Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k q : ℕ)
    (w : (supportLatticeNets μ R hR k).points)
    (z : (supportLatticeNets μ R hR (k + q)).points)
    (hne : supportLatticeAncestor μ R hR k q z ≠ w) :
    supportLatticeCell μ R hR k w ⊆
      (ball (z : Ambient d) (latticeRadius R (k + q) / 4))ᶜ := by
  have hn : netAncestor (supportLatticeNets μ R hR) k q (supportLatticeCenter μ R hR (k + q) z) ≠
      supportLatticeCenter μ R hR k w := by
    intro heq
    apply hne
    apply Subtype.ext
    exact congrArg (fun y : μ.support => (y : Ambient d)) heq
  exact closedNetCell_avoids_deep_other_core R hR (supportLatticeNets μ R hR)
    (supportLatticeNets_monotone μ R hR) k q (supportLatticeCenter μ R hR k w)
    (supportLatticeCenter μ R hR (k + q) z) z.property hn

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellOverlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null overlaps of support lattice cells

The countable union of intersections of distinct closed cells is measurable and avoids
every deep core ball. Upper growth and lower AD bounds turn these holes into nullity;
when a core radius exceeds the support diameter, separation makes the overlap empty.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

def supportLatticeOverlap {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    Set (Ambient d) := by
  classical
  exact ⋃ z : (supportLatticeNets μ R hR k).points, ⋃ w : (supportLatticeNets μ R hR k).points,
    if z = w then ∅ else supportLatticeCell μ R hR k z ∩ supportLatticeCell μ R hR k w

theorem mem_supportLatticeOverlap {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) : x ∈ supportLatticeOverlap μ R hR k ↔
    ∃ z w : (supportLatticeNets μ R hR k).points, z ≠ w ∧
      x ∈ supportLatticeCell μ R hR k z ∧ x ∈ supportLatticeCell μ R hR k w := by
  classical
  simp only [supportLatticeOverlap, mem_iUnion]
  constructor
  · rintro ⟨z, w, hx⟩
    by_cases h : z = w
    · simp only [ite_eq_left h, mem_empty_iff_false] at hx
    · exact ⟨z, w, h, by simpa only [ite_eq_right h] using! hx⟩
  · rintro ⟨z, w, h, hz, hw⟩
    exact ⟨z, w, by simpa only [ite_eq_right h] using! And.intro hz hw⟩

theorem supportLatticeOverlap_disjoint_deep_core {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k q : ℕ) (f : (supportLatticeNets μ R hR (k + q)).points) :
    Disjoint (supportLatticeOverlap μ R hR k) (ball (f : Ambient d) (latticeRadius R (k + q) / 4)) := by
  apply Set.disjoint_left.mpr
  intro x hx hball
  obtain ⟨z, w, hne, hz, hw⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
  by_cases hp : supportLatticeAncestor μ R hR k q f = z
  · have hpw : supportLatticeAncestor μ R hR k q f ≠ w := by simpa only [hp] using! hne
    exact supportLatticeCell_avoids_deep_other_core μ R hR k q w f hpw hw hball
  · exact supportLatticeCell_avoids_deep_other_core μ R hR k q z f hp hz hball

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CleanSupportPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cleaning the support lattice partition

Removing the union of all cell overlaps produces nested, disjoint measurable cells that
cover the support outside one exceptional set. Net centers avoid that set, so cleaning
preserves the closed cells as closures. Under the growth bounds, it also preserves cell
mass and gives a unique cell at every scale almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

def supportLatticeExceptional {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) :
    Set (Ambient d) := ⋃ k : ℕ, supportLatticeOverlap μ R hR k

def cleanSupportCell {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : Set (Ambient d) :=
  supportLatticeCell μ R hR k z \ supportLatticeExceptional μ R hR

theorem cleanSupportCell_disjoint {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) (z w : (supportLatticeNets μ R hR k).points) (hne : z ≠ w) :
    Disjoint (cleanSupportCell μ R hR k z) (cleanSupportCell μ R hR k w) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨hz, hgood⟩ ⟨hw, _⟩
  apply hgood
  exact mem_iUnion.mpr ⟨k, (mem_supportLatticeOverlap μ R hR k x).mpr ⟨z, w, hne, hz, hw⟩⟩

theorem cleanSupportCell_nested {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR (k + t)).points) :
    cleanSupportCell μ R hR (k + t) z ⊆
      cleanSupportCell μ R hR k (supportLatticeAncestor μ R hR k t z) :=
  sdiff_subset_sdiff_left (supportLatticeCell_nested μ R hR k t z)

theorem net_center_not_exceptional {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    (z : Ambient d) ∉ supportLatticeExceptional μ R hR := by
  intro hz
  obtain ⟨l, hl⟩ := mem_iUnion.mp hz
  by_cases hkl : k ≤ l
  · let w : (supportLatticeNets μ R hR (l + 0)).points :=
      ⟨z, supportLatticeNets_monotone μ R hR hkl z.property⟩
    have hd := supportLatticeOverlap_disjoint_deep_core μ R hR l 0 w
    exact Set.disjoint_left.mp hd hl (mem_ball_self (div_pos (latticeRadius_pos R hR (l + 0)) (by norm_num)))
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hkl))
    have hd := supportLatticeOverlap_disjoint_deep_core μ R hR l q z
    exact Set.disjoint_left.mp hd hl (mem_ball_self (div_pos (latticeRadius_pos R hR (l + q)) (by norm_num)))

theorem center_mem_cleanSupportCell {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : (z : Ambient d) ∈ cleanSupportCell μ R hR k z :=
  ⟨subset_closure (center_mem_netDescendants (supportLatticeNets μ R hR) k
    (supportLatticeCenter μ R hR k z) z.property), net_center_not_exceptional μ R hR k z⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteSupportRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def supportDescendantsAt {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k t : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Set (supportLatticeNets μ R hR (k + t)).points :=
  {w | supportLatticeAncestor μ R hR k t w = z}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NormalizedSetIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized indicators weight a measurable set by the reciprocal of its real mass.
Finite set mass gives integrability and L² membership for these averaging functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

def normalizedSetIndicator (μ : Measure X) (A : Set X) : X → ℝ :=
  A.indicator (fun _ => (μ.real A)⁻¹)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CellHaarFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar functions for nested cells

The difference of normalized indicators, scaled by the square root of the smaller cell's
mass, has mean zero. Its squared integral is the complementary mass ratio, and pairing
with an `L²` function recovers the difference of the two cell means.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X]

def cellHaar (μ : Measure X) (A B : Set X) (x : X) : ℝ :=
  Real.sqrt (μ.real A) * (normalizedSetIndicator μ A x - normalizedSetIndicator μ B x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CellHaarPairGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure CellHaarPair {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (I : ℕ) where
  outerOffset : ℕ
  innerOffset : ℕ
  depth_bound : outerOffset + innerOffset ≤ I
  outerCenter : (supportLatticeNets μ R hR (k + outerOffset)).points
  innerCenter : (supportLatticeNets μ R hR (k + outerOffset + innerOffset)).points
  outer_ancestor : supportLatticeAncestor μ R hR k outerOffset outerCenter = z
  inner_ancestor : supportLatticeAncestor μ R hR (k + outerOffset) innerOffset innerCenter = outerCenter

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k I : ℕ}
  {z : (supportLatticeNets μ R hR k).points}

def CellHaarPair.outerCell (P : CellHaarPair μ R hR k z I) : Set (Ambient d) :=
  cleanSupportCell μ R hR (k + P.outerOffset) P.outerCenter

def CellHaarPair.innerCell (P : CellHaarPair μ R hR k z I) : Set (Ambient d) :=
  cleanSupportCell μ R hR (k + P.outerOffset + P.innerOffset) P.innerCenter

def CellHaarPair.test (P : CellHaarPair μ R hR k z I) : Ambient d → ℝ :=
  cellHaar μ P.innerCell P.outerCell

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_LatticeDescendantGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure SupportCellDescendant {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) where
  depth : ℕ
  center : Ambient d
  mem_net : center ∈ (supportLatticeNets μ R hR (k + depth)).points
  ancestor : supportLatticeAncestor μ R hR k depth ⟨center, mem_net⟩ = z

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def SupportCellDescendant.radius (i : SupportCellDescendant μ R hR k z) : ℝ := latticeRadius R (k + i.depth)

def SupportCellDescendant.binaryLevel (i : SupportCellDescendant μ R hR k z) : ℕ := 6 * i.depth + 1

def SupportCellDescendant.cell (i : SupportCellDescendant μ R hR k z) : Set (Ambient d) :=
  cleanSupportCell μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩

theorem SupportCellDescendant.radius_pos (i : SupportCellDescendant μ R hR k z) : 0 < i.radius :=
  latticeRadius_pos R hR (k + i.depth)

theorem SupportCellDescendant.center_mem_support (i : SupportCellDescendant μ R hR k z) : i.center ∈ μ.support :=
  (supportLatticeNets μ R hR (k + i.depth)).subset i.mem_net

theorem SupportCellDescendant.center_dist_top (i : SupportCellDescendant μ R hR k z) :
    dist i.center (z : Ambient d) ≤ 2 * latticeRadius R k := by
  have hm := (center_mem_cleanSupportCell μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).1
  have hp := supportLatticeCell_nested μ R hR k i.depth ⟨i.center, i.mem_net⟩ hm
  rw [i.ancestor] at hp
  exact (supportLatticeCell_bounds μ R hR k z).2 hp

theorem SupportCellDescendant.binary_radius (i : SupportCellDescendant μ R hR k z) :
    i.radius = (2 * latticeRadius R k) * (1 / 2 : ℝ) ^ i.binaryLevel := by
  change latticeRadius R (k + i.depth) = _
  rw [latticeRadius_add]
  change _ = (2 * latticeRadius R k) * (1 / 2 : ℝ) ^ (6 * i.depth + 1)
  rw [pow_succ, pow_mul]
  norm_num
  ring

theorem SupportCellDescendant.scale_eq (i j : SupportCellDescendant μ R hR k z)
    (hij : i.binaryLevel ≤ j.binaryLevel) :
    j.radius = i.radius * (1 / 2 : ℝ) ^ (j.binaryLevel - i.binaryLevel) := by
  rw [i.binary_radius, j.binary_radius]
  simp only [mul_assoc, ← pow_add, Nat.add_sub_of_le hij]

theorem SupportCellDescendant.separated (i j : SupportCellDescendant μ R hR k z)
    (hij : i.binaryLevel = j.binaryLevel) (hne : i ≠ j) :
    (1 / 8 : ℝ) * i.radius + (1 / 8 : ℝ) * j.radius ≤ dist i.center j.center := by
  have ht : i.depth = j.depth := by
    change 6 * i.depth + 1 = 6 * j.depth + 1 at hij
    omega
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  dsimp only at ht
  subst tj
  have hxy : xi ≠ xj := by
    intro heq
    subst xj
    exact hne rfl
  have hs := (supportLatticeNets μ R hR (k + ti)).separated hxi hxj hxy
  change (1 / 8 : ℝ) * latticeRadius R (k + ti) +
    (1 / 8 : ℝ) * latticeRadius R (k + ti) ≤ dist xi xj
  have hp := latticeRadius_pos R hR (k + ti)
  linarith

theorem SupportCellDescendant.core_admissible (i : SupportCellDescendant μ R hR k z)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    AdmissibleRadius μ ((1 / 8 : ℝ) * i.radius) := by
  refine ⟨mul_pos (by norm_num) i.radius_pos, ?_⟩
  have hle := latticeRadius_antitone R hR.le (Nat.le_add_right k i.depth)
  apply (ENNReal.ofReal_le_ofReal (show (1 / 8 : ℝ) * i.radius ≤ latticeRadius R k / 8 by
    change (1 / 8 : ℝ) * latticeRadius R (k + i.depth) ≤ _
    linarith)).trans hcore.2

theorem SupportCellDescendant.cell_subset_top (i : SupportCellDescendant μ R hR k z) :
    i.cell ⊆ cleanSupportCell μ R hR k z := by
  have h := cleanSupportCell_nested μ R hR k i.depth ⟨i.center, i.mem_net⟩
  rw [i.ancestor] at h
  exact h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_LatticeMassPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass bounds for lattice descendants

Each descendant cell is contained in a ball with controlled radius. Global
upper growth therefore bounds its mass by a constant times the corresponding
power of its radius, both in extended and real-valued form.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def latticeMassPackingConstant (n : ℕ) (C G B : ℝ) : ℝ :=
  G * 3 ^ n * B * 2 ^ n * C * 8 ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_BoundaryCellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def annularCellMassConstant (n : ℕ) (C : ℝ) : ℝ := C * (512 * 8 : ℝ) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatCellSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def HasFlatCell {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (A α : ℝ) : Prop :=
  ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
    (∀ x ∈ ball (z : Ambient d) (A * latticeRadius R₀ k), x ∈ μ.support →
      infDist x (S : Set (Ambient d)) ≤ α * latticeRadius R₀ k) ∧
    (∀ x ∈ ball (z : Ambient d) (A * latticeRadius R₀ k), x ∈ S →
      infDist x μ.support ≤ α * latticeRadius R₀ k)

def HasFlatDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (I : ℕ) (A α : ℝ) : Prop :=
  ∃ i : SupportCellDescendant μ R₀ hR₀ k z,
    0 < i.depth ∧ i.depth ≤ I ∧ A * i.radius ≤ latticeRadius R₀ k / 8 ∧
      HasFlatCell n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ A α

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellChainGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.center_mem_cell {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) : i.center ∈ i.cell :=
  center_mem_cleanSupportCell μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ExcessPropagationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

def propagationScale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

def propagationHorizon (j : ℕ) : ℕ := 2 * j + 3

def propagationTestRadius (j : ℕ) : ℝ := 8 * (2 : ℝ) ^ propagationHorizon j

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_JointPlaneGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous approximation by two affine planes

The joint squared-distance error defines a good set close to both planes. Its
continuity gives local integrability, and an integral error bound yields a lower
mass estimate for the good set by controlling the complementary bad set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def jointPlaneFitError {d : ℕ} (S W : AffineSubspace ℝ (Ambient d))
    (x : Ambient d) : ℝ :=
  infDist x (S : Set (Ambient d)) ^ 2 + infDist x (W : Set (Ambient d)) ^ 2

def jointPlaneGoodSet {d : ℕ} (S W : AffineSubspace ℝ (Ambient d))
    (R η : ℝ) : Set (Ambient d) :=
  ball 0 R ∩ {x | jointPlaneFitError S W x < η ^ 2}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NeighboringFitErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def dyadicFitErrorConstant (n : ℕ) (b : ℝ) : ℝ := 2 + 2 * (2 : ℝ) ^ (n + 2) * b ^ 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OrderedSpanConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped BigOperators

def OrderedSpanSeparated {d : ℕ} : (n : ℕ) → (Fin n → Ambient d) → ℝ → Prop
  | 0, _, _ => True
  | n + 1, v, r => OrderedSpanSeparated n (Fin.init v) r ∧
      r ≤ infDist (v (Fin.last n)) (Submodule.span ℝ (range (Fin.init v)) : Set (Ambient d))

def spanConditionConstant (M r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => spanConditionConstant M r n * (1 + M / r) + 1 / r

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedBoxContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

def planeBoxInnerRadius (Q : ℝ≥0) (H : ℕ) : ℝ := ((H : ℝ) + 1) / ((Q : ℝ) + 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalCoordinateTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

def normalDirection {q d : ℕ} (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) : Ambient d :=
  N (EuclideanSpace.basisFun (Fin q) ℝ i)

def normalCoordinate {q d : ℕ} (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (i : Fin q) (x : Ambient d) : ℝ := N.toContinuousLinearMap.adjoint (x - a) i

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedRegionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

def radialUnitCutoff {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) : ℝ :=
  max 0 (min 1 (R + 1 - dist x a))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter
open scoped BoundedContinuousFunction

def scalarCappedTransform {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient d) : ℝ :=
  ∫ y, f y * scalarCappedRieszKernel m e ε (x, y) ∂μ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTestSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

def symmetricScalarCappedTestKernel {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (g : Ambient d → ℝ) (x h : Ambient d) : ℝ :=
  cappedInverseDistancePow (m + 1) ε (0, h) *
    (inner ℝ e h * (g (x + h) - g (x - h)))

def symmetricScalarRieszTestKernel {d : ℕ} (m : ℕ) (e : Ambient d)
    (g : Ambient d → ℝ) (x h : Ambient d) : ℝ :=
  inverseDistancePow (m + 1) 0 h *
    (inner ℝ e h * (g (x + h) - g (x - h)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzSecondDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def symmetricSecondDifference (g : Ambient d → F) (x h : Ambient d) : F :=
  g (x + h) + g (x - h) - (2 : ℝ) • g x

theorem first_order_remainder_of_lipschitz_derivative (g : Ambient d → F)
    (hg : Differentiable ℝ g) (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ g))
    (x h : Ambient d) :
    ‖g (x + h) - g x - fderiv ℝ g x h‖ ≤ (L : ℝ) * ‖h‖ ^ 2 := by
  have hbound : ∀ y ∈ segment ℝ x (x + h),
      ‖fderiv ℝ g y - fderiv ℝ g x‖ ≤ (L : ℝ) * ‖h‖ := by
    intro y hy
    calc
      _ ≤ (L : ℝ) * ‖y - x‖ := hL.norm_sub_le y x
      _ ≤ (L : ℝ) * ‖h‖ := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hy
  have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hg y) hbound (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using! hh

theorem second_difference_of_lipschitz_derivative (g : Ambient d → F)
    (hg : Differentiable ℝ g) (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ g))
    (x h : Ambient d) :
    ‖symmetricSecondDifference g x h‖ ≤ 2 * (L : ℝ) * ‖h‖ ^ 2 := by
  have hp := first_order_remainder_of_lipschitz_derivative g hg L hL x h
  have hm := first_order_remainder_of_lipschitz_derivative g hg L hL x (-h)
  have heq : symmetricSecondDifference g x h =
      (g (x + h) - g x - fderiv ℝ g x h) +
      (g (x + -h) - g x - fderiv ℝ g x (-h)) := by
    simp only [symmetricSecondDifference, map_neg, sub_eq_add_neg, two_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖g (x + h) - g x - fderiv ℝ g x h‖ +
        ‖g (x + -h) - g x - fderiv ℝ g x (-h)‖ := norm_add_le _ _
    _ ≤ (L : ℝ) * ‖h‖ ^ 2 + (L : ℝ) * ‖-h‖ ^ 2 := add_le_add hp hm
    _ = _ := by rw [norm_neg]; ring

theorem schwartz_second_difference_quadratic_bound (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖symmetricSecondDifference g x h‖ ≤
      2 * SchwartzMap.seminorm ℝ 0 0
        (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g)) * ‖h‖ ^ 2 := by
  let Dg := fderivCLM ℝ (Ambient d) F g
  let DDg := fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) Dg
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 DDg, apply_nonneg _ _⟩
  have hL : LipschitzWith L Dg := by
    apply lipschitzWith_of_nnnorm_fderiv_le Dg.differentiable
    intro y
    have hb : ‖fderiv ℝ Dg y‖ ≤ (L : ℝ) := DDg.norm_le_seminorm ℝ y
    exact_mod_cast hb
  exact second_difference_of_lipschitz_derivative g g.differentiable L hL x h

theorem schwartz_second_difference_uniform_bound (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖symmetricSecondDifference g x h‖ ≤ 4 * SchwartzMap.seminorm ℝ 0 0 g := by
  have hp := g.norm_le_seminorm ℝ (x + h)
  have hm := g.norm_le_seminorm ℝ (x - h)
  have hx := g.norm_le_seminorm ℝ x
  calc
    _ ≤ ‖g (x + h) + g (x - h)‖ + ‖(2 : ℝ) • g x‖ := norm_sub_le _ _
    _ ≤ (‖g (x + h)‖ + ‖g (x - h)‖) + ‖(2 : ℝ) • g x‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by rw [norm_smul]; norm_num <;> linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSchwartzKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of fractional Schwartz kernels

Second-difference estimates control the fractional kernel near the origin, while
Schwartz bounds and inverse-distance tails control its exterior integral. Combining
the two regions gives integrability under upper growth and, in particular, for volume.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem volume_global_upper_growth (d : ℕ) :
    GlobalUpperGrowth d ((volume : Measure (Ambient d)) (ball 0 1)).toReal
      (volume : Measure (Ambient d)) := by
  refine ⟨ENNReal.toReal_nonneg, fun x r hr => ?_⟩
  rw [Measure.addHaar_ball_of_pos volume x hr]
  have hf : (volume : Measure (Ambient d)) (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin]
  exact le_of_eq (mul_comm _ _)

def fractionalSchwartzKernel {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g : Ambient d → F) (x h : Ambient d) : F :=
  inverseDistancePow (m + 1) 0 h • symmetricSecondDifference g x h

theorem fractionalSchwartzKernel_near_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℕ) (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖fractionalSchwartzKernel (p + 1) g x h‖ ≤
      (2 * SchwartzMap.seminorm ℝ 0 0
        (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g))) *
          inverseDistancePow p 0 h := by
  have hb := schwartz_second_difference_quadratic_bound g x h
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [inverseDistancePow, dist_self, zero_pow (by omega : p + 1 + 1 ≠ 0),
      inv_zero, zero_mul]
    positivity
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h *
          (2 * SchwartzMap.seminorm ℝ 0 0
            (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g)) * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSchwartzKernel_far_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖fractionalSchwartzKernel m g x h‖ ≤
      (4 * SchwartzMap.seminorm ℝ 0 0 g) * inverseDistancePow (m + 1) 0 h := by
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  calc
    _ ≤ inverseDistancePow (m + 1) 0 h * (4 * SchwartzMap.seminorm ℝ 0 0 g) :=
      mul_le_mul_of_nonneg_left (schwartz_second_difference_uniform_bound g x h)
        (inverseDistancePow_nonneg _ _ _)
    _ = _ := mul_comm _ _

theorem fractionalSchwartzKernel_integrable_of_growth {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, F)) (x : Ambient d) :
    Integrable (fractionalSchwartzKernel (p + 1) g x) μ := by
  have hmeas : AEStronglyMeasurable (fractionalSchwartzKernel (p + 1) g x) μ := by
    apply ((inverseDistancePow_measurable (p + 1 + 1) (0 : Ambient d)).aestronglyMeasurable.smul
      (show Continuous (symmetricSecondDifference g x) from (by
        unfold symmetricSecondDifference
        fun_prop)).aestronglyMeasurable)
  have hnear : IntegrableOn (fractionalSchwartzKernel (p + 1) g x) (closedBall 0 1) μ := by
    have hi := (inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 1 (by norm_num)).1
    apply (hi.const_mul (2 * SchwartzMap.seminorm ℝ 0 0
      (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g)))).mono'
        hmeas.restrict
    exact Filter.Eventually.of_forall (fractionalSchwartzKernel_near_bound p g x)
  have hfar : IntegrableOn (fractionalSchwartzKernel (p + 1) g x) (closedExterior 0 1) μ := by
    have hi := (inverseDistancePow_closedExterior_integrable_and_bound
      (p + 1) C μ hgrowth 0 1 (by norm_num)).1
    apply (hi.const_mul (4 * SchwartzMap.seminorm ℝ 0 0 g)).mono' hmeas.restrict
    exact Filter.Eventually.of_forall (fractionalSchwartzKernel_far_bound (p + 1) g x)
  have hs : closedBall (0 : Ambient d) 1 ∪ closedExterior 0 1 = univ := by
    ext h
    simp only [mem_union, mem_closedBall, dist_zero_right, closedExterior, mem_ofPred_eq,
      dist_zero_left, mem_univ, iff_true]
    exact le_total ‖h‖ 1
  have hi := hnear.union hfar
  rw [hs] at hi
  exact integrableOn_univ.mp hi

theorem fractionalSchwartzKernel_integrable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) : Integrable (fractionalSchwartzKernel (p + 1) g x) :=
  fractionalSchwartzKernel_integrable_of_growth p _ volume (volume_global_upper_growth (p + 1)) g x

def fractionalSchwartzTest (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) : ℂ :=
  (-1 / 2 : ℝ) • ∫ h : Ambient (p + 1), fractionalSchwartzKernel (p + 1) g x h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTestDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def dilatedFractionalKernel {d : ℕ} (m : ℕ) (g : Ambient d → F)
    (x : Ambient d) (t : ℝ) (h : Ambient d) : F :=
  inverseDistancePow (m + 1) 0 h • symmetricSecondDifference g x (t • h)

def dilatedFractionalGradientKernel {d : ℕ} (m : ℕ) (g : Ambient d → F)
    (x : Ambient d) (t : ℝ) (h : Ambient d) : F :=
  inverseDistancePow (m + 1) 0 h •
    (fderiv ℝ g (x + t • h) h - fderiv ℝ g (x - t • h) h)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_ScalarRieszTestLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

def scalarRieszSchwartzTest {d : ℕ} (m : ℕ) (e : Ambient d)
    (g : 𝓢(Ambient d, ℝ)) (x : Ambient d) : ℝ :=
  (-1 / 2 : ℝ) * ∫ h, symmetricScalarRieszTestKernel m e g x h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalGradientDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An integrable dominator for fractional gradients

Schwartz derivative seminorms control the near and far parts separately, with
inverse-distance powers `p` and `p + 2`. In dimension `p + 1` their sum is
integrable and uniformly bounds the dilated gradient kernel for dilation
parameters between one half and two.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def fractionalGradientDominator {d : ℕ} (p : ℕ) (g : 𝓢(Ambient d, F))
    (x h : Ambient d) : ℝ :=
  (4 * SchwartzMap.seminorm ℝ 0 0
    (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g))) *
      (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h +
  (4 * (SchwartzMap.seminorm ℝ 1 0 (fderivCLM ℝ (Ambient d) F g) +
    ‖x‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) F g))) *
      (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_GradientRieszTestIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gradient identities for scalar Riesz tests

Summing directional Schwartz derivatives over an orthonormal basis recovers the
dilated fractional gradient kernel. Integrating this identity and passing to
vanishing capped truncations yields the fractional Schwartz integral with its
factor of negative one half.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set LineDeriv

abbrev scalarSchwartzDerivative {d : ℕ} (g : 𝓢(Ambient d, ℝ))
    (e : Ambient d) : 𝓢(Ambient d, ℝ) := ∂_{e} g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarRieszTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The scalar far Riesz transform

Subtracting the kernel at the localization center gives an integrable far-field
kernel under global upper growth. Quantitative decay bounds yield measurability
and local `L²` control of its scalar integral on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

def scalarFarRieszTransform {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (e a : Ambient d) (R : ℝ) (x : Ambient d) : ℝ :=
  ∫ y in closedExterior a R, inner ℝ e (kernel m x y - kernel m a y) ∂μ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ScalarRieszLocalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform local bounds for scalar Riesz transforms

Near and far inverse-distance kernels give an integrable majorant for symmetric
Schwartz test kernels. Its coefficients depend on Schwartz seminorms and a bound
on the base point, yielding a local bound uniform over positive truncation scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

def scalarRieszLocalDominator {d : ℕ} (p : ℕ) (e : Ambient d)
    (g : 𝓢(Ambient d, ℝ)) (R : ℝ) (h : Ambient d) : ℝ :=
  (2 * ‖e‖ * SchwartzMap.seminorm ℝ 0 0 (fderivCLM ℝ (Ambient d) ℝ g)) *
    (closedBall (0 : Ambient d) 1).indicator (inverseDistancePow p 0) h +
  (4 * ‖e‖ * (SchwartzMap.seminorm ℝ 1 0 g + R * SchwartzMap.seminorm ℝ 0 0 g)) *
    (closedExterior (0 : Ambient d) 1).indicator (inverseDistancePow (p + 2) 0) h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaledBallBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scaled ball bumps give compactly supported Lipschitz cutoffs. A lower ball-mass bound
allows normalization to integral one with an explicit scale-dependent Lipschitz bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def scaledBallBump {d : ℕ} (a : Ambient d) (r : ℝ) (x : Ambient d) : ℝ :=
  max 0 (min 1 (2 - r⁻¹ * dist x a))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedBumpPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

def normalizedBumpPairingBound (p : ℕ) (C c : ℝ) : ℝ :=
  8 * C ^ 2 * 4 ^ (p + 1) * 2 ^ (p + 1) * 2 ^ p / c +
    (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) * C * 2 ^ (p + 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_ReflectionlessAnnularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular bounds from scalar reflectionlessness

Scalar reflectionlessness annihilates localized pairings against mean-zero test
functions. Comparing normalized bumps at two radii bounds centered annular kernel
integrals, first in each scalar direction and then in the ambient Euclidean norm.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

def ScalarReflectionlessAt {d : ℕ} (m : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) : Prop :=
  ∀ (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (H R : ℝ),
    LipschitzWith L φ → 0 ≤ H → 0 < R → 2 * H ≤ R →
    (∀ x, φ x ≠ 0 → dist x a ≤ H) → (∫ x, φ x ∂μ) = 0 →
      rieszScalarPairing m μ a R e φ = 0

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightPairingRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regional height pairings

The height pairing on a set combines the symmetric interior fractional bilinear
integral with a renormalized cross-region term. For affine normal heights and
mean-zero tests on a ball, cancellation of the far contribution identifies this
regional expression with the scalar Riesz pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

def heightRawCrossIntegrand {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  φ q.1 * (w q.1 - w q.2) * inverseDistancePow (m + 1) q.1 q.2

def heightPairingOn {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w φ : Ambient d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
    ∂(μ.restrict s).prod (μ.restrict s)) +
  ∫ q, renormalizedNormalIntegrand m w φ a q ∂(μ.restrict s).prod (μ.restrict sᶜ)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FourierJetMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier jets and Schwartz moments

Iterated directional Fourier derivatives correspond to polynomially weighted
Schwartz functions. Evaluating these derivatives at zero expresses Fourier jets
as integrable moments with the appropriate Fourier normalization factor.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform

def fourierDerivativeFactor : ℂ := -(2 * Real.pi * Complex.I)

def fourierMomentSchwartz {d : ℕ} :
    {n : ℕ} → (Fin n → Ambient d) → 𝓢(Ambient d, ℂ) → 𝓢(Ambient d, ℂ)
  | 0, _, g => g
  | n + 1, m, g => fourierDerivativeFactor •
      smulLeftCLM ℂ (inner ℝ · (m 0)) (fourierMomentSchwartz (n := n) (Fin.tail m) g)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_SchwartzJetCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap LineDeriv
open scoped LineDeriv

abbrev JetCoordinateIndex (d N : ℕ) := Σ i : Fin (N + 1), Fin i.val → Fin d

def schwartzJetCoordinates (d N : ℕ) :
    𝓢(Ambient d, ℂ) →ₗ[ℂ] (JetCoordinateIndex d N → ℂ) :=
  LinearMap.pi fun i => (TemperedDistribution.delta (0 : Ambient d)).toLinearMap.comp
    (iteratedLineDerivOpCLM ℂ 𝓢(Ambient d, ℂ)
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j))).toLinearMap

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_JetMomentPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial pairings for Fourier jets

A finite family of jet coefficients defines a multivariable moment polynomial.
Its pairing with a Schwartz function is integrable and equals the corresponding
linear combination of Fourier derivatives at zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

def jetMomentPolynomial {d N : ℕ} (c : JetCoordinateIndex d N → ℂ) :
    MvPolynomial (Fin d) ℂ :=
  ∑ i, MvPolynomial.C (c i * fourierDerivativeFactor ^ i.1.val) *
    ∏ j, MvPolynomial.X (i.2 j)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExpandingSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Expanding smooth cutoffs

Dilating a fixed bump gives compactly supported smooth cutoffs equal to one on
balls of increasing radius. Composition with linear contractions bounds all
derivatives by Schwartz seminorms and supplies uniform derivative bounds for
the cutoff errors.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

def unitSmoothCutoff (d : ℕ) : ContDiffBump (0 : Ambient d) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def expandingSmoothCutoff (d j : ℕ) (x : Ambient d) : ℝ :=
  unitSmoothCutoff d (((j : ℝ) + 1)⁻¹ • x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShrinkingSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set
open scoped ContDiff

def scaledSmoothCutoff (d : ℕ) (r : ℝ) (x : Ambient d) : ℝ :=
  unitSmoothCutoff d (r⁻¹ • x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_ShrinkingJetSeminorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set Filter Topology
open scoped ContDiff

def jetCutoffCoefficient (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i * 2 ^ (i + 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShrinkingSchwartzLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set Filter Topology
open scoped ContDiff

def shrinkingRadius (j : ℕ) : ℝ := ((j : ℝ) + 2)⁻¹

def shrinkingSchwartzCutoff {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (j : ℕ) : 𝓢(Ambient d, F) :=
  smulLeftCLM F (scaledSmoothCutoff d (shrinkingRadius j)) g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzNormDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Filter Topology Set MeasureTheory
open scoped FourierTransform ContDiff

theorem schwartz_norm_division_smooth {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hzero : (0 : Ambient d) ∉ tsupport g) :
    ContDiff ℝ ∞ (fun x => ‖x‖⁻¹ • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hzero] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy]
    exact smul_zero _
  · exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul (g.contDiffAt ⊤)

def schwartzNormDivision {d : ℕ} (g : 𝓢(Ambient d, ℂ))
    (hcompact : HasCompactSupport g) (hzero : (0 : Ambient d) ∉ tsupport g) :
    𝓢(Ambient d, ℂ) :=
  (hcompact.smul_left (f := fun x => ‖x‖⁻¹)).toSchwartzMap
    (schwartz_norm_division_smooth g hzero)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FourierPhaseDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

def fourierPhase {d : ℕ} (ξ x : Ambient d) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSymbolBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for the fractional symbol

The cosine difference defining the fractional symbol is nonnegative and has quadratic
cancellation near the origin. Combining this local bound with inverse-power decay at
infinity gives integrability under upper growth bounds, in particular for volume.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

def fractionalSymbolKernel {d : ℕ} (m : ℕ) (ξ h : Ambient d) : ℝ :=
  inverseDistancePow (m + 1) 0 h * (1 - Real.cos (2 * Real.pi * inner ℝ ξ h))

def fractionalSymbol (p : ℕ) (ξ : Ambient (p + 1)) : ℝ :=
  ∫ h, fractionalSymbolKernel (p + 1) ξ h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalFourierFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter Function

def fractionalFourierKernel (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (q : Ambient (p + 1) × Ambient (p + 1)) : ℂ :=
  fractionalSymbolKernel (p + 1) q.1 q.2 • (fourierPhase q.1 x * g q.1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_PolynomialLeadingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Leading homogeneous terms under dilation

Along an expanding sequence of positive radii, normalization by the total
degree makes lower-degree powers vanish and preserves the top-degree power.
Applying this limit to the finite homogeneous decomposition of a polynomial
recovers its leading homogeneous component pointwise.
-/

namespace RieszRectifiability

noncomputable section

open Filter Topology

def polynomialExpansionRadius (j : ℕ) : ℝ := (j : ℝ) + 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSchwartzBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Seminorm bounds for the fractional Schwartz kernel

Second-derivative seminorms control the near-origin contribution of the
fractional Schwartz kernel. Growth estimates for inverse powers of distance
bound the exterior contribution in terms of the supremum seminorm.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem schwartz_second_derivative_seminorm_bound {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    SchwartzMap.seminorm ℝ 0 0
      (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] ℂ) (fderivCLM ℝ (Ambient d) ℂ g)) ≤
      SchwartzMap.seminorm ℝ 0 2 g := by
  apply seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
  intro x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, fderivCLM_apply]
  change ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ SchwartzMap.seminorm ℝ 0 2 g
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact g.norm_iteratedFDeriv_le_seminorm ℝ 2 x

theorem fractionalSchwartzKernel_integral_norm_bound {d : ℕ}
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    (∫ h, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      4 * (C * 2 ^ (p + 1) * 2 ^ p) * SchwartzMap.seminorm ℝ 0 2 g +
        8 * (C * 2 ^ (p + 1)) * SchwartzMap.seminorm ℝ 0 0 g := by
  let M := SchwartzMap.seminorm ℝ 0 0
    (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] ℂ) (fderivCLM ℝ (Ambient d) ℂ g))
  let N := SchwartzMap.seminorm ℝ 0 0 g
  have hM : 0 ≤ M := apply_nonneg _ _
  have hN : 0 ≤ N := apply_nonneg _ _
  have hM2 : M ≤ SchwartzMap.seminorm ℝ 0 2 g := schwartz_second_derivative_seminorm_bound g
  have hK := fractionalSchwartzKernel_integrable_of_growth p C μ hgrowth g x
  have hnearK := (inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 1 (by norm_num)).1
  have hnearB := inverseDistancePow_near_integral_bound p C μ hgrowth 0 1 (by norm_num)
  have hnear : (∫ h in ball 0 1, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      4 * (C * 2 ^ (p + 1) * 2 ^ p) * SchwartzMap.seminorm ℝ 0 2 g := by
    calc
      _ ≤ ∫ h in closedBall 0 1, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ :=
        integral_mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) hK.norm.restrict
      _ ≤ ∫ h in closedBall 0 1, (2 * M) * inverseDistancePow p 0 h ∂μ :=
        integral_mono hK.norm.restrict (hnearK.const_mul _) (fractionalSchwartzKernel_near_bound p g x)
      _ = (2 * M) * ∫ h in closedBall 0 1, inverseDistancePow p 0 h ∂μ := integral_const_mul _ _
      _ ≤ (2 * M) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * 1)) :=
        mul_le_mul_of_nonneg_left hnearB (by positivity)
      _ ≤ _ := by nlinarith [hgrowth.1, mul_nonneg hgrowth.1 (by positivity : 0 ≤ (2 : ℝ) ^ (p + 1) * 2 ^ p), hM2]
  obtain ⟨hfarK, hfarB⟩ := inverseDistancePow_closedExterior_integrable_and_bound
    (p + 1) C μ hgrowth 0 1 (by norm_num)
  have hext : (ball (0 : Ambient d) 1)ᶜ = closedExterior 0 1 := by
    ext h
    simp only [mem_compl_iff, mem_ball, closedExterior, mem_ofPred_eq, not_lt, dist_comm h 0]
  have hfar : (∫ h in (ball 0 1)ᶜ, ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      8 * (C * 2 ^ (p + 1)) * SchwartzMap.seminorm ℝ 0 0 g := by
    rw [hext]
    calc
      _ ≤ ∫ h in closedExterior 0 1, (4 * N) * inverseDistancePow (p + 1 + 1) 0 h ∂μ :=
        integral_mono hK.norm.restrict (hfarK.const_mul _) (fractionalSchwartzKernel_far_bound (p + 1) g x)
      _ = (4 * N) * ∫ h in closedExterior 0 1, inverseDistancePow (p + 1 + 1) 0 h ∂μ := integral_const_mul _ _
      _ ≤ (4 * N) * (2 * (C * 2 ^ (p + 1) / 1)) := mul_le_mul_of_nonneg_left hfarB (by positivity)
      _ = _ := by dsimp [N] <;> ring
  rw [← integral_add_compl measurableSet_ball hK.norm]
  exact add_le_add hnear hfar

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSchwartzContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuity of fractional Schwartz tests

The integral defining a fractional Schwartz test respects addition and scalar
multiplication. Uniform seminorm bounds control these tests and support their
continuity under Schwartz approximation.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

theorem fractionalSchwartzTest_add (p : ℕ) (f g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    fractionalSchwartzTest p (f + g) x = fractionalSchwartzTest p f x + fractionalSchwartzTest p g x := by
  have he : fractionalSchwartzKernel (p + 1) (f + g) x =
      fun h => fractionalSchwartzKernel (p + 1) f x h + fractionalSchwartzKernel (p + 1) g x h := by
    funext h
    simp only [fractionalSchwartzKernel, symmetricSecondDifference, _root_.add_apply,
      smul_add, smul_sub]
    abel
  unfold fractionalSchwartzTest
  rw [he, integral_add (fractionalSchwartzKernel_integrable p f x)
    (fractionalSchwartzKernel_integrable p g x)]
  exact smul_add (-1 / 2 : ℝ) (∫ h, fractionalSchwartzKernel (p + 1) f x h)
    (∫ h, fractionalSchwartzKernel (p + 1) g x h)

theorem fractionalSchwartzTest_smul (p : ℕ) (c : ℂ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    fractionalSchwartzTest p (c • g) x = c • fractionalSchwartzTest p g x := by
  have he : fractionalSchwartzKernel (p + 1) (c • g) x =
      fun h => c • fractionalSchwartzKernel (p + 1) g x h := by
    funext h
    simp only [fractionalSchwartzKernel, symmetricSecondDifference, _root_.smul_apply,
      smul_add, smul_sub, smul_comm (2 : ℝ) c, smul_comm (inverseDistancePow _ _ _) c]
  unfold fractionalSchwartzTest
  rw [he, integral_smul, smul_comm]

theorem fractionalSchwartzTest_uniform_bound (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTest p g x‖ ≤
      4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1) * 2 ^ p) *
        SchwartzMap.seminorm ℝ 0 2 g +
      8 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1)) *
        SchwartzMap.seminorm ℝ 0 0 g := by
  have hb := fractionalSchwartzKernel_integral_norm_bound p _ volume
    (volume_global_upper_growth (p + 1)) g x
  have hn := norm_integral_le_integral_norm (μ := (volume : Measure (Ambient (p + 1))))
    (fractionalSchwartzKernel (p + 1) g x)
  unfold fractionalSchwartzTest
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
  norm_num
  nlinarith [norm_nonneg (∫ h, fractionalSchwartzKernel (p + 1) g x h)]

def fractionalSchwartzTestCLM (p : ℕ) (x : Ambient (p + 1)) :
    𝓢(Ambient (p + 1), ℂ) →L[ℂ] ℂ := by
  apply mkCLMtoNormedSpace (fun g => fractionalSchwartzTest p g x)
    (fun f g => fractionalSchwartzTest_add p f g x)
    (fun c g => fractionalSchwartzTest_smul p c g x)
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let A := 4 * (C * 2 ^ (p + 1) * 2 ^ p)
  let B := 8 * (C * 2 ^ (p + 1))
  let s : Finset (ℕ × ℕ) := {(0, 0), (0, 2)}
  refine ⟨s, A + B, by dsimp [A, B, C] <;> positivity, fun g => ?_⟩
  have h0 : SchwartzMap.seminorm ℝ 0 0 g ≤ s.sup (schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) g := by
    exact Seminorm.le_def.mp (Finset.le_sup
      (f := schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) (by simp [s] : (0, 0) ∈ s)) g
  have h2 : SchwartzMap.seminorm ℝ 0 2 g ≤ s.sup (schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) g := by
    exact Seminorm.le_def.mp (Finset.le_sup
      (f := schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) (by simp [s] : (0, 2) ∈ s)) g
  have hA : 0 ≤ A := by dsimp [A, C] <;> positivity
  have hB : 0 ≤ B := by dsimp [B, C] <;> positivity
  calc
    _ ≤ A * SchwartzMap.seminorm ℝ 0 2 g + B * SchwartzMap.seminorm ℝ 0 0 g :=
      fractionalSchwartzTest_uniform_bound p g x
    _ ≤ (A + B) * s.sup (schwartzSeminormFamily ℂ (Ambient (p + 1)) ℂ) g := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hA, mul_le_mul_of_nonneg_left h0 hB]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

def fractionalSchwartzDecaySize (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) : ℝ :=
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) * SchwartzMap.seminorm ℝ (p + 4) 2 g +
    (4 * C * 2 ^ (p + 1) * SchwartzMap.seminorm ℝ (p + 2) 0 g +
      (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2) *
        (∫ y : Ambient (p + 1), ‖y‖ * ‖g y‖))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalWeightedDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

def fractionalSchwartzUniformSize (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) : ℝ :=
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  4 * (C * 2 ^ (p + 1) * 2 ^ p) * SchwartzMap.seminorm ℝ 0 2 g +
    8 * (C * 2 ^ (p + 1)) * SchwartzMap.seminorm ℝ 0 0 g

def fractionalSchwartzWeightedSize (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) : ℝ :=
  2 ^ (p + 3) * (fractionalSchwartzUniformSize p g + fractionalSchwartzDecaySize p g)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GrowthVolumeDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Volume domination from intrinsic upper growth

An upper growth bound in the intrinsic Euclidean dimension implies domination
by Lebesgue measure. The density bound is normalized by the unit-ball volume
and includes the dimensional factor needed for closed-ball comparison.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def intrinsicGrowthDensityBound (n : ℕ) (C : ℝ) : ℝ≥0 :=
  Real.toNNReal (C * 2 ^ n / (volume : Measure (Ambient n)).real (ball 0 1))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_TwoSidedIntrinsicDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two-sided intrinsic densities

Lower ball-growth bounds give a positive multiple of Euclidean volume dominated
by the measure. Together with the upper-growth domination, this produces a
measurable density with pointwise lower and upper bounds by clipping its
Radon–Nikodym derivative without changing the represented measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def intrinsicLowerDensityBound (n : ℕ) (C : ℝ) : ℝ≥0 :=
  Real.toNNReal ((C * (volume : Measure (Ambient n)).real (ball 0 1))⁻¹)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def cappedPairEnergy {d : ℕ} (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  (w q.1 - w q.2) ^ 2 * cappedInverseDistancePow (m + 1) ε q

def cappedWeightedDifference {d : ℕ} (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  Real.sqrt (cappedInverseDistancePow (m + 1) ε q) * (w q.1 - w q.2)

theorem cappedWeightedDifference_memLp {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w : Ambient d → ℝ) (hw : MemLp w 2 μ) :
    MemLp (cappedWeightedDifference m ε w) 2 (μ.prod μ) := by
  have hdiff : MemLp (fun q : Ambient d × Ambient d => w q.1 - w q.2) 2 (μ.prod μ) :=
    (hw.comp_fst μ).sub (hw.comp_snd μ)
  have hcap := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  have hsqrt : Measurable (fun q : Ambient d × Ambient d =>
      Real.sqrt (cappedInverseDistancePow (m + 1) ε q)) := hcap.sqrt.measurable
  apply (hdiff.norm.const_mul (Real.sqrt ((ε ^ (m + 1))⁻¹))).mono'
    (hsqrt.aestronglyMeasurable.mul hdiff.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  change ‖Real.sqrt (cappedInverseDistancePow (m + 1) ε q) * (w q.1 - w q.2)‖ ≤
    Real.sqrt ((ε ^ (m + 1))⁻¹) * ‖w q.1 - w q.2‖
  rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  exact (le_abs_self _).trans (cappedInverseDistancePow_bound (m + 1) ε hε q)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactRieszPairingTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported pairing tails

Global upper growth bounds the integral of a bounded, compactly supported test
function. This gives an explicit constant for the inverse-radius error between
the scalar Riesz pairing and its interior product-measure integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def compactRieszTailConstant (m : ℕ) (C : ℝ) {d : ℕ} (e : Ambient d) (H : ℝ) (B : ℝ≥0) : ℝ :=
  (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
    (‖e‖ * H * ((B : ℝ) * (C * (H + 1) ^ m))) * (2 * (C * 2 ^ m))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OscillationEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fractional height energy from scalar oscillation

A squared cutoff times a centered Lipschitz height is a mean-zero test with an
explicit Lipschitz bound. Scalar Riesz oscillation controls its pairing; combined
with the ball and shell second-moment estimates, this bounds the fractional
pair energy of the rescaled height on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

def centeredHeightTestConstant (M c H W : ℝ) (K L : ℝ≥0) : ℝ≥0 :=
  K + 2 * L * Real.toNNReal (W + Real.sqrt (M / c) + (K : ℝ) * H)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedExteriorPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

def normalizedExteriorBound (m : ℕ) (C B H R b : ℝ) (K : ℝ≥0) (W P : ℝ)
    (ℓ : ℕ) (lastError : ℝ) : ℝ :=
  (2 ^ (m + 1) * (P * (2 * (C * 2 ^ m / R)))) * (1 / 2 : ℝ) ^ ℓ +
    (((m + 1 : ℝ) * 2 ^ (m + 2) * H) * (P * ((B / R) / (1 - b / 2)))) * (b / 2) ^ ℓ +
    (((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
      (P * (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))))) * lastError

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTruncatedTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncated fractional Schwartz tests

Restricting the symmetric second-difference kernel to the closed exterior of a
ball gives measurable tests with uniform bounds in Schwartz seminorms. The
integrable full kernel dominates every truncation, so dominated convergence
recovers the fractional Schwartz test as the truncation radii tend to zero.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

def fractionalSchwartzTruncatedTest (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) : ℂ :=
  (-1 / 2 : ℝ) • (∫ h in closedExterior 0 ε, fractionalSchwartzKernel (p + 1) g x h)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FiniteFractionalHeightPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetrization of finite fractional height pairings

The distance cutoff defines a measurable, bounded kernel invariant under
swapping its two variables. Applying the symmetric height-kernel identity and
rewriting the cutoff as an indicator identifies the bilinear pairing with an
iterated integral over the closed exterior region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

def symmetricFractionalCutoffKernel {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  if ε ≤ dist q.1 q.2 then inverseDistancePow (m + 1) q.1 q.2 else 0

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ComplexHeightPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

def complexHeightInteriorIntegrand {d : ℕ} (m : ℕ) (w : Ambient d → ℝ)
    (g : Ambient d → ℂ) (q : Ambient d × Ambient d) : ℂ :=
  (w q.1 - w q.2) • (inverseDistancePow (m + 1) q.1 q.2 • (g q.1 - g q.2))

def complexRenormalizedNormalIntegrand {d : ℕ} (m : ℕ) (w : Ambient d → ℝ)
    (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) : ℂ :=
  (w q.1 * inverseDistancePow (m + 1) q.1 q.2 -
    w q.2 * (inverseDistancePow (m + 1) q.1 q.2 - inverseDistancePow (m + 1) a q.2)) • g q.1

def complexHeightPairingOn {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ) : ℂ :=
  (1 / 2 : ℝ) • (∫ q, complexHeightInteriorIntegrand m w g q ∂(μ.restrict s).prod (μ.restrict s)) +
    ∫ q, complexRenormalizedNormalIntegrand m w g a q ∂(μ.restrict s).prod (μ.restrict sᶜ)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_UniformBilateralExcessPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bilateral excess propagation

The conclusion combines a squared-excess estimate with bilateral beta smallness.
A contradiction sequence first yields bilateral convergence and then a further
subsequence with vanishing normalized excess, producing one propagation index
that works uniformly for all measures satisfying the stated bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

def ExcessBilateralConclusion {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (r δ ε : ℝ) : Prop :=
  squaredExcess n μ 0 r ≤ δ ^ 2 ∧ bilateralBeta n μ 0 r < ε

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicPropagationRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic descendant radii

The radius at depth `j` is the original radius divided by `2 ^ j`. Rescaling by
another dyadic power either returns to a shallower descendant or passes to a
larger original scale. Positivity and the support-diameter bound ensure that an
admissible dyadic horizon remains admissible for every descendant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def descendantRadius (r : ℝ) (j : ℕ) : ℝ := r / (2 : ℝ) ^ j

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_ADInteractionPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def interactionPackingConstant (n : ℕ) (C G c J : ℝ) : ℝ :=
  (C / c ^ n) * G * (2 * J + c) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicLipschitzFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized dyadic Lipschitz test families

The family packages mean-zero compactly supported tests with dyadic radii, separated
centers, and weights whose squares are the dimensional powers of the radii.
Its support and regularity assumptions give integrability, while global upper growth
gives weighted Gram estimates at both finer and coarser scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

structure DyadicLipschitzFamily (ι : Type*) (n d : ℕ) (μ : Measure (Ambient d)) (c J A : ℝ) where
  center : ι → Ambient d
  radius : ι → ℝ
  weight : ι → ℝ
  level : ι → ℕ
  test : ι → Ambient d → ℝ
  lip : ι → ℝ≥0
  radius_pos : ∀ i, 0 < radius i
  weight_pos : ∀ i, 0 < weight i
  weight_sq : ∀ i, weight i ^ 2 = radius i ^ n
  lipschitz : ∀ i, LipschitzWith (lip i) (test i)
  lip_bound : ∀ i, (lip i : ℝ) ≤ A / (radius i * weight i)
  value_bound : ∀ i x, |test i x| ≤ A / weight i
  support_subset : ∀ i, tsupport (test i) ⊆ ball (center i) (J * radius i)
  mean_zero : ∀ i, (∫ x, test i x ∂μ) = 0
  center_mem : ∀ i, center i ∈ μ.support
  core_admissible : ∀ i, AdmissibleRadius μ (c * radius i)
  scale_eq : ∀ i j, level i ≤ level j → radius j = radius i * (1 / 2 : ℝ) ^ (level j - level i)
  separated : ∀ i j, level i = level j → i ≠ j →
    c * radius i + c * radius j ≤ dist (center i) (center j)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLipschitzAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem lipschitz_amplitude_of_ball_support {d : ℕ} [Nontrivial (Ambient d)]
    (f : Ambient d → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (z : Ambient d) (R : ℝ) (hR : 0 < R)
    (hs : tsupport f ⊆ ball z R) (x : Ambient d) :
    |f x| ≤ 2 * (L : ℝ) * R := by
  obtain ⟨v, hv⟩ := exists_norm_eq (E := Ambient d) hR.le
  let y := z + v
  have hy : dist y z = R := by
    dsimp [y]
    rw [dist_eq_norm]
    simpa only [add_sub_cancel_left] using! hv
  have hyzero : f y = 0 := by
    by_contra hn
    have hh := hs (subset_tsupport f hn)
    change dist y z < R at hh
    rw [hy] at hh
    exact (lt_irrefl R) hh
  by_cases hx : f x = 0
  · rw [hx, abs_zero]
    positivity
  have hxR : dist x z < R := hs (subset_tsupport f hx)
  have hxy : dist x y ≤ 2 * R := by
    have ht := dist_triangle x z y
    rw [dist_comm z y, hy] at ht
    linarith
  have hl := hLip.dist_le_mul x y
  rw [Real.dist_eq, hyzero, sub_zero] at hl
  calc
    _ ≤ (L : ℝ) * dist x y := hl
    _ ≤ (L : ℝ) * (2 * R) := mul_le_mul_of_nonneg_left hxy L.coe_nonneg
    _ = _ := by ring

theorem original_oscillation_test_amplitude {d : ℕ} [Nontrivial (Ambient d)]
    (f : Ambient d → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (z : Ambient d) (r J : ℝ) (hr : 0 < r) (hJ : 0 < J)
    (hL : (L : ℝ) ≤ 1 / r) (hs : tsupport f ⊆ ball z (J * r))
    (x : Ambient d) : |f x| ≤ 2 * J := by
  calc
    _ ≤ 2 * (L : ℝ) * (J * r) :=
      lipschitz_amplitude_of_ball_support f L hLip z (J * r) (mul_pos hJ hr) hs x
    _ ≤ 2 * (1 / r) * (J * r) := by gcongr
    _ = _ := by field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_OriginalDyadicTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

structure DyadicOscillationTests (ι : Type*) (d : ℕ)
    (μ : Measure (Ambient d)) (c J : ℝ) where
  center : ι → Ambient d
  radius : ι → ℝ
  level : ι → ℕ
  test : ι → Ambient d → ℝ
  lip : ι → ℝ≥0
  radius_pos : ∀ i, 0 < radius i
  lipschitz : ∀ i, LipschitzWith (lip i) (test i)
  lip_bound : ∀ i, (lip i : ℝ) ≤ 1 / radius i
  support_subset : ∀ i, tsupport (test i) ⊆ ball (center i) (J * radius i)
  mean_zero : ∀ i, (∫ x, test i x ∂μ) = 0
  center_mem : ∀ i, center i ∈ μ.support
  core_admissible : ∀ i, AdmissibleRadius μ (c * radius i)
  scale_eq : ∀ i j, level i ≤ level j →
    radius j = radius i * (1 / 2 : ℝ) ^ (level j - level i)
  separated : ∀ i j, level i = level j → i ≠ j →
    c * radius i + c * radius j ≤ dist (center i) (center j)

def DyadicOscillationTests.weight {ι : Type*} {d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (i : ι) : ℝ :=
  Real.sqrt (F.radius i ^ n)

theorem DyadicOscillationTests.weight_pos {ι : Type*} {d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (i : ι) : 0 < F.weight n i := by
  exact Real.sqrt_pos.mpr (pow_pos (F.radius_pos i) n)

theorem DyadicOscillationTests.weight_sq {ι : Type*} {d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (i : ι) :
    F.weight n i ^ 2 = F.radius i ^ n :=
  Real.sq_sqrt (pow_nonneg (F.radius_pos i).le n)

theorem DyadicOscillationTests.value_bound {ι : Type*} {d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (hJ : 0 < J) (i : ι) (x : Ambient d) :
    |F.test i x| ≤ 2 * J :=
  original_oscillation_test_amplitude (F.test i) (F.lip i) (F.lipschitz i)
    (F.center i) (F.radius i) J (F.radius_pos i) hJ (F.lip_bound i) (F.support_subset i) x

def DyadicOscillationTests.normalized {ι : Type*} {d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (hJ : 0 < J) :
    DyadicLipschitzFamily ι n d μ c J (2 * J + 1) where
  center := F.center
  radius := F.radius
  weight := F.weight n
  level := F.level
  test := fun i x => (F.weight n i)⁻¹ * F.test i x
  lip := fun i => ‖(F.weight n i)⁻¹‖₊ * F.lip i
  radius_pos := F.radius_pos
  weight_pos := F.weight_pos n
  weight_sq := F.weight_sq n
  lipschitz := fun i => lipschitz_const_mul_real (F.lipschitz i) _
  lip_bound := by
    intro i
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (F.weight_pos n i))]
    calc
      _ ≤ (F.weight n i)⁻¹ * (1 / F.radius i) :=
        mul_le_mul_of_nonneg_left (F.lip_bound i) (inv_nonneg.mpr (F.weight_pos n i).le)
      _ = 1 / (F.radius i * F.weight n i) := by ring
      _ ≤ (2 * J + 1) / (F.radius i * F.weight n i) := by
        exact div_le_div_of_nonneg_right (by linarith)
          (mul_nonneg (F.radius_pos i).le (F.weight_pos n i).le)
  value_bound := by
    intro i x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (F.weight_pos n i))]
    calc
      _ ≤ (F.weight n i)⁻¹ * (2 * J) :=
        mul_le_mul_of_nonneg_left (F.value_bound hJ i x) (inv_nonneg.mpr (F.weight_pos n i).le)
      _ ≤ (F.weight n i)⁻¹ * (2 * J + 1) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (F.weight_pos n i).le)
      _ = _ := by ring
  support_subset := fun i => tsupport_mul_subset_right.trans (F.support_subset i)
  mean_zero := by intro i; rw [integral_const_mul, F.mean_zero i, mul_zero]
  center_mem := F.center_mem
  core_admissible := F.core_admissible
  scale_eq := F.scale_eq
  separated := F.separated

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_OriginalOscillationWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure OriginalOscillationWitness {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r J v : ℝ) where
  direction : Ambient d
  test : Ambient d → ℝ
  lip : ℝ≥0
  direction_bound : ‖direction‖ ≤ 1
  lipschitz : LipschitzWith lip test
  lip_bound : (lip : ℝ) ≤ 1 / r
  support_subset : tsupport test ⊆ ball a (J * r)
  mean_zero : (∫ x, test x ∂μ) = 0
  large_pairing : v * r ^ n < |rieszScalarPairing n μ a (2 * (J * r)) direction test|

theorem exists_original_oscillation_witness {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (a : Ambient d) (r J v : ℝ) (hr : 0 < r)
    (hfail : ¬ ScalarOscillationBound n μ a (J * r) (v * r ^ (n + 1))) :
    Nonempty (OriginalOscillationWitness n μ a r J v) := by
  classical
  unfold ScalarOscillationBound at hfail
  push Not at hfail
  obtain ⟨e, he, φ, hφ, hs, hz, hlarge⟩ := hfail
  refine ⟨{
    direction := e
    test := fun x => r⁻¹ * φ x
    lip := ‖r⁻¹‖₊
    direction_bound := he
    lipschitz := by simpa only [mul_one] using! lipschitz_const_mul_real hφ r⁻¹
    lip_bound := by simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), one_div, le_refl]
    support_subset := tsupport_mul_subset_right.trans hs
    mean_zero := by rw [integral_const_mul, hz, mul_zero]
    large_pairing := ?_
  }⟩
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)]
  have hm := mul_lt_mul_of_pos_left hlarge (inv_pos.mpr hr)
  have hid : r⁻¹ * (v * r ^ (n + 1)) = v * r ^ n := by
    rw [pow_succ]
    field_simp
  simpa only [hid] using! hm

def originalOscillationWitnessOfFailure {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r J v : ℝ) (hr : 0 < r)
    (hfail : ¬ ScalarOscillationBound n μ a (J * r) (v * r ^ (n + 1))) :
    OriginalOscillationWitness n μ a r J v :=
  Classical.choice (exists_original_oscillation_witness n μ a r J v hr hfail)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_BadCellTestFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

abbrev BadSupportDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) :=
  {i : SupportCellDescendant μ R hR k z //
    ¬ ScalarOscillationBound n μ i.center (J * i.radius) (v * i.radius ^ (n + 1))}

def badCellWitness {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) (i : BadSupportDescendant n μ R hR k z J v) :
    OriginalOscillationWitness n μ i.val.center i.val.radius J v :=
  originalOscillationWitnessOfFailure n μ i.val.center i.val.radius J v i.val.radius_pos i.property

def badCellTestFamily {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (J v : ℝ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    DyadicOscillationTests (BadSupportDescendant n μ R hR k z J v) d μ (1 / 8) J where
  center := fun i => i.val.center
  radius := fun i => i.val.radius
  level := fun i => i.val.binaryLevel
  test := fun i => (badCellWitness n μ R hR k z J v i).test
  lip := fun i => (badCellWitness n μ R hR k z J v i).lip
  radius_pos := fun i => i.val.radius_pos
  lipschitz := fun i => (badCellWitness n μ R hR k z J v i).lipschitz
  lip_bound := fun i => (badCellWitness n μ R hR k z J v i).lip_bound
  support_subset := fun i => (badCellWitness n μ R hR k z J v i).support_subset
  mean_zero := fun i => (badCellWitness n μ R hR k z J v i).mean_zero
  center_mem := fun i => i.val.center_mem_support
  core_admissible := fun i => i.val.core_admissible hcore
  scale_eq := fun i j hij => i.val.scale_eq j.val hij
  separated := fun i j hij hne => i.val.separated j.val hij (fun h => hne (Subtype.ext h))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellChainComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.eq_of_common_point_same_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i j : SupportCellDescendant μ R hR k z) (hdepth : i.depth = j.depth)
    (x : Ambient d) (hi : x ∈ i.cell) (hj : x ∈ j.cell) : i = j := by
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  change ti = tj at hdepth
  subst tj
  have heq : (⟨xi, hxi⟩ : (supportLatticeNets μ R hR (k + ti)).points) = ⟨xj, hxj⟩ := by
    by_contra hne
    exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR (k + ti) _ _ hne) hi hj
  have hx : xi = xj := congrArg Subtype.val heq
  subst xj
  rfl

theorem supportLatticeAncestor_eq_of_center_mem {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (w : (supportLatticeNets μ R hR (k + t)).points)
    (hw : (w : Ambient d) ∈ cleanSupportCell μ R hR k z) :
    supportLatticeAncestor μ R hR k t w = z := by
  have ht := cleanSupportCell_nested μ R hR k t w (center_mem_cleanSupportCell μ R hR (k + t) w)
  by_contra hne
  exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) ht hw

def SupportCellDescendant.compose {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    SupportCellDescendant μ R hR k z where
  depth := i.depth + j.depth
  center := j.center
  mem_net := by rw [← Nat.add_assoc]; exact j.mem_net
  ancestor := by
    apply supportLatticeAncestor_eq_of_center_mem
    exact i.cell_subset_top (j.cell_subset_top j.center_mem_cell)

theorem SupportCellDescendant.compose_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).depth = i.depth + j.depth := rfl

theorem SupportCellDescendant.compose_cell {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).cell = j.cell := by
  simp only [SupportCellDescendant.cell, SupportCellDescendant.compose,
    cleanSupportCell, supportLatticeCell, supportLatticeCenter, Nat.add_assoc]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatDescendantMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def flatDescendantMassConstant (n : ℕ) (C G : ℝ) (I : ℕ) : ℝ :=
  C * G * (24 * (64 : ℝ) ^ I) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularCellGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def annularCellComparisonError (n : ℕ) (C G : ℝ) (D : ℝ≥0) : ℝ :=
  3 * ((D : ℝ) ^ 2 * (G * 2 ^ n * annularCellMassConstant n C) + 1) +
    3 * exteriorCellMeanConstant n G 1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellAnnularWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure CellAnnulus {d : ℕ} (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (ρ : ℝ) where
  center : Ambient d
  center_mem : center ∈ μ.support
  center_dist : dist center (z : Ambient d) ≤ latticeRadius R₀ k / 8
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  inner_le_outer : innerRadius ≤ outerRadius
  inner_lower : ρ * latticeRadius R₀ k ≤ innerRadius
  outer_upper : outerRadius ≤ latticeRadius R₀ k / 8

def CellAnnulus.transform {d : ℕ} {μ : Measure (Ambient d)} {R₀ : ℝ} {hR₀ : 0 < R₀}
    {k : ℕ} {z : (supportLatticeNets μ R₀ hR₀ k).points} {ρ : ℝ}
    (W : CellAnnulus μ R₀ hR₀ k z ρ) (n : ℕ) : Ambient d :=
  smoothAnnularTransform n μ W.center W.innerRadius W.outerRadius
    W.inner_pos (W.inner_pos.trans_le W.inner_le_outer)

def HasLargeCellAnnulus {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (ρ β : ℝ) : Prop :=
  ∃ W : CellAnnulus μ R₀ hR₀ k z ρ, β ≤ ‖W.transform n‖

def CellHaarPair.refl {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (I : ℕ) : CellHaarPair μ R hR k z I where
  outerOffset := 0
  innerOffset := 0
  depth_bound := Nat.zero_le I
  outerCenter := z
  innerCenter := z
  outer_ancestor := by apply Subtype.ext; rfl
  inner_ancestor := by apply Subtype.ext; rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OriginalTestCutoffError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Outer-cutoff errors for mean-zero Lipschitz tests

Restricting the measure to a large ball changes a scalar Riesz pairing by a
controlled tail. The explicit oscillation constant combines the compact test's
amplitude bound with growth and cancellation estimates outside that ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def oscillationTailConstant (n : ℕ) (G J : ℝ) : ℝ :=
  (2 ^ (n + 1) + (n + 1 : ℝ) * 2 ^ (n + 2)) *
    (2 * J * (G * J ^ n)) * J * (2 * (G * 2 ^ n))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_UniformSmallScalePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def smallRieszRadiusFraction (n : ℕ) (G J v : ℝ) : ℝ :=
  min (1 / (2 * J)) (v / (2 * (oscillationTailConstant n G J + 1)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_RieszOscillationPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing for Riesz oscillations

The packing constant combines finitely many coarse levels with the small-scale
Riesz packing estimate. Its positivity yields a packing bound whose constant is
chosen uniformly before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def rieszOscillationPackingConstant (n : ℕ) (C G c J v : ℝ) (D : ℝ≥0) (N : ℕ) : ℝ :=
  (N : ℝ) * ((C / c ^ n) * G * (1 + c) ^ n) +
    (((4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
      (D : ℝ) ^ 2) * G * 3 ^ n / (v / 2) ^ 2) + 1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_HaarCellMassRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def haarCellMassRatio (n : ℕ) (C G : ℝ) (I : ℕ) : ℝ :=
  C * G * 3 ^ n * 8 ^ n * (64 : ℝ) ^ (I * n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_HaarTopBallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def topCellBallIndicator {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (A : ℝ) : Ambient d → ℝ :=
  (ball (z : Ambient d) (A * latticeRadius R k)).indicator (fun _ => 1)

def haarTopBallPackingConstant (n : ℕ) (C G A v : ℝ) (D : ℝ≥0) (I : ℕ) : ℝ :=
  (haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2) * (C * G * (8 * A) ^ n) / v ^ 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_NoFlatDescendantPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def NoFlatDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (I : ℕ) (A α : ℝ) :=
  {i : SupportCellDescendant μ R₀ hR₀ k z //
    ¬ HasFlatDescendant n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ I A α}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BetaDescendantTotalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Total mass of bad-beta descendants

Bad-beta descendants are the support-cell descendants whose enlarged-ball
bilateral beta number exceeds the threshold. Taking the supremum over finite
subsets upgrades the uniform finite Carleson estimate to their full `ENNReal`
mass sum, with the constant still chosen before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def BadBetaDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (H ε : ℝ) :=
  {i : SupportCellDescendant μ R hR k z // ε ≤ bilateralBeta n μ i.center (H * i.radius)}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneDiskHausdorffMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

def planeUnitHausdorffMeasure (n : ℕ) : ℝ≥0∞ :=
  (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall 0 1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteNormalizedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

variable {ι : Type*}

def finiteWeightDenominator (F : Finset ι) (w : ι → ℝ) : ℝ :=
  max 1 (∑ i ∈ F, w i)

def finiteNormalizedWeight (F : Finset ι) (w : ι → ℝ) (i : ι) : ℝ :=
  w i / finiteWeightDenominator F w

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_FiniteChartParameterPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def finiteChartPackingFactor (N : ℕ) : ℝ≥0 := 4 * ((N : ℝ≥0) + 1)

def finiteChartParameterCenter {n : ℕ} (e : Ambient n) (r : ℝ) (N : ℕ) (i : Fin N) : Ambient n :=
  (((i.val : ℝ) + 1) * (r / (2 * ((N : ℝ) + 1)))) • e

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SeparatedParameterPatchGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gluing separated parameter patches

Separation of the parameter centers and control of the image centers give a uniform
cross-patch Lipschitz estimate. The glued map extends to a parameter ball, whose
image covers all patches with an explicit Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def separatedPatchGluingConstant (M A L : ℝ≥0) : ℝ≥0 :=
  max M (2 * (3 * A + L))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_FiniteBallChartUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite unions of ball charts

Separated parameter islands encode finitely many bounded Lipschitz charts in a single
ball chart. The union constant combines the packing factor, the gluing estimate, and
the ambient Lipschitz extension constant. Extension followed by a nonexpansive
retraction also handles charts initially defined on subsets of the parameter ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def finiteBallChartUnionConstant (d N : ℕ) (M : ℝ≥0) : ℝ≥0 :=
  lipschitzExtensionConstant (Ambient d) *
    separatedPatchGluingConstant (M * (4 * finiteChartPackingFactor N)) (finiteChartPackingFactor N) 0

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FinitePieceCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates selected from a Lipschitz ball cover

Choosing a preimage for each covered point produces coordinates in the parameter
ball. The Lipschitz bound on the covering map controls ambient distances by the
distances between these selected coordinates, without requiring continuity of
the selection.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def finitePartialCoordinateConstant (d N : ℕ) (M : ℝ≥0) : ℝ≥0 :=
  max 1 (finiteBallChartUnionConstant d N (lipschitzExtensionConstant (Ambient d) * M))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FiniteCoverCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

def finiteCoverCutoff (c : X) (r : ℝ) (x : X) : ℝ :=
  max 0 (min 1 (4 - dist x c / r))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CellRegionStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits and stops of good cell regions

The limit region consists of points whose containing descendants all satisfy a
chosen good-cell predicate. Stops are the first failures along containment chains.
Countability of descendants makes the limit region measurable by removing the
union of bad cells from the starting cell.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellRegionLimit {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) : Set (Ambient d) :=
  {x ∈ cleanSupportCell μ R hR k z | ∀ i, x ∈ i.cell → Good i}

def cellRegionStops {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    Set (SupportCellDescendant μ R hR k z) :=
  {i | ¬Good i ∧ ∀ j, j.depth < i.depth → i.cell ⊆ j.cell → Good j}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def activeRegionCell (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) : Prop :=
  ∀ q : SupportCellDescendant μ R hR k z, q.depth ≤ i.depth → i.cell ⊆ q.cell → Good q

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CappedStoppingDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Set Metric

def cappedStoppingDistance {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ) (x : X) : ℝ :=
  ⨅ i : Option ι, match i with
    | none => R
    | some i => dist x (c i) + r i

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStoppingScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

def cellRegionStoppingScale : Ambient d → ℝ :=
  cappedStoppingDistance (latticeRadius R k)
    (fun i : {i // activeRegionCell Good i} => i.val.center)
    (fun i => i.val.radius)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

def activeRegionLevel (t : ℕ) : Set (SupportCellDescendant μ R hR k z) :=
  {i | i.depth = t ∧ activeRegionCell Good i}

theorem activeRegionLevel_finite (t : ℕ) : (activeRegionLevel μ R hR k z Good t).Finite := by
  have hN := separated_set_finite_inter_compact (supportLatticeNets μ R hR (k + t)).points
    (closedBall (z : Ambient d) (2 * latticeRadius R k)) (latticeRadius R (k + t))
    (latticeRadius_pos R hR (k + t)) (supportLatticeNets μ R hR (k + t)).separated
    (isCompact_closedBall _ _)
  have himage : (SupportCellDescendant.center '' activeRegionLevel μ R hR k z Good t).Finite := by
    apply hN.subset
    rintro x ⟨i, hi, rfl⟩
    refine ⟨?_, i.center_dist_top⟩
    have hd : i.depth = t := hi.1
    rw [← hd]
    exact i.mem_net
  apply himage.of_finite_image
  intro i hi j hj hcenter
  apply i.eq_of_common_point_same_depth j (hi.1.trans hj.1.symm) i.center i.center_mem_cell
  rw [hcenter]
  exact j.center_mem_cell

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)

def activeLevelIndex : Finset (SupportCellDescendant μ R hR k z) :=
  (activeRegionLevel_finite μ R hR k z Good t).toFinset

theorem mem_activeLevelIndex (i : SupportCellDescendant μ R hR k z) :
    i ∈ activeLevelIndex μ R hR k z Good t ↔
      i ∈ activeRegionLevel μ R hR k z Good t := by
  classical
  exact (activeRegionLevel_finite μ R hR k z Good t).mem_toFinset

def activeLevelCutoff (i : SupportCellDescendant μ R hR k z) (x : Ambient d) : ℝ :=
  finiteCoverCutoff i.center (latticeRadius R (k + t)) x

def activeLevelWeight (i : SupportCellDescendant μ R hR k z) (x : Ambient d) : ℝ :=
  finiteNormalizedWeight (activeLevelIndex μ R hR k z Good t)
    (fun j => activeLevelCutoff μ R hR k z t j x) i

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ImmediateChildPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def supportImmediateChildren {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Finset (SupportCellDescendant μ R hR k z) :=
  activeLevelIndex μ R hR k z (fun _ => True) 1

theorem mem_supportImmediateChildren {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i : SupportCellDescendant μ R hR k z) :
    i ∈ supportImmediateChildren μ R hR k z ↔ i.depth = 1 := by
  rw [supportImmediateChildren, mem_activeLevelIndex]
  change (i.depth = 1 ∧ activeRegionCell (fun _ => True) i) ↔ i.depth = 1
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ => trivial⟩⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_RegionRepresentativeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellRegionRepresentatives {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) : Set (Ambient d) :=
  cellRegionLimit μ R hR k z Good ∪ range (fun i : cellRegionStops μ R hR k z Good => i.val.center)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellBadCountBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellBadCountBound {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (N : ℕ) (x : Ambient d) : Prop :=
  ∀ F : Finset (SupportCellDescendant μ R hR k z),
    (∀ i ∈ F, Bad i ∧ q.depth ≤ i.depth ∧ i.cell ⊆ q.cell ∧ x ∈ i.cell) → F.card ≤ N

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CountableCellMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable cell multiplicity

The sum of cell indicators measures pointwise overlap. Its integral is the total
cell mass, giving tail bounds, almost-everywhere finite incidence, and lower
bounds for the mass where the multiplicity is controlled.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def cellMultiplicity {ι X : Type*} (A : ι → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def supportCellRoot {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) : SupportCellDescendant μ R hR k z where
  depth := 0
  center := z
  mem_net := by simpa only [Nat.add_zero] using! z.property
  ancestor := by simp only [supportLatticeAncestor, supportLatticeCenter, netAncestor_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_FiniteProjectionAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite projection averages

Weighted displacement averages interpolate between the identity and local
projections. Nonnegative weights control displacement from the original point
or a common reference point, and continuous data give a continuous average.
-/

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

variable {ι : Type*} {d : ℕ}

def finiteProjectionAverage (F : Finset ι) (θ : ι → Ambient d → ℝ)
    (π : ι → Ambient d → Ambient d) (x : Ambient d) : Ambient d :=
  x + ∑ i ∈ F, θ i x • (π i x - x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_NonemptyAffineProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine projection with an explicit nonemptiness witness

This projection takes the plane's nonemptiness as an argument rather than a typeclass
assumption. Its displacement is the distance to the plane, and the map is 1-Lipschitz.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

def nonemptyAffineProjection {d : ℕ} (S : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) : Ambient d → Ambient d :=
  letI : Nonempty S := hS.to_subtype
  fun x => (orthogonalProjection S x : Ambient d)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionDiskLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection between subspace disks

Projecting a displacement orthogonally and translating its center carries a closed
disk into a disk of the same radius. The disk lift records this range constraint.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

def projectionDiskLift {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) : closedBall b ρ → closedBall a ρ :=
  fun u => ⟨a + P.orthogonalProjectionOnto ((u.val : Ambient d) - (b : Ambient d)), by
    change dist (a + P.orthogonalProjectionOnto ((u.val : Ambient d) - (b : Ambient d))) a ≤ ρ
    calc
      _ = ‖P.starProjection ((u.val : Ambient d) - (b : Ambient d))‖ := by
        rw [dist_eq_norm, add_sub_cancel_left]
        rfl
      _ ≤ ‖(u.val : Ambient d) - (b : Ambient d)‖ := P.norm_starProjection_apply_le _
      _ ≤ ρ := u.property⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_PlaneChangeProjectedMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parameter maps under a change of plane

The disk lift and orthogonal projection transfer a parametrization to another
plane. Normal Lipschitz control and the distance between projections bound its
deviation from the identity parameter map.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def planeChangedParameterMap {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) (g : closedBall a ρ → Ambient d) : closedBall b ρ → Q :=
  fun v => Q.orthogonalProjectionOnto (g (projectionDiskLift P Q a b ρ v))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionConditionedRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellProjectionNoncollapse {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (P : Submodule ℝ (Ambient d)) (κ : ℝ)
    (i : SupportCellDescendant μ R hR k z) : Prop :=
  ∀ v ∈ (S i).direction, κ * ‖v‖ ≤ ‖P.starProjection v‖

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionRegionChildAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection-region child assembly

Projection-disk coordinates and separated-patch gluing assemble child charts into a
bounded Lipschitz chart covering the region limit and each child's covered cell.
The uncovered parent-cell mass is bounded by the sum of the uncovered child-cell masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def projectionRegionAssemblyConstant (d : ℕ) (L M : ℝ≥0) : ℝ≥0 :=
  ((lipschitzExtensionConstant (Ambient d) *
    separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) * 2) * 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionRegionDepthCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-depth projection-region charts

Iterating child assembly yields a bounded chart with recursively controlled Lipschitz
constant. A fixed fractional stop-mass bound gives a geometric uncovered-mass bound
at each finite depth.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def projectionRegionDepthConstant (d : ℕ) (L : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 1
  | J + 1 => projectionRegionAssemblyConstant d L (projectionRegionDepthConstant d L J)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelProjectionMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

def activeLevelProjectionMap : Ambient d → Ambient d :=
  finiteProjectionAverage (activeLevelIndex μ R hR k z Good t)
    (activeLevelWeight μ R hR k z Good t)
    (fun i => nonemptyAffineProjection (S i) (hS i).1)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionLocalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

def activeProjectionError (d : ℕ) (ε : ℝ) : ℝ :=
  (2048 + 1048576 * (9 : ℝ) ^ d) * ε

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Active-cell chart predicates

Input charts parametrize a larger tangential disk and capture the surface near an active cell.
Surface charts retain exact tangential coordinates on a smaller disk together with quantitative
normal slope, height, and local image bounds. These predicates package the geometric data used
to propagate charts through the active projection construction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
  {z : (supportLatticeNets μ R hR k).points}

def HasActiveCellSurfaceChart (q : SupportCellDescendant μ R hR k z)
    (S : AffineSubspace ℝ (Ambient d)) (ε : ℝ) (A : Set (Ambient d)) : Prop :=
  ∃ h : closedBall (S.direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) → Ambient d,
    LipschitzWith 2 h ∧
    LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε))
      (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
    (∀ u, h u ∈ A ∧ S.direction.orthogonalProjectionOnto (h u) = u.val ∧
      infDist (h u) (S : Set (Ambient d)) ≤ (262144 * ε) * q.radius ∧
      h u ∈ closedBall q.center (3 * q.radius)) ∧
    A ∩ closedBall q.center ((9 / 4 : ℝ) * q.radius) =
      Set.range h ∩ closedBall q.center ((9 / 4 : ℝ) * q.radius)

def HasActiveCellInputChart (q : SupportCellDescendant μ R hR k z)
    (S : AffineSubspace ℝ (Ambient d)) (A : Set (Ambient d)) : Prop :=
  ∃ g : closedBall (S.direction.orthogonalProjectionOnto q.center) ((11 / 4 : ℝ) * q.radius) → Ambient d,
    LipschitzWith 2 g ∧
    (∀ u, S.direction.orthogonalProjectionOnto (g u) = u.val) ∧
    (∀ u, g u ∈ closedBall q.center (3 * q.radius)) ∧
    Set.range g ⊆ A ∧
    A ∩ closedBall q.center ((5 / 2 : ℝ) * q.radius) ⊆ Set.range g

def HasActiveSurfaceCharts (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (ε : ℝ) (A : Set (Ambient d)) : Prop :=
  ∀ q ∈ activeLevelIndex μ R hR k z Good t, HasActiveCellSurfaceChart q (S q) ε A

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSurfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

def activeRegionSurface : ℕ → Set (Ambient d)
  | 0 => (S (supportCellRoot μ R hR k z) : Set (Ambient d))
  | t + 1 => (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS) ''
      activeRegionSurface t

def activeRegionParameterMap : ℕ → Ambient d → Ambient d
  | 0 => id
  | t + 1 => activeLevelProjectionMap μ R hR k z Good (t + 1) S hS ∘
      activeRegionParameterMap t

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionZeroSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

def cellRegionZeroSet : Set (Ambient d) :=
  {x | cellRegionStoppingScale μ R hR k z Good x = 0}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLimitModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

def IsActiveRegionLimitModel {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ)
    (f : S (supportCellRoot μ R hR k z) → Ambient d) : Prop :=
  Continuous f ∧ IsProperMap f ∧
  TendstoUniformly (fun t (u : S (supportCellRoot μ R hR k z)) =>
    activeRegionParameterMap μ R hR k z Good S hS t u) f atTop ∧
  (∀ t (u : S (supportCellRoot μ R hR k z)),
    dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤
      ((17039360 * ε) / 63) * latticeRadius R (k + t)) ∧
  cellRegionZeroSet μ R hR k z Good ⊆ Set.range f ∧
  cellRegionLimit μ R hR k z Good ⊆ Set.range f ∧
  ∀ (K : Set (Ambient d)) (δ : ℝ), 0 < δ →
    (∀ x ∈ K, δ ≤ cellRegionStoppingScale μ R hR k z Good x) →
    ∃ N, ∀ t, N ≤ t → Set.range f ∩ K = activeRegionSurface μ R hR k z Good S hS t ∩ K

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionGlobalLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators NNReal

def activeProjectionGlobalLipschitzConstant (d : ℕ) : ℝ≥0 :=
  Real.toNNReal (3 + 24 * (9 : ℝ) ^ d)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionTransitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (s : ℕ)

def activeRegionTransitionMap : ℕ → Ambient d → Ambient d
  | 0 => id
  | j + 1 => activeLevelProjectionMap μ R hR k z Good (s + j + 1) S hS ∘ activeRegionTransitionMap j

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_PlaneChartBallArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def planeChartBallAreaConstant (n : ℕ) (K L : ℝ≥0) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞) * (K : ℝ≥0∞) * (L : ℝ≥0∞)) ^ n * planeUnitHausdorffMeasure n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_PlaneDiskLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def planeDiskLowerAreaConstant (n : ℕ) (L : ℝ≥0) : ℝ≥0∞ :=
  planeUnitHausdorffMeasure n / (L : ℝ≥0∞) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveLocalLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionPositiveLocalLowerAreaConstant (n : ℕ) : ℝ≥0∞ :=
  planeDiskLowerAreaConstant n 64 * (ENNReal.ofReal (1 / 16 : ℝ)) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStopMassArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stopping-cell mass controlled by model area

Global growth bounds and the lower area of stopping cores control the mass of
stopping cells by Hausdorff measure on the limit model. Disjoint cores allow these
estimates to be summed over countable families inside a prescribed region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionStopMassAreaConstant (n : ℕ) (G : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (G * 384 ^ n) / activeRegionPositiveLocalLowerAreaConstant n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellPieceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def activeCellStopDescendants {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) : Set (SupportCellDescendant μ R hR k z) :=
  {i | i ∈ cellRegionStops μ R hR k z Good ∧ q.depth < i.depth ∧ i.cell ⊆ q.cell}

def activeCellRepresentedSet {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) : Set (Ambient d) :=
  (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E) ∪
    ⋃ i : {i : SupportCellDescendant μ R hR k z //
      i ∈ activeCellStopDescendants μ R hR k z Good q ∧
        ¬ Disjoint (closedBall i.center (i.radius / 32)) E}, i.val.cell

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellChildImageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Image-mass estimates for selected stopping cells

Pairwise disjointness controls the total mass omitted by child pieces. Combining
that bound with the active-cell representation estimates the mass still missing
from a glued image in terms of discarded surface area and child-cell losses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def activeCellSelectedStopSet {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    Set (SupportCellDescendant μ R hR k z) :=
  {i | i ∈ activeCellStopDescendants μ R hR k z Good q ∧
    ¬ Disjoint (closedBall i.center (i.radius / 32)) E}

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellFinitePieceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeCellFinitePieceAssemblyConstant (d N : ℕ) (P M : ℝ≥0) : ℝ≥0 :=
  (lipschitzExtensionConstant (Ambient d) *
    separatedPatchGluingConstant (M * (4 * (32 * finitePartialCoordinateConstant d N P)))
      (32 * finitePartialCoordinateConstant d N P) (finitePartialCoordinateConstant d N P)) * 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLargeRadiusLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLargeRadiusLowerAreaConstant (n : ℕ) : ℝ≥0∞ :=
  planeDiskLowerAreaConstant n 1 * (ENNReal.ofReal (1 / 8 : ℝ)) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSmallRadiusLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def activeRegionLowScaleAreaFactor (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  (384 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n) *
    (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)

def activeRegionSmallRadiusLowerAreaConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  min (activeRegionLowScaleAreaFactor n C G)⁻¹
    (activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (1 / 1024 : ℝ)) ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionAllRadiusLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def activeRegionAllRadiusLowerAreaConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  min (activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal (1 / 8 : ℝ)) ^ n)
    (activeRegionLargeRadiusLowerAreaConstant n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLargeScaleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLargeAreaConstant (n d : ℕ) : ℝ≥0∞ :=
  (((activeProjectionGlobalLipschitzConstant d) ^ 2 : ℝ≥0) : ℝ≥0∞) ^ n *
    (3 : ℝ≥0∞) ^ n * planeUnitHausdorffMeasure n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveScaleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive stopping-scale charts bound the local Hausdorff area of an active-region limit
surface by a finite dimensional constant times the cell radius to the power `n`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLocalAreaConstant (n d : ℕ) : ℝ≥0∞ :=
  (((activeProjectionGlobalLipschitzConstant d) ^ 3 * 2 : ℝ≥0) : ℝ≥0∞) ^ n *
    (ENNReal.ofReal (5 / 2)) ^ n * planeUnitHausdorffMeasure n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSmallScaleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionSmallScaleAreaConstant (n d : ℕ) (C : ℝ) : ℝ≥0∞ :=
  (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) *
    ENNReal.ofReal (C * 256 ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionZeroSetArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def activeRegionZeroAreaConstant (n : ℕ) (C : ℝ) : ℝ≥0∞ :=
  (6 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionZeroLocalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def activeRegionZeroLocalAreaConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  (6 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n) * ENNReal.ofReal G * (2 : ℝ≥0∞) ^ n

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLocalUpperArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionLocalUpperAreaConstant (n d : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  activeRegionZeroLocalAreaConstant n C G +
    activeRegionSmallScaleAreaConstant n d C * ENNReal.ofReal G * (2 : ℝ≥0∞) ^ n +
    planeChartBallAreaConstant n 16 64 * (2 : ℝ≥0∞) ^ n +
    planeChartBallAreaConstant n 4 16

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_OriginalTopAreaCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def enlargedTopMassConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (G * 4 ^ n) * ENNReal.ofReal (C * 8 ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionUniformArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def activeRegionUniformAreaConstant (n d : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  activeRegionZeroAreaConstant n C +
    activeRegionSmallScaleAreaConstant n d C * enlargedTopMassConstant n C G +
    activeRegionLargeAreaConstant n d * ENNReal.ofReal (C * 8 ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_BadBetaStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stopping estimates from bad-beta multiplicity

Bad-beta descendants form a countable family of measurable cells. Their total-mass
packing bound controls the tail of the cell multiplicity and gives almost-everywhere
finite incidence. At the threshold twice the packing constant, at least half the
root-cell mass remains in the low-multiplicity region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def badBetaMultiplicity {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (H ε : ℝ) : Ambient d → ℝ≥0∞ :=
  cellMultiplicity (fun i : BadBetaDescendant n μ R hR k z H ε => i.val.cell)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CellRestartPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def cellRestartsAfter {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) : Prop :=
  i.depth = 0 ∨ ∃ q : SupportCellDescendant μ R hR k z,
    Bad q ∧ i.depth = q.depth + 1 ∧ i.cell ⊆ q.cell

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ImmediateChildChartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def immediateChildAssemblyConstant (d : ℕ) (M : ℝ≥0) : ℝ≥0 :=
  finiteBallChartUnionConstant d (257 ^ d) (M / 64)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_RestartChartStepBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lipschitz constants for restart-chart iteration

The step constant simultaneously bounds the inherited chart constant, one, and
the two constants needed for immediate-child and active-cell assembly. Iterating
this monotone envelope gives nondecreasing bounds for every finite restart depth.
-/

namespace RieszRectifiability

noncomputable section

open scoped NNReal

def restartChartStepConstant (d N : ℕ) (P M : ℝ≥0) : ℝ≥0 :=
  max M (max 1 (max (immediateChildAssemblyConstant d M)
    (activeCellFinitePieceAssemblyConstant d N P M)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_GoodRegionRestartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restart chart assembly in a good region

Immediate-child charts first assemble at selected stopping cells, then join the
finite pieces of the active region. The resulting ball chart covers both families;
its uncovered mass is bounded by the omitted surface area and child deficits.
The Lipschitz constant is controlled by two restart steps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def goodRegionRestartAssemblyConstant (d N : ℕ) (P M : ℝ≥0) : ℝ≥0 :=
  activeCellFinitePieceAssemblyConstant d N P (immediateChildAssemblyConstant d M)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_RestartCoverageInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restart coverage with a finite bad-cell budget

The iterated chart constant records the cost of assembling child charts. Induction
on the bad-cell budget covers points outside the restart remainders, since passing
a bad descendant reduces the remaining budget. Countable subadditivity then bounds
the uncovered mass by the original deficit and the sum of all remainder masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def badBudgetChartConstant (step : ℝ≥0 → ℝ≥0) : ℕ → ℝ≥0
  | 0 => step 1
  | b + 1 => step (badBudgetChartConstant step b)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def relativeRestartGood (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) :
    SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ → Prop :=
  fun i => ¬ Bad (q.compose i)

def relativeSelectedRestartStops (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    Set (SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) :=
  {i | i ∈ cellRegionStops μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
      (relativeRestartGood Bad q) ∧
    (i.depth = 0 ∨ ¬ Disjoint (closedBall i.center (i.radius / 32)) E)}

def selectedRestartParent (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) : Set (Ambient d) :=
  cellRegionLimit μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ (relativeRestartGood Bad q) ∩ E

def selectedRestartRemainder (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) : Set (Ambient d) :=
  q.cell \ (selectedRestartParent Bad q E ∪
    ⋃ i : relativeSelectedRestartStops Bad q E, i.val.cell)

def selectedRestartNext (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    Set {w : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad w} :=
  {w | ∃ i : relativeSelectedRestartStops Bad q E,
    ∃ j : supportImmediateChildren μ R hR (k + q.depth + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩, w.val = q.compose (i.val.compose j.val)}

theorem selected_restart_child_is_restart
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (i : relativeSelectedRestartStops Bad q E)
    (j : supportImmediateChildren μ R hR (k + q.depth + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩) : cellRestartsAfter Bad (q.compose (i.val.compose j.val)) := by
  have hbad : Bad (q.compose i.val) := not_not.mp i.property.1.1
  have hj := (mem_supportImmediateChildren μ R hR _ _ j.val).mp j.property
  refine Or.inr ⟨q.compose i.val, hbad, ?_, ?_⟩
  · simp only [SupportCellDescendant.compose_depth, hj, Nat.add_assoc]
  · rw [SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell,
      SupportCellDescendant.compose_cell]
    exact j.val.cell_subset_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_OriginalADRestartCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selected restart assembly with controlled mass deficit

`HasSelectedRestartAssembly` records how parent charts incorporate selected
child charts while preserving range and Lipschitz bounds. For a fixed regular
AD measure with a bounded Riesz transform, restart-loss and bad-count budgets
then produce a root-ball chart with arbitrarily small relative mass deficit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def HasSelectedRestartAssembly {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (n : ℕ) (Bad : SupportCellDescendant μ R hR k z → Prop)
    (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
    (step : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}) (M : ℝ≥0)
    (child : ∀ w : selectedRestartNext Bad q.val (E q),
      ball (0 : Ambient n) w.val.val.radius → Ambient d),
    (∀ w, LipschitzWith M (child w)) →
    (∀ w, Set.range (child w) ⊆ closedBall w.val.val.center (2 * w.val.val.radius)) →
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (step M) g ∧ Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      selectedRestartParent Bad q.val (E q) ⊆ Set.range g ∧
      ∀ w, w.val.val.cell ∩ Set.range (child w) ⊆ Set.range g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ProjectionStopShadowMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projected mass of stopping-cell shadows

The stopping-cell radius bound converts individual fitted-plane shadow estimates into
a Hausdorff measure bound for their projected union, controlled by the top cell's mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def projectionStopShadowConstant (n : ℕ) (C σ κ : ℝ) : ℝ :=
  ((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
    (σ + κ) * (2 : ℝ) ^ n * (C * (8 : ℝ) ^ n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Surface data for selected restart assembly

Finite Lipschitz surface pieces and an active-region limit model supply the parent chart
at a good restart. At a bad restart the selected stop is the root, so immediate-child
assembly suffices. Both cases share a bound given by two restart-chart steps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

/-- Plane fits, a limit model, and bounded surface pieces covering the restart set. -/
structure SelectedRestartSurfaceData (n : ℕ)
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (ε : ℝ) (N : ℕ) (P : ℝ≥0) where
  planes : SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ →
    AffineSubspace ℝ (Ambient d)
  isPlane : ∀ i, IsAffineNPlane n (planes i)
  fits : ∀ i, activeRegionCell (relativeRestartGood Bad q) i →
    bilateralPlaneError μ i.center (1024 * i.radius) (planes i) < ε
  model : planes (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) → Ambient d
  isModel : IsActiveRegionLimitModel μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
    (relativeRestartGood Bad q) planes isPlane ε model
  domains : Fin N → Set (Ambient n)
  domains_bounded : ∀ j, domains j ⊆ ball (0 : Ambient n) q.radius
  pieces : Fin N → Ambient n → Ambient d
  pieces_lipschitz : ∀ j, LipschitzOnWith P (pieces j) (domains j)
  pieces_bounded : ∀ j, pieces j '' domains j ⊆ closedBall q.center (3 * q.radius)
  pieces_cover : E = ⋃ j : Fin N, pieces j '' domains j

/-- Embed an immediate child of a relative selected stop into the next restart nodes. -/
def selectedRestartChildNode (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (i : relativeSelectedRestartStops Bad q E)
    (j : supportImmediateChildren μ R hR (k + q.depth + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩) : selectedRestartNext Bad q E :=
  ⟨⟨q.compose (i.val.compose j.val), selected_restart_child_is_restart Bad q E i j⟩,
    ⟨i, j, rfl⟩⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_BallChartPartialMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ball charts as ambient parameter maps

A chart on a parameter ball is extended by zero outside its domain. On the ball,
this ambient map agrees with the chart and retains its Lipschitz bound.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

def ballChartPartialMap {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) (u : Ambient n) : Ambient d := by
  classical
  exact if hu : u ∈ ball (0 : Ambient n) r then g ⟨u, hu⟩ else 0

theorem ballChartPartialMap_apply {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) (u : Ambient n) (hu : u ∈ ball (0 : Ambient n) r) :
    ballChartPartialMap r g u = g ⟨u, hu⟩ := by
  simp only [ballChartPartialMap, dite_eq_left hu]

theorem ballChartPartialMap_lipschitzOn {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) (M : ℝ≥0) (hg : LipschitzWith M g) :
    LipschitzOnWith M (ballChartPartialMap r g) (ball (0 : Ambient n) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [ballChartPartialMap_apply r g x hx, ballChartPartialMap_apply r g y hy]
  exact hg.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩

theorem ballChartPartialMap_image {n d : ℕ} (r : ℝ)
    (g : ball (0 : Ambient n) r → Ambient d) :
    ballChartPartialMap r g '' ball (0 : Ambient n) r = Set.range g := by
  apply Set.Subset.antisymm
  · rintro y ⟨u, hu, rfl⟩
    rw [ballChartPartialMap_apply r g u hu]
    exact Set.mem_range_self (⟨u, hu⟩ : ball (0 : Ambient n) r)
  · rintro y ⟨u, rfl⟩
    exact ⟨u.val, u.property, ballChartPartialMap_apply r g u.val u.property⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartBallChartData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selected restart surface data from a ball chart

A Lipschitz ball chart supplies the single covering piece in selected restart
surface data, alongside the given fitted planes and active-region limit model.
The relative good-cell condition for beta stopping is also identified with the
strict bilateral-beta bound after composing descendants.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def selectedRestartSurfaceDataOfBallChart
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z)
    (S : SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ)
    (hfit : ∀ i, activeRegionCell (relativeRestartGood Bad q) i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
      (relativeRestartGood Bad q) S hS ε f)
    (g : ball (0 : Ambient n) q.radius → Ambient d) (M : ℝ≥0) (hg : LipschitzWith M g)
    (himage : Set.range g ⊆ closedBall q.center (3 * q.radius)) :
    SelectedRestartSurfaceData n Bad q (Set.range g) ε 1 M where
  planes := S
  isPlane := hS
  fits := hfit
  model := f
  isModel := hmodel
  domains := fun _ => ball (0 : Ambient n) q.radius
  domains_bounded := fun _ => Subset.rfl
  pieces := fun _ => ballChartPartialMap q.radius g
  pieces_lipschitz := fun _ => ballChartPartialMap_lipschitzOn q.radius g M hg
  pieces_bounded := fun _ => by
    rw [ballChartPartialMap_image]
    exact himage
  pieces_cover := by simp only [ballChartPartialMap_image, iUnion_const]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_NativeCoreAreaFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform fraction for core area

The core-area fraction depends only on the dimension and upper growth
constant. Its coefficient bound compares lattice-cell mass with the
Hausdorff measure of a plane disk at the smaller core scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def nativeCoreAreaFraction (n : ℕ) (G : ℝ) : ℝ :=
  min (1 / 2) ((planeUnitHausdorffMeasure n).toReal /
    (2 * (G * (3 : ℝ) ^ n * (32 : ℝ) ^ n)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_NativeSurfaceArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic surface-area measures

The native surface-area measure is Hausdorff measure restricted to the surface.
Upper area growth gives local finiteness and regularity, while lower area bounds
identify the support when the surface is closed.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

def nativeSurfaceArea {d : ℕ} (n : ℕ) (A : Set (Ambient d)) : Measure (Ambient d) :=
  (μH[(n : ℝ)] : Measure (Ambient d)).restrict A

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_NativeSurfaceRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Two-sided Hausdorff measure bounds yield a single AD constant for native surface area.
Global positive-dimensional lower growth also forces infinite support diameter.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

def nativeSurfaceADConstant (n : ℕ) (c C : ℝ≥0∞) : ℝ :=
  1 + C.toReal + (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n).toReal⁻¹

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_SurfaceBallCellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cell centers near a surface ball

Compactness makes the separated lattice centers near a ball finite. A Euclidean packing
estimate bounds their number uniformly in the ball center and radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem surface_ball_cell_centers_finite {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    {z : (supportLatticeNets ν r hr 0).points | dist (z : Ambient d) a ≤ 5 * r}.Finite := by
  have hf := separated_set_finite_inter_compact (supportLatticeNets ν r hr 0).points
    (closedBall a (5 * r)) (latticeRadius r 0) (latticeRadius_pos r hr 0)
    (supportLatticeNets ν r hr 0).separated (isCompact_closedBall _ _)
  have hpre := hf.preimage (f := fun z : (supportLatticeNets ν r hr 0).points => (z : Ambient d))
    Subtype.val_injective.injOn
  apply hpre.subset
  intro z hz
  exact ⟨z.property, hz⟩

def surfaceBallCellCenters {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) : Finset (supportLatticeNets ν r hr 0).points :=
  (surface_ball_cell_centers_finite ν r hr a).toFinset

end

end RieszRectifiability

end OAI
end


