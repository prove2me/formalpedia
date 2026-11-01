-- Prove2me | Definitions.Def_OAIQ080A000
-- name    : OAIQ080A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:06:16.917644+00:00
-- url     : https://prove2.me/theorems/987412be-cd63-429d-a643-ebbac9ae844e
-- title:
--   Definitions bundle OAIQ080A000 of the split of OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1188 declarations of OpenAI's Lean: 901 definitions, 23 inductive types or structures, 29 instances and 235 theorems. The definitions and types are `OAI.BoltzmannNonuniqueness.AdmissibleLocal`, `OAI.BoltzmannNonuniqueness.AffineSlices.intervalConstant`, `OAI.BoltzmannNonuniqueness.AffineSlices.rectangleConstant`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.cell`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.commonMoment`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.finiteEnvelope`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.momentMajorant`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.shell`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.squareEnvelope`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.tailRegion`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.term`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timeSpaceVolume`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.torusChart`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.torusTail`, `OAI.BoltzmannNonuniqueness.AxialAnalytic.FlowParameters`, `OAI.BoltzmannNonuniqueness.AxialAnalytic.jointCharacteristic`, `OAI.BoltzmannNonuniqueness.AxialAnalytic.jointFoot`, `OAI.BoltzmannNonuniqueness.AxialBackground.atom`, `OAI.BoltzmannNonuniqueness.AxialBackground.cell`, `OAI.BoltzmannNonuniqueness.AxialBackground.compactWeightLower`, `OAI.BoltzmannNonuniqueness.AxialBackground.relativeWeight`, `OAI.BoltzmannNonuniqueness.AxialBackground.weight`, `OAI.BoltzmannNonuniqueness.AxialDerivative.A`, `OAI.BoltzmannNonuniqueness.AxialFlow.bands`, `OAI.BoltzmannNonuniqueness.AxialFlow.characteristic`, `OAI.BoltzmannNonuniqueness.AxialFlow.collapsedCenters`, `OAI.BoltzmannNonuniqueness.AxialFlow.foot`, `OAI.BoltzmannNonuniqueness.AxialFlow.interiorArgumentBound`, `OAI.BoltzmannNonuniqueness.AxialFlow.profile`, `OAI.BoltzmannNonuniqueness.AxialFlow.profileCenters`, `OAI.BoltzmannNonuniqueness.AxialFlow.residual`, `OAI.BoltzmannNonuniqueness.AxialFlow.velocity`, `OAI.BoltzmannNonuniqueness.AxialModulus.axialRegion`, `OAI.BoltzmannNonuniqueness.AxialModulus.intervalMajorant`, `OAI.BoltzmannNonuniqueness.AxialSlices.lineConstant`, `OAI.BoltzmannNonuniqueness.AxialSlices.lineProfile`, `OAI.BoltzmannNonuniqueness.AxialSlices.scalarConstant`, `OAI.BoltzmannNonuniqueness.AxialTransport.flightFoot`, `OAI.BoltzmannNonuniqueness.AxialTransport.flightVelocity` and 884 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Boltzmann_Admissibility`, `Boltzmann_Approximation_CapCoefficientExtraction`, `Boltzmann_Approximation_CapColdAverages`, `Boltzmann_Approximation_CapColdBounds`, `Boltzmann_Approximation_CapCoveredDamping`, `Boltzmann_Approximation_CapDilationCompactness`, `Boltzmann_Approximation_CapDilationScales`, `Boltzmann_Approximation_CapEscapingSeed`, `Boltzmann_Approximation_CapFiniteBackgroundLimit`, `Boltzmann_Approximation_CapHotSourceIntegrability`, `Boltzmann_Approximation_CapHotTransportBalance`, `Boltzmann_Approximation_CapHotUndamped`, `Boltzmann_Approximation_CapLabelFreeLimit`, `Boltzmann_Approximation_CapLimitTransport`, `Boltzmann_Approximation_CapMildLimit`, `Boltzmann_Approximation_CapMixedCollisionLimits`, `Boltzmann_Approximation_CapMixedPositiveBound`, `Boltzmann_Approximation_CapPairMoments`, `Boltzmann_Approximation_CappedDensitySequence`, `Boltzmann_Approximation_ColoredDifferenceAlgebra`, `Boltzmann_Approximation_CutoffEntropyMeasure`, `Boltzmann_Approximation_CutoffLipschitz`, `Boltzmann_Approximation_CutoffLossFrequency`, `Boltzmann_Approximation_DormantBoxLimit`, `Boltzmann_Approximation_DormantConstruction`, `Boltzmann_Approximation_MildCharacteristics`, `Boltzmann_Approximation_MildCurveContinuity`, `Boltzmann_Approximation_MildRenormalization`, `Boltzmann_Approximation_PositiveComparisonBound`, `Boltzmann_Approximation_PositiveIntegralFixedPoint`, `Boltzmann_Approximation_PositiveMildRepresentative`, `Boltzmann_Approximation_PositiveSourceFormula`, `Boltzmann_Approximation_PositiveVolterra`, `Boltzmann_Approximation_SubcapColdControl`, `Boltzmann_Approximation_SubcapMildLimits`, `Boltzmann_Approximation_SurvivalProfile`, `Boltzmann_Branching_AffineSlices`, `Boltzmann_Branching_AxisInput`, `Boltzmann_Branching_AxisMismatch`, `Boltzmann_Branching_BackgroundCappedLoss`, `Boltzmann_Branching_BoundedAverageProducts`, `Boltzmann_Branching_BoundedCollisionBlocks`, `Boltzmann_Branching_BoundedMeshStep`, `Boltzmann_Branching_CharacteristicCoordinates`, `Boltzmann_Branching_CharacteristicCutoffGeometry`, `Boltzmann_Branching_CharacteristicProductTest`, `Boltzmann_Branching_ChartPointLift`, `Boltzmann_Branching_ClippedColdFiniteLimit`, `Boltzmann_Branching_CommonMomentEnvelope`, `Boltzmann_Branching_CompactCapFamily`, `Boltzmann_Branching_CompactParameterConvergence`, `Boltzmann_Branching_ControlledParameterPath`, `Boltzmann_Branching_DampedBranchingBlocks`, `Boltzmann_Branching_DampedCollisionHistories`, `Boltzmann_Branching_DatumBounds`, `Boltzmann_Branching_DiagonalVanishingCap`, `Boltzmann_Branching_DilatedCoreDensity`, `Boltzmann_Branching_DilatedTwoCoreLimit`, `Boltzmann_Branching_DoubleCollisionTests`, `Boltzmann_Branching_EntrySites`, `Boltzmann_Branching_EuclideanBackwardMap`, `Boltzmann_Branching_EuclideanKineticMap`, `Boltzmann_Branching_ExponentialPairIntegrability`, `Boltzmann_Branching_FiveGainConvergence`, `Boltzmann_Branching_FiveGainPullback`, `Boltzmann_Branching_FiveGainRank`, `Boltzmann_Branching_FlightMeasure`, `Boltzmann_Branching_GainNonnegative`, `Boltzmann_Branching_HalfGaussianMoment`, `Boltzmann_Branching_HotCanonicalFamily`, `Boltzmann_Branching_HotChartHomeomorph`, `Boltzmann_Branching_HotCollisionDecomposition`, `Boltzmann_Branching_HotGainReduction`, `Boltzmann_Branching_HotPairWindowGeometry`, `Boltzmann_Branching_HotPhysicalSource`, `Boltzmann_Branching_HotPositiveRegion`, `Boltzmann_Branching_HotQuadraticGain`, `Boltzmann_Branching_HotSeedCoreLower`, `Boltzmann_Branching_HotWindowGeometry`, `Boltzmann_Branching_IncomingLossRate`, `Boltzmann_Branching_LargeOutput`, `Boltzmann_Branching_LateBoxAccessMeasure`, `Boltzmann_Branching_LinearHotLocalization`, `Boltzmann_Branching_LossIntegrability`, `Boltzmann_Branching_MainCoreScaleWindow`, `Boltzmann_Branching_MainParameters`, `Boltzmann_Branching_MismatchSlices`, `Boltzmann_Branching_MixedPhysicalMeasures`, `Boltzmann_Branching_MixedRealGain`, `Boltzmann_Branching_MovingBoxMass`, `Boltzmann_Branching_NormalGainMeasureActions`, `Boltzmann_Branching_OffAxisBoxExhaustion`, `Boltzmann_Branching_PerturbedFiniteBlock`, `Boltzmann_Branching_PhaseDecompositionNorm`, `Boltzmann_Branching_PhaseSliceLocalization`, `Boltzmann_Branching_PlaneChart`, `Boltzmann_Branching_PowerDiskMixture`, `Boltzmann_Branching_ProductKineticCutoff`, `Boltzmann_Branching_PublishedInputs`, `Boltzmann_Branching_RawPairCompactness`, `Boltzmann_Branching_RebuiltHotInitial`, `Boltzmann_Branching_RedundantParameterSupport`, `Boltzmann_Branching_RedundantPlaneIntegral`, `Boltzmann_Branching_ReferenceAngularCharts`, `Boltzmann_Branching_ReferenceBranchingHistories`, `Boltzmann_Branching_ReferenceCollisionGeometry`, `Boltzmann_Branching_RescaledBoundedGain`, `Boltzmann_Branching_RescaledParameterSlab`, `Boltzmann_Branching_SeparationBoxContainment`, `Boltzmann_Branching_ShiftedStripe`, `Boltzmann_Branching_SmoothedPrePostIdentity`, `Boltzmann_Branching_SpacetimeFourierCoordinates`, `Boltzmann_Branching_StageParameterIntegration`, `Boltzmann_Branching_StripeCells`, `Boltzmann_Branching_SupportedTensorConvergence`, `Boltzmann_Branching_ThreeCollisionTimes`, `Boltzmann_Branching_TightCapFamily`, `Boltzmann_Branching_TimeSourceCumulative`, `Boltzmann_Branching_TranslatedCoreKernel`, `Boltzmann_Branching_TransportCutoff`, `Boltzmann_Branching_WeightedJetSolutions`, `Boltzmann_Branching_WeightedJetStability`, `Boltzmann_Branching_WeightedNetLoss`, `Boltzmann_Branching_WeightedPairUniformIntegrability`, `Boltzmann_Branching_WeightedThermalChain`, `Boltzmann_Collision_AngularGainTranslationTests`, `Boltzmann_Collision_AngularPairTests`, `Boltzmann_Collision_AxialAtomicSheet`, `Boltzmann_Collision_AxialBandMeasure`, `Boltzmann_Collision_AxialFlow`, `Boltzmann_Collision_AxialJointAnalytic`, `Boltzmann_Collision_AxialSecondMismatch`, `Boltzmann_Collision_CarlemanIdentity`, `Boltzmann_Collision_CarlemanNormalCoordinates`, `Boltzmann_Collision_CarlemanOperator`, `Boltzmann_Collision_CollisionConservation`, `Boltzmann_Collision_CollisionDissipation`, `Boltzmann_Collision_CollisionMeasure`, `Boltzmann_Collision_CollisionParameterShuffle`, `Boltzmann_Collision_CollisionSources`, `Boltzmann_Collision_CollisionWeakMarginals`, `Boltzmann_Collision_GaussianEstimates`, `Boltzmann_Collision_GaussianFrequency`, `Boltzmann_Collision_GaussianLocalExistence`, `Boltzmann_Collision_ScalarEntropyConvex`, `Boltzmann_Collision_SheetGain`, `Boltzmann_Collision_SheetIntervals`, `Boltzmann_Collision_TransverseAverage`, `Boltzmann_Collision_TransverseStripeWeak`, `Boltzmann_Collision_VelocityAverageDifference`, `Boltzmann_Collision_VelocityFourierMultiplier`, `Boltzmann_Collision_VelocitySmoothingError`, `Boltzmann_Collision_VelocityWeight`, `Boltzmann_Collision_WeightAlgebra`, `Boltzmann_Collision_WeightLocalL1`, `Boltzmann_Compactness_EntropyDissipationCoordinates`, `Boltzmann_Compactness_FiniteParameterChain`, `Boltzmann_Compactness_FiniteThermalLimit`, `Boltzmann_Compactness_KineticDensityMeasurable`, `Boltzmann_Compactness_KineticDilationIntegral`, `Boltzmann_Compactness_KineticWindowL1`, `Boltzmann_Compactness_LocalAdmissibility`, `Boltzmann_Compactness_LocalizedDampedBalance`, `Boltzmann_Compactness_LocalizedGainSmoothingAE`, `Boltzmann_Compactness_NormalizedCollisionRates`, `Boltzmann_Compactness_NormalizedKernelAction`, `Boltzmann_Compactness_NormalizedPairCompactness`, `Boltzmann_Compactness_PairBoundedTruncation`, `Boltzmann_Compactness_PairPatchIdentity`, `Boltzmann_Compactness_PeriodicFiniteMild`, `Boltzmann_Compactness_PeriodicInitialEntropyLimit`, `Boltzmann_Compactness_PeriodicMildApproximation`, `Boltzmann_Compactness_PeriodicMomentEntropy`, `Boltzmann_Compactness_PeriodicStrongAverages`, `Boltzmann_Compactness_PeriodicWeakCompactness`, `Boltzmann_Compactness_PhysicalCharacteristic`, `Boltzmann_Compactness_PhysicalFrequencyWindow`, `Boltzmann_Compactness_RenormalizedIntegrability`, `Boltzmann_Compactness_SelectedCoreSelection`, `Boltzmann_Compactness_SelectedLargeOutput`, `Boltzmann_Compactness_SelectedNonaxialLimit`, `Boltzmann_Compactness_SelectedOriginDeletion`, `Boltzmann_Compactness_SelectedTwoGainLimit`, `Boltzmann_Compactness_StrongMassClip`, `Boltzmann_Compactness_UniformGain`, `Boltzmann_Compactness_UniformIntegrability`, `Boltzmann_Compactness_WeakL1Operations`, `Boltzmann_Compactness_WeakL1ToWeakStar`, `Boltzmann_Jets_AnnularEnvelopes`, `Boltzmann_Jets_ColdCentralVanishing`, `Boltzmann_Jets_ColdGaussianFamily`, `Boltzmann_Jets_ColdMildRepresentative`, `Boltzmann_Jets_CoreDensityTranslation`, `Boltzmann_Jets_CoreJointParameterDensity`, `Boltzmann_Jets_CoreParameterStep`, `Boltzmann_Jets_FreeCoreGainKernel`, `Boltzmann_Jets_FreeCoreMismatch`, `Boltzmann_Jets_GeometricColdSource`, `Boltzmann_Jets_GeometricEntry`, `Boltzmann_Jets_GeometricMesh`, `Boltzmann_Jets_GeometricPositiveCompact`, `Boltzmann_Jets_GeometricSlice`, `Boltzmann_Jets_GeometricTwoCoreUniform`, `Boltzmann_Jets_JetBarrierKinetic`, `Boltzmann_Jets_JetBarriers`, `Boltzmann_Jets_JetColdLimitComparison`, `Boltzmann_Jets_JetContinuation`, `Boltzmann_Jets_JetCoreConvergence`, `Boltzmann_Jets_JetCoreMomentBound`, `Boltzmann_Jets_JetEnvelopeTimeIntegral`, `Boltzmann_Jets_JetFamilyBounds`, `Boltzmann_Jets_JetPeriodicDatum`, `Boltzmann_Jets_JetProfiles`, `Boltzmann_Jets_JetSupersolutions`, `Boltzmann_Jets_OriginMeshLimit`, `Boltzmann_Jets_OriginMeshStep`, `Boltzmann_Jets_PeriodicJetFamilies`, `Boltzmann_Jets_SpatialCutoffIntegrability`, `Boltzmann_Jets_ThermalParameterChain`, `Boltzmann_Jets_ThermalStripeIdentity`, `Boltzmann_Jets_TorusAnnularIntegrability`, `Boltzmann_Jets_TorusChart`, `Boltzmann_Jets_TorusTailRegions`, `Boltzmann_Jets_TorusTransport`, `Boltzmann_Model`.
--
--   **Imports.** It imports the published bundle `Def_BoltzmannNonuniqueness`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ080A002`; the statements `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_mesh_average_L1_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_spacetime_weakStar_limit_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_coldLabelAverage_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.eventually_positive_fraction_mass_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_mixedPrelimitMeasure_gaussian_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.cap_family_cutoff_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_gainLoss_uniformIntegrable_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_spacetime_outer_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_total_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.positiveMainKernel_bound_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.retained_second_small_off_bands_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_pair_uniform_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selected_velocity_windows_q80` and `OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80`.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit 1581d4c

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness

section
-- module Solutions.OAIQ080_BZ.Compat
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
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision model for periodic hard spheres

The normal parametrization and absolute angular kernel here are exactly those of
Sections 1–2 of the paper.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem collisionKernel_nonneg (v w ω : Velocity) : 0 ≤ collisionKernel v w ω :=
  abs_nonneg _

theorem scatter_energy (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    ‖scatterLeft v w ω‖ ^ 2 + ‖scatterRight v w ω‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  unfold scatterLeft scatterRight normalComponent
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs,
    inner_sub_left]
  ring

theorem normalComponent_scatter (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    normalComponent (scatterLeft v w ω) (scatterRight v w ω) ω =
      -normalComponent v w ω := by
  simp only [normalComponent, scatterLeft, scatterRight, inner_sub_left, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hω]
  ring

theorem scatterLeft_involutive (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    scatterLeft (scatterLeft v w ω) (scatterRight v w ω) ω = v := by
  change scatterLeft v w ω -
    normalComponent (scatterLeft v w ω) (scatterRight v w ω) ω • ω = v
  rw [normalComponent_scatter v w ω hω]
  simp [scatterLeft, neg_smul]

theorem scatterRight_involutive (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    scatterRight (scatterLeft v w ω) (scatterRight v w ω) ω = w := by
  change scatterRight v w ω +
    normalComponent (scatterLeft v w ω) (scatterRight v w ω) ω • ω = w
  rw [normalComponent_scatter v w ω hω]
  simp [scatterRight, neg_smul]

theorem collisionKernel_scatter (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    collisionKernel (scatterLeft v w ω) (scatterRight v w ω) ω =
      collisionKernel v w ω := by
  simp only [collisionKernel, normalComponent_scatter v w ω hω, abs_neg]

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Admissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The entropy-class solution and nonuniqueness statement

The solution class follows Definition 2.1 with explicit integrability conditions.
The renormalized equation uses derivatives of smooth periodic lifts, while
integrals use volume on the unit torus and Euclidean velocity space.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

/-- Two global solutions of one datum, differing on a common initial interval. -/
def NonuniquenessStatement : Prop :=
  ∃ f₀ : Density, BoundedVelocitySupport f₀ ∧
    ∃ (F G : Evolution) (T : ℝ), AdmissibleGlobal f₀ F ∧ AdmissibleGlobal f₀ G ∧
      StrongEarly T F ∧ StrongEarly T G ∧
      ∃ t ∈ Icc 0 T, ¬(F t =ᵐ[volume] G t)

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CompactParameterConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite separated approximations of compact velocity tests

The approximating algebra consists of finite linear combinations of products
of one-variable continuous tests. This is the compact velocity approximation
used in the cold--hot product passage.
-/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def tensorTest (f : C(X, ℝ)) (g : C(Y, ℝ)) : C(X × Y, ℝ) :=
  ⟨fun p => f p.1*g p.2,(f.continuous.comp continuous_fst).mul
    (g.continuous.comp continuous_snd)⟩

inductive IsTensorSum : C(X × Y, ℝ) → Prop
  | zero : IsTensorSum 0
  | tensor (f : C(X, ℝ)) (g : C(Y, ℝ)) : IsTensorSum (tensorTest f g)
  | add {f g} : IsTensorSum f → IsTensorSum g → IsTensorSum (f+g)
  | smul (r : ℝ) {f} : IsTensorSum f → IsTensorSum (r • f)

theorem IsTensorSum.mul {f g : C(X × Y, ℝ)} (hf : IsTensorSum f) (hg : IsTensorSum g) :
    IsTensorSum (f*g) := by
  induction hf with
  | zero => simpa only [zero_mul] using (IsTensorSum.zero : IsTensorSum (0 : C(X × Y, ℝ)))
  | tensor a b =>
    induction hg with
    | zero => simpa only [mul_zero] using (IsTensorSum.zero : IsTensorSum (0 : C(X × Y, ℝ)))
    | tensor c d =>
      have he : tensorTest a b*tensorTest c d = tensorTest (a*c) (b*d) := by
        ext p
        change (a p.1*b p.2)*(c p.1*d p.2) = (a p.1*c p.1)*(b p.2*d p.2)
        ring
      rw [he]
      exact IsTensorSum.tensor _ _
    | add _ _ ih₁ ih₂ => simpa only [mul_add] using IsTensorSum.add ih₁ ih₂
    | smul r _ ih => simpa only [mul_smul_comm] using IsTensorSum.smul r ih
  | add _ _ ih₁ ih₂ => simpa only [add_mul] using IsTensorSum.add ih₁ ih₂
  | smul r _ ih => simpa only [smul_mul_assoc] using IsTensorSum.smul r ih

def tensorAlgebra (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    Subalgebra ℝ C(X × Y, ℝ) where
  carrier := {f | IsTensorSum f}
  zero_mem' := IsTensorSum.zero
  add_mem' := IsTensorSum.add
  mul_mem' := IsTensorSum.mul
  one_mem' := by
    change IsTensorSum (1 : C(X × Y, ℝ))
    convert IsTensorSum.tensor (1 : C(X, ℝ)) (1 : C(Y, ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [tensorTest]
  algebraMap_mem' r := by
    change IsTensorSum ((algebraMap ℝ C(X × Y, ℝ)) r)
    convert IsTensorSum.tensor (ContinuousMap.const X r) (1 : C(Y, ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [tensorTest]

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SupportedTensorConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform approximation by products of compactly supported velocity tests -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

inductive IsSupportedTensorSum : C(X × Y, ℝ) → Prop
  | zero : IsSupportedTensorSum 0
  | tensor (f : C(X, ℝ)) (g : C(Y, ℝ))
      (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
      IsSupportedTensorSum (tensorTest f g)
  | add {f g} : IsSupportedTensorSum f → IsSupportedTensorSum g → IsSupportedTensorSum (f+g)
  | smul (r : ℝ) {f} : IsSupportedTensorSum f → IsSupportedTensorSum (r • f)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

instance sphereArea_isFiniteMeasure : IsFiniteMeasure sphereArea := by
  unfold sphereArea
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness

end

end

section

/-! # Continuous compact pair kernels for the physical outgoing angular law -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Compactness

def angularPostTest (φ : C(Velocity,ℝ)) (p : Velocity × Velocity) : ℝ :=
  ∫ ω : Sphere, collisionKernel p.1 p.2 ω*φ (scatterLeft p.1 p.2 ω) ∂sphereArea

theorem angularPostTest_continuous (φ : C(Velocity,ℝ)) : Continuous (angularPostTest φ) := by
  have hc : Continuous (fun z : (Velocity × Velocity) × Sphere =>
      collisionKernel z.1.1 z.1.2 z.2*φ (scatterLeft z.1.1 z.1.2 z.2)) := by
    unfold collisionKernel scatterLeft normalComponent
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := sphereArea)
    (f := fun p : Velocity × Velocity => fun ω : Sphere =>
      collisionKernel p.1 p.2 ω*φ (scatterLeft p.1 p.2 ω)) hc isCompact_univ
  change Continuous (fun p : Velocity × Velocity =>
    ∫ ω : Sphere, collisionKernel p.1 p.2 ω*φ (scatterLeft p.1 p.2 ω) ∂sphereArea)
  simpa only [Measure.restrict_univ] using h

def angularPostCutoffTest (η φ : C(Velocity,ℝ)) : C(Velocity × Velocity,ℝ) :=
  ⟨fun p => (η p.1*η p.2)*angularPostTest φ p,
    ((η.continuous.comp continuous_fst).mul (η.continuous.comp continuous_snd)).mul
      (angularPostTest_continuous φ)⟩

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LossIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrability of the original hard-sphere loss integral -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem collisionKernel_le_norm (v w : Velocity) (ω : Sphere) :
    collisionKernel v w ω ≤ ‖v - w‖ := by
  have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simpa only [collisionKernel, normalComponent, hω, mul_one] using
    abs_real_inner_le_norm (v - w) (ω : Velocity)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_ColoredDifferenceAlgebra
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The symmetric gain and colored collision algebra

The symmetric bilinear gain is defined from the paper's exact angular kernel.
Integral additivity carries integrability hypotheses. The resulting algebra
combines the cold and hot collision equations.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness

def gainPairMeasure : Measure (Velocity × Sphere) :=
  (volume : Measure Velocity).prod sphereArea

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The monotone implicit axial flow

The cold jet profile in Section 4 of the supplied manuscript is
`σ + α * tanh (γ * z / s)`. Its characteristic map is expanding,
giving a unique implicit velocity at every nonnegative time. The proof uses
continuity, the intermediate value theorem, and monotonicity. No differentiability or
unproved kinetic estimate is assumed.
-/

noncomputable section

open Set Function

namespace BoltzmannNonuniqueness.AxialFlow

/-- The initial axial velocity at scale `s`. -/
def profile (σ α γ s z : ℝ) : ℝ := σ + α * Real.tanh (γ * z / s)

/-- The spatial position at time `t` of a characteristic starting from `z`. -/
def characteristic (σ α γ s t z : ℝ) : ℝ := z + t * profile σ α γ s z

/-- The residual of the implicit velocity equation at the proposed velocity `u`. -/
def residual (σ α γ s t z u : ℝ) : ℝ :=
  u - profile σ α γ s (z - t * u)

theorem tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  apply (Real.artanh_le_artanh_iff
    ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
    ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩).mp
  simpa only [Real.artanh_tanh] using hxy

theorem tanh_continuous : Continuous Real.tanh := by
  change Continuous (fun z : ℝ => Real.tanh z)
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun z => (Real.cosh_pos z).ne')

theorem continuous_profile (σ α γ s : ℝ) : Continuous (profile σ α γ s) := by
  unfold profile
  exact continuous_const.add (continuous_const.mul
    (tanh_continuous.comp ((continuous_const.mul continuous_id).div_const s)))

theorem profile_monotone {σ α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) :
    Monotone (profile σ α γ s) := by
  intro x y hxy
  have h := tanh_monotone
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hγ) hs.le)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h hα)

theorem profile_sub_center_le {σ α γ s z : ℝ} (hα : 0 ≤ α) :
    |profile σ α γ s z - σ| ≤ α := by
  simp only [profile, add_sub_cancel_left, abs_mul, abs_of_nonneg hα]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one (γ * z / s)).le hα

theorem continuous_residual (σ α γ s t z : ℝ) : Continuous (residual σ α γ s t z) := by
  unfold residual
  exact continuous_id.sub ((continuous_profile σ α γ s).comp
    (continuous_const.sub (continuous_const.mul continuous_id)))

/-- The characteristic map expands ordered distances by at least one. -/
theorem characteristic_sub_ge {σ α γ s t x y : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (hxy : x ≤ y) :
    y - x ≤ characteristic σ α γ s t y - characteristic σ α γ s t x := by
  have hp := profile_monotone (σ := σ) hα hγ hs hxy
  have hp' := mul_le_mul_of_nonneg_left hp ht
  dsimp only [characteristic]
  linarith

theorem characteristic_strictMono {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    StrictMono (characteristic σ α γ s t) := by
  intro x y hxy
  have h := characteristic_sub_ge (σ := σ) hα hγ hs ht hxy.le
  linarith

/-- The scalar residual expands ordered velocity differences by at least one. -/
theorem residual_sub_ge {σ α γ s t z u v : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (huv : u ≤ v) :
    v - u ≤ residual σ α γ s t z v - residual σ α γ s t z u := by
  have hp := profile_monotone (σ := σ) hα hγ hs
    (show z - t * v ≤ z - t * u by nlinarith)
  dsimp only [residual]
  linarith

theorem residual_strictMono {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    StrictMono (residual σ α γ s t z) := by
  intro u v huv
  have h := residual_sub_ge (σ := σ) (z := z) hα hγ hs ht huv.le
  linarith

/-- The implicit equation has a root between the two extremal axial speeds, even without a
sign restriction on time. Nonnegative time will be used for uniqueness. -/
theorem exists_residual_zero {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    ∃ u ∈ Icc (σ - α) (σ + α), residual σ α γ s t z u = 0 := by
  have hl : residual σ α γ s t z (σ - α) ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left
      (Real.neg_one_lt_tanh (γ * (z - t * (σ - α)) / s)).le hα
    dsimp only [residual, profile]
    linarith
  have hr : 0 ≤ residual σ α γ s t z (σ + α) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.tanh_lt_one (γ * (z - t * (σ + α)) / s)).le hα
    dsimp only [residual, profile]
    linarith
  exact intermediate_value_Icc (by linarith : σ - α ≤ σ + α)
    (continuous_residual σ α γ s t z).continuousOn ⟨hl, hr⟩

/-- The implicit velocity selected by the inverse of the residual. Its defining equation and
uniqueness are proved below under the physical parameter restrictions. -/
def velocity (σ α γ s t z : ℝ) : ℝ := invFun (residual σ α γ s t z) 0

theorem velocity_spec {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    velocity σ α γ s t z = profile σ α γ s (z - t * velocity σ α γ s t z) := by
  obtain ⟨u, _, hu⟩ := exists_residual_zero (σ := σ) (γ := γ) (s := s)
    (t := t) (z := z) hα
  exact sub_eq_zero.mp (invFun_eq ⟨u, hu⟩)

theorem velocity_unique {σ α γ s t z u : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (hu : u = profile σ α γ s (z - t * u)) : u = velocity σ α γ s t z := by
  apply (residual_strictMono hα hγ hs ht).injective
  exact (sub_eq_zero.mpr hu).trans (sub_eq_zero.mpr (velocity_spec hα)).symm

theorem velocity_sub_center_le {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    |velocity σ α γ s t z - σ| ≤ α := by
  rw [velocity_spec hα]
  exact profile_sub_center_le hα

/-- The inverse characteristic map is 1-Lipschitz in the spatial coordinate. -/
theorem characteristic_inverse_lipschitz {σ α γ s t x y : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |x - y| ≤ |characteristic σ α γ s t x - characteristic σ α γ s t y| := by
  rcases le_total x y with hxy | hyx
  · have hd := characteristic_sub_ge (σ := σ) hα hγ hs ht hxy
    have hf := (characteristic_strictMono (σ := σ) hα hγ hs ht).monotone hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hf)]
    linarith
  · have hd := characteristic_sub_ge (σ := σ) hα hγ hs ht hyx
    have hf := (characteristic_strictMono (σ := σ) hα hγ hs ht).monotone hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr hf)]
    exact hd

/-- The initial spatial coordinate of the characteristic passing through `(t,z)`. -/
def foot (σ α γ s t z : ℝ) : ℝ := z - t * velocity σ α γ s t z

theorem characteristic_foot {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    characteristic σ α γ s t (foot σ α γ s t z) = z := by
  have hu := velocity_spec (σ := σ) (γ := γ) (s := s) (t := t) (z := z) hα
  dsimp only [characteristic, foot]
  rw [← hu]
  ring

/-- Spatial separation does not increase when characteristics are traced backwards. -/
theorem foot_lipschitz {σ α γ s t z w : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |foot σ α γ s t z - foot σ α γ s t w| ≤ |z - w| := by
  have h := characteristic_inverse_lipschitz (σ := σ) (x := foot σ α γ s t z)
    (y := foot σ α γ s t w) hα hγ hs ht
  simpa only [characteristic_foot hα] using h

theorem foot_lipschitzWith {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    LipschitzWith 1 (foot σ α γ s t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (foot_lipschitz (σ := σ) (z := z) (w := w) hα hγ hs ht)

end BoltzmannNonuniqueness.AxialFlow

end

end

section

/-!
# Singular line integrals in the Carleman slice bound

For `q > 1`, the one-dimensional slice of the transverse power singularity
is integrable away from the line through the axis and has exactly the
power `|A|^(1-q)` appearing in Section 3, equation `ker:line-integral`.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AxialSlices

def lineProfile (q s : ℝ) : ℝ := (1 + s ^ 2) ^ (-q / 2)

def lineConstant (q : ℝ) : ℝ := ∫ s : ℝ, lineProfile q s

end BoltzmannNonuniqueness.AxialSlices

end

end

section

/-! # Uniform collapse of the implicit axial profile at small scales

This is the small-scale part of the characteristic-matching lemma in §8.
An interior profile value must approach z/t; the remaining values are close
to one of the two endpoint speeds. The bound is uniform in z and the center.
-/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.AxialFlow

def interiorArgumentBound (c : ℝ) : ℝ :=
  max |Real.artanh (-c)| |Real.artanh c|

end BoltzmannNonuniqueness.AxialFlow

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.UnifIntegrableCompat
/-!
# Uniform integrability compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. The two disagree on uniform integrability:

* `d13f23b`'s `UnifIntegrable f p μ` is `Tendsto (fun ε ↦ ⨆ i s (_ : μ s ≤ ε), eLpNorm (f i) p
  (μ.restrict s)) (𝓝 0) (𝓝 0)` (extended-real `ε`, `δ`, any set `s`); `0df444a`'s is the real
  `ε`-`δ` form over measurable sets with `eLpNorm (s.indicator (f i)) p μ`.
* `d13f23b`'s `UniformIntegrable f p μ` has two components, `UnifIntegrable f p μ` and a uniform
  bound; `0df444a`'s has three, measurability first. In `d13f23b` the bound alone gives
  measurability, since there `eLpNorm` is `∞` on a function that is not a.e. strongly measurable.
* `d13f23b`'s `UnifTight` takes `ε : ℝ≥0∞`; `0df444a`'s takes `ε : ℝ≥0`.

So that ported proofs keep `d13f23b`'s shapes (`obtain ⟨hu, C, hC⟩ := hf`, `intro ε hε` with
`ε : ℝ≥0∞`, `hu.ae_mono`, `hu.comp`), this file declares `OAI.UnifIntegrable`,
`OAI.UniformIntegrable` and `OAI.UnifTight`, which shadow Mathlib's inside `namespace OAI`, with
`d13f23b`'s API under `d13f23b`'s names, proved from `0df444a`'s. `OAI.UnifIntegrable` carries the
measurability of every member (Mathlib's `UnifIntegrable` together with it), so that
`OAI.UniformIntegrable` keeps `d13f23b`'s two components and is equivalent to Mathlib's
`UniformIntegrable` (`OAI.uniformIntegrable_iff_mathlib`).

`d13f23b`'s `unifIntegrable_iff` and `unifIntegrable_iff'` cannot be stated as equivalences here
(the right sides do not give measurability): the port rewrites their `mp` direction to
`OAI.UnifIntegrable.enn_spec` / `enn_spec'` and their `mpr` direction to
`OAI.UnifIntegrable.of_enn` / `of_enn'`, which take the measurability as a second argument.
-/

noncomputable section UnifIntegrableCompat

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace OAI

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {p : ℝ≥0∞} {f g : ι → α → β}

/-- Uniform integrability in the measure theory sense, with the measurability of each member
(`d13f23b`'s `UnifIntegrable`, whose `eLpNorm` bounds carry it). -/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  MeasureTheory.UnifIntegrable f p μ ∧ ∀ i, AEStronglyMeasurable (f i) μ

/-- Uniform integrability in the probability sense, in `d13f23b`'s two-component shape. -/
def UniformIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  UnifIntegrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, eLpNorm (f i) p μ ≤ C

/-- Uniform tightness with an extended-real `ε` (`d13f23b`'s `UnifTight`). -/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ε > 0, ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

@[aesop 50% apply (rule_sets := [Measurable])]
protected theorem aestronglyMeasurable (hf : UnifIntegrable f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ :=
  hf.2 i

end UnifIntegrable

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

@[aesop 50% apply (rule_sets := [Measurable])]
protected theorem aestronglyMeasurable (hf : UniformIntegrable f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ :=
  hf.1.2 i

end UniformIntegrable


/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published analytic input for periodic hard-sphere nonuniqueness

`GLPS1988Proposition3` expresses the velocity-localized, time-dependent specialization of Proposition 3
of F. Golse, P.-L. Lions, B. Perthame and R. Sentis, "Regularity of the moments of the solution of
a transport equation", J. Functional Analysis 76 (1988), 110–125, pp. 115–116,
DOI: 10.1016/0022-1236(88)90051-1. The passage to evolution equations is explained in their
Remark (2), p. 119. In their notation, the velocity measure is supported on velocities `(1,v)`;
compact velocity support supplies their nonconcentration condition (2.14).

This compactness statement applies to uniformly integrable sources with bounded velocity
support, independently of the cap and branching constructions.

The global continuation input is Theorem 4.1 of C. D. Levermore and N. Masmoudi,
"From the Boltzmann equation to an incompressible Navier–Stokes–Fourier system",
Arch. Rational Mech. Anal. 196 (2010), 753–809, pp. 765–767,
DOI: 10.1007/s00205-009-0254-5. The elementary entropy estimate converts that
continuation theorem to separate gain and loss integrability.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

abbrev Velocity := EuclideanSpace ℝ (Fin 3)
abbrev SpaceTime := ℝ × Velocity
abbrev KineticPhase := SpaceTime × Velocity

/-! ## Scalar estimates in the reference branching process

The uniform distribution of a spherical coordinate gives a lower bound for
retention in the speed-five ball and a positive branching potential.
-/

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceCollisionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The hard-sphere offspring sphere and reference collision rate

The one-child sphere law gives geometric identities for conservation of
momentum and energy, and bounds for the two-beam collision frequency.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev V := EuclideanSpace ℝ (Fin 3)

/-- One child on the sphere having the two incident velocities as diameter endpoints. -/
def child (v w n : V) : V := (1 / 2 : ℝ) • (v + w) + (‖v - w‖ / 2) • n

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The normalized outgoing-sphere kernel for reference collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def sphereProbability : Measure Sphere := (ENNReal.ofReal (4*Real.pi))⁻¹ • sphereArea

def outgoing : Kernel (V × V) V :=
  (Kernel.id ×ₖ Kernel.const (V × V) sphereProbability).map
    (fun z => child z.1.1 z.1.2 z.2.1)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The transverse collision point used in the three-collision minorization -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def firstAxis : V := EuclideanSpace.single 0 1
def secondAxis : V := EuclideanSpace.single 1 1
def beamAxis : V := EuclideanSpace.single 2 1
def minorizationNormal : V := -(Real.sqrt 2)⁻¹ • (firstAxis+beamAxis)

theorem axis_norms : ‖firstAxis‖ = 1 ∧ ‖secondAxis‖ = 1 ∧ ‖beamAxis‖ = 1 := by
  simp [firstAxis,secondAxis,beamAxis,EuclideanSpace.single,PiLp.norm_single]

theorem first_beam_inner : inner ℝ firstAxis beamAxis = 0 := by
  simp [firstAxis,beamAxis,EuclideanSpace.inner_single_left,EuclideanSpace.single]

theorem first_beam_norms : ‖firstAxis+beamAxis‖ = Real.sqrt 2 ∧
    ‖firstAxis-beamAxis‖ = Real.sqrt 2 := by
  have hp : ‖firstAxis+beamAxis‖^2 = 2 := by
    rw [norm_add_sq_real,axis_norms.1,axis_norms.2.2,first_beam_inner]
    norm_num
  have hm : ‖firstAxis-beamAxis‖^2 = 2 := by
    rw [norm_sub_sq_real,axis_norms.1,axis_norms.2.2,first_beam_inner]
    norm_num
  constructor
  · exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hp)
  · exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hm)

theorem minorizationNormal_norm : ‖minorizationNormal‖ = 1 := by
  rw [minorizationNormal,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num)),first_beam_norms.1]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityFourierMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Decay and continuity of the localized transport multiplier -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def velocityMultiplier (n : ℕ) (k : SpaceTime) (v : Velocity) : ℝ :=
  (1+((n : ℝ)*(k.1+inner ℝ k.2 v))^2)⁻¹

def velocityMultiplierMass (R : ℝ) (n : ℕ) (k : SpaceTime) : ℝ :=
  ∫ v in Metric.closedBall (0 : Velocity) R, velocityMultiplier n k v

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The complex resolvent multiplier and its exact squared norm -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def complexVelocityMultiplier (n : ℕ) (k : SpaceTime) (v : Velocity) : ℂ :=
  (1+Complex.I*(n : ℂ)*(k.1+inner ℝ k.2 v))⁻¹

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpacetimeFourierCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hilbert coordinates for the evolution transport Fourier transform -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

abbrev FourierSpace := WithLp 2 SpaceTime

def characteristicDirection (v : Velocity) : FourierSpace := WithLp.toLp 2 (1,v)

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The transverse singularity in the velocity majorant

Section 3 uses `H(v) = exp(-‖v‖²) * ⟨v⟩^(-100) * (1 + ‖v̄‖^(-q))`.
Thus its polynomial factor is `(1 + ‖v‖²)^(-50)`. The values assigned on
the velocity axis use Mathlib's real-power convention and do not affect
Lebesgue integrability.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.VelocityWeight

abbrev Transverse := EuclideanSpace ℝ (Fin 2)

def transverse (v : Velocity) : Transverse :=
  WithLp.toLp 2 (fun i : Fin 2 => v i.castSucc)

def axial (v : Velocity) : ℝ := v (Fin.last 2)

def singularity (q : ℝ) (u : Transverse) : ℝ := ‖u‖ ^ (-q)

def H (q : ℝ) (v : Velocity) : ℝ :=
  Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) *
    (1 + singularity q (transverse v))

/-- The coordinate split is first axial, then transverse. -/
def split : Velocity ≃ᵐ (ℝ × Transverse) :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))

theorem split_apply (v : Velocity) : split v = (axial v, transverse v) := by
  apply Prod.ext
  · rfl
  · apply (WithLp.ext_iff 2).mpr
    funext i
    change v ((Fin.last 2).succAbove i) = v i.castSucc
    rw [Fin.succAbove_last]

theorem split_measurePreserving : MeasurePreserving split := by
  have h₁ := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin 2))
  exact (h₁.trans h₂).trans h₃

theorem norm_sq_split (v : Velocity) :
    ‖v‖ ^ 2 = ‖transverse v‖ ^ 2 + (axial v) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [transverse, axial, PiLp.toLp_apply]
  exact Fin.sum_univ_castSucc (fun i : Fin 3 => v i ^ 2)

end BoltzmannNonuniqueness.VelocityWeight

end

end

section

/-! # Plancherel energy for the partial Fourier transform in spacetime -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

def velocityFourier (r : Velocity × FourierSpace → ℂ) (p : Velocity × FourierSpace) : ℂ :=
  𝓕 (fun x => r (p.1,x)) p.2


attribute [local irreducible] velocityFourier

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Transverse collision-line coordinates

An orthonormal line chart gives the regular and singular terms in the
geometric slice estimate of Section 3. The singular distance is assumed
nonzero here; the product-measure argument must remove its null exceptional set.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialSlices

namespace BoltzmannNonuniqueness.TransverseLine

def quarterTurn (e : Transverse) : Transverse := WithLp.toLp 2 ![-e 1, e 0]

def line (e : Transverse) (D s : ℝ) : Transverse := D • e + s • quarterTurn e

def lineWeight (q : ℝ) (e : Transverse) (D s : ℝ) : ℝ :=
  1 + ‖line e D s‖ ^ (-q)

end BoltzmannNonuniqueness.TransverseLine

end

end

section

/-!
# Transverse angular averages

The angular singularity in `ker:transverse-expectation` is integrable when
`q < 2`. Gaussian Cartesian integration and polar coordinates prove this
without choosing a trigonometric chart on the unit circle.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.TransverseAverage

abbrev Circle := sphere (0 : Transverse) 1

def circleArea : Measure Circle := (volume : Measure Transverse).toSphere

def unitAxis : Transverse := EuclideanSpace.single 0 1

def angular (q : ℝ) (e : Transverse) (ω : Circle) : ℝ :=
  |inner ℝ e (ω : Transverse)| ^ (1 - q)

/-- A finite constant depending only on `q`, independent of the direction. -/
def angularMass (q : ℝ) : ℝ :=
  2 * Real.pi + ∫ ω, angular q unitAxis ω ∂circleArea

/-- The degree `-1` kernel in `ker:transverse-expectation`; its value at zero is zero. -/
def kernel (q : ℝ) (e n : Transverse) : ℝ :=
  (1 + |inner ℝ e (‖n‖⁻¹ • n)| ^ (1 - q)) / ‖n‖

def direction (v : Transverse) : Transverse := ‖v‖⁻¹ • v

/-- A single constant works for small disks, large disks, and the atom at zero. -/
def expectationConstant (q : ℝ) : ℝ :=
  2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) + 6 * angularMass q / Real.pi

end BoltzmannNonuniqueness.TransverseAverage

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PlaneChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph chart for a collision plane

The chart records actual three-dimensional velocities. Its displacement
satisfies the collision-plane equation, and the three-dimensional ball
restriction is precisely the transverse-plus-axial restriction used in
the geometric slice estimate. Identifying its measure with the Carleman
plane measure remains a separate change-of-variables theorem.
-/

noncomputable section

open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.PlaneChart

def join (u : Transverse) (z : ℝ) : Velocity := split.symm (z, u)

theorem transverse_join (u : Transverse) (z : ℝ) : transverse (join u z) = u := by
  have h := congrArg Prod.snd (split.apply_symm_apply (z, u))
  simpa only [join, split_apply] using h

theorem axial_join (u : Transverse) (z : ℝ) : axial (join u z) = z := by
  have h := congrArg Prod.fst (split.apply_symm_apply (z, u))
  simpa only [join, split_apply] using h

theorem norm_join_sq (u : Transverse) (z : ℝ) : ‖join u z‖ ^ 2 = ‖u‖ ^ 2 + z ^ 2 := by
  rw [norm_sq_split, transverse_join, axial_join]

theorem transverse_sub (v w : Velocity) : transverse (v - w) = transverse v - transverse w := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  rfl

theorem axial_sub (v w : Velocity) : axial (v - w) = axial v - axial w := rfl

def normal (v p : Velocity) : Transverse := transverse (v - p)

def slope (v p : Velocity) : ℝ := axial (v - p) / ‖normal v p‖

def offset (v p : Velocity) : ℝ := inner ℝ (direction (normal v p)) (transverse v)

def chart (v p : Velocity) (z s : ℝ) : Velocity :=
  join (line (direction (normal v p)) (offset v p - slope v p * z) s) (axial v + z)

end BoltzmannNonuniqueness.PlaneChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DatumBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summable cold-jet datum bounds

Section 4 of the supplied manuscript bounds the mass and energy of each annulus by a constant
times `s_j²`, and its absolute entropy by a constant times `s_j² (1 + |log s_j|)`.
Those scalar bounds are summable for the stated geometric scales, and their tails converge
to zero. Indices start at zero; the manuscript's indices starting at one
are obtained by removing the first term.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.DatumBounds

/-- The annular scale `s₀ exp(-jη)`. -/
def scale (s₀ η : ℝ) (j : ℕ) : ℝ := s₀ * Real.exp (-(j : ℝ) * η)

/-- The summable majorant for the absolute entropy of one annulus. -/
def entropyBound (s₀ η : ℝ) (j : ℕ) : ℝ :=
  scale s₀ η j ^ 2 * (1 + |Real.log (scale s₀ η j)|)

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cold-jet annuli and opposite stripe enlargements

These are the actual spatial masks of Section 4. The geometric scale is
indexed from zero here, representing the manuscript's first positive index.
-/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.DatumBounds

namespace BoltzmannNonuniqueness.JetGeometry

def gapCoefficient (η : ℝ) : ℝ := (Real.exp η - 1) / 16

def jetScale (s₀ η : ℝ) (j : ℕ) : ℝ := scale s₀ η (j + 1)

def enlargementWidth (η s : ℝ) : ℝ := gapCoefficient η / 4 * s ^ 2

def annularCore (η s : ℝ) : Set Transverse :=
  {y | s + gapCoefficient η * s ^ 2 < ‖y‖ ∧
    ‖y‖ < Real.exp η * s - gapCoefficient η * s ^ 2}

def stripe (s : ℝ) (positive : Bool) : Set Transverse :=
  {y | ∃ k : ℤ, ((k : ℝ) + if positive then 0 else 1 / 2) * s ^ 2 < y 0 ∧
    y 0 < ((k : ℝ) + (if positive then 0 else 1 / 2) + 1 / 4) * s ^ 2}

def mask (η s : ℝ) (positive : Bool) : Set Transverse := annularCore η s ∩ stripe s positive

def enlargement (η s : ℝ) (positive : Bool) : Set Transverse :=
  cthickening (enlargementWidth η s) (mask η s positive)

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Pairwise disjoint periodic cold-jet spatial enlargements -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetLattice

abbrev Lattice := Fin 3 → ℤ

structure Label where
  annulus : ℕ
  positive : Bool
  lattice : Lattice
  deriving DecidableEq

def transverseShift (n : Lattice) : Transverse :=
  WithLp.toLp 2 (fun i : Fin 2 => (n i.castSucc : ℝ))

def axialShift (n : Lattice) : ℝ := (n (Fin.last 2) : ℝ)

def spatialEnlargement (s₀ η t : ℝ) (i : Label) : Set Velocity :=
  {x | transverse x - transverseShift i.lattice ∈
      enlargement η (jetScale s₀ η i.annulus) i.positive ∧
    |axial x - axialShift i.lattice| ≤ 1 / 8 + 2 * t + 1 / 16}

end BoltzmannNonuniqueness.JetLattice

end

end

section

/-! # A fixed smooth compactly supported thermal probability kernel -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetThermalKernel

def bump : ContDiffBump (0 : Velocity) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

def J : Velocity → ℝ := bump.normed volume

def bound : ℝ := (∫ v, bump v)⁻¹

end BoltzmannNonuniqueness.JetThermalKernel

end

end

section

/-! # Mass, support and integrability of translated thermal profiles -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel

namespace BoltzmannNonuniqueness.JetThermalLaw

def scaled (d : ℝ) (a : Velocity) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  (d ^ 3)⁻¹ * f (d⁻¹ • (v - a))

def density (d : ℝ) (a : Velocity) : Velocity → ℝ := scaled d a J

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # Absolute-entropy bounds under thermal scaling and translation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetThermalEntropy

def entropy (x : ℝ) : ℝ := x * |Real.log x|

def entropyConstant : ℝ := ∫ w, entropy (J w)

end BoltzmannNonuniqueness.JetThermalEntropy

end

end

section

/-! # The integrable hyperbolic axial weight of the cold datum -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetAxialWeight

/-- The manuscript's `S(ℓ) = sech² ℓ`. -/
def S (x : ℝ) : ℝ := (Real.cosh x)⁻¹ ^ 2

theorem S_pos (x : ℝ) : 0 < S x := by unfold S; positivity

theorem S_le_one (x : ℝ) : S x ≤ 1 := by
  have hc := Real.one_le_cosh x
  have hi : (Real.cosh x)⁻¹ ≤ 1 := (inv_le_one₀ (Real.cosh_pos x)).mpr hc
  unfold S
  nlinarith [inv_nonneg.mpr (Real.cosh_pos x).le]

theorem continuous_S : Continuous S := by
  unfold S
  exact (Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 2

theorem tanh_derivative (x : ℝ) : HasDerivAt Real.tanh (S x) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have he : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 = S x := by
    have hid := Real.cosh_sq_sub_sinh_sq x
    unfold S
    rw [← pow_two, ← pow_two, hid]
    field_simp
  rw [he] at h
  have ht : Real.tanh = fun z => Real.sinh z / Real.cosh z :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [ht]
  exact h

end BoltzmannNonuniqueness.JetAxialWeight

end

end

section

/-! # Uniform mass and centered first moment of the barrier Gaussian -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGaussianMoments

def kernel (b : ℝ) (v : Velocity) : ℝ := Real.exp (-b * ‖v‖ ^ 2)

def mass : ℝ := ∫ v, kernel 1 v
def moment : ℝ := ∫ v : Velocity, ‖v‖ * kernel 1 v

end BoltzmannNonuniqueness.JetGaussianMoments

end

end

section

/-! # Explicit points in both stripe-annulus masks -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetMaskNonempty

def first (s : ℝ) (a : Bool) : ℝ := (if a then 1 / 8 else 5 / 8) * s ^ 2

def radius (η s : ℝ) : ℝ := (s + Real.exp η * s) / 2

def point (η s : ℝ) (a : Bool) : Transverse :=
  WithLp.toLp 2 ![first s a, Real.sqrt ((radius η s) ^ 2 - (first s a) ^ 2)]

end BoltzmannNonuniqueness.JetMaskNonempty

end

end

section

/-! # A uniform Gaussian sum over integer copies in the fundamental cell -/

noncomputable section

open scoped BigOperators

namespace BoltzmannNonuniqueness.JetLatticeGaussian

def exponential (n : ℤ) : ℝ := Real.exp (-|(n : ℝ)|)

def gaussian (b R ξ : ℝ) (n : ℤ) : ℝ :=
  Real.exp (-b * (max (|ξ - (n : ℝ)| - R) 0) ^ 2)

def constant : ℝ := Real.exp 3 * ∑' n : ℤ, exponential n

end BoltzmannNonuniqueness.JetLatticeGaussian

end

end

section

/-! # The three-dimensional integer-copy Gaussian bound -/

noncomputable section

open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetLatticeGaussian

namespace BoltzmannNonuniqueness.JetLatticeProduct

def coordinates : Lattice ≃ ℤ × (ℤ × ℤ) where
  toFun n := (n 0, n 1, n 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

def product (b R : ℝ) (x : Fin 3 → ℝ) (n : Lattice) : ℝ :=
  JetLatticeGaussian.gaussian b R (x 0) (n 0) * JetLatticeGaussian.gaussian b R (x 1) (n 1) * JetLatticeGaussian.gaussian b R (x 2) (n 2)

end BoltzmannNonuniqueness.JetLatticeProduct

end

end

section

/-! # The vanishing stripe period and relative thermal shift -/

noncomputable section

open Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def stripeAtPeriod (p : ℝ) (a : Bool) : Set Transverse :=
  {y | ∃ k : ℤ, ((k:ℝ)+(if a then 0 else 1/2))*p < y 0 ∧
    y 0 < ((k:ℝ)+(if a then 0 else 1/2)+1/4)*p}

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialJointAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Spatial derivatives of the implicit cold-jet flow -/

noncomputable section

open Filter
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialDerivative

def A (α γ s z : ℝ) : ℝ := (α * γ / s) * S (γ * z / s)

theorem A_nonneg {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (z : ℝ) :
    0 ≤ A α γ s z := mul_nonneg (div_nonneg (mul_nonneg hα hγ) hs) (S_pos _).le

theorem profile_derivative (σ α γ s z : ℝ) :
    HasDerivAt (profile σ α γ s) (A α γ s z) z := by
  have h := (tanh_derivative (γ * z / s)).comp z (((hasDerivAt_id z).const_mul γ).div_const s)
  refine ((hasDerivAt_const z σ).add (h.const_mul α)).congr_deriv ?_
  unfold A
  ring

theorem characteristic_derivative (σ α γ s t z : ℝ) :
    HasDerivAt (characteristic σ α γ s t) (1 + t * A α γ s z) z :=
  (hasDerivAt_id z).add ((profile_derivative σ α γ s z).const_mul t)

theorem foot_derivative {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) :
    HasDerivAt (foot σ α γ s t) (1 + t * A α γ s (foot σ α γ s t z))⁻¹ z := by
  apply HasDerivAt.of_local_left_inverse
    (foot_lipschitzWith hα hγ hs ht).continuous.continuousAt
    (characteristic_derivative σ α γ s t (foot σ α γ s t z))
  · have hA := A_nonneg hα hγ hs.le (foot σ α γ s t z)
    positivity
  · exact Eventually.of_forall (fun y => characteristic_foot hα)

theorem velocity_derivative {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z : ℝ) :
    HasDerivAt (velocity σ α γ s t)
      (A α γ s (foot σ α γ s t z) / (1 + t * A α γ s (foot σ α γ s t z))) z := by
  have h := (profile_derivative σ α γ s (foot σ α γ s t z)).comp z
    (foot_derivative hα hγ hs ht z)
  have he : profile σ α γ s ∘ foot σ α γ s t = velocity σ α γ s t :=
    funext (fun _ => (velocity_spec hα).symm)
  rw [he] at h
  simpa only [div_eq_mul_inv] using h

end BoltzmannNonuniqueness.AxialDerivative

end

end

section

/-! # Continuity of the implicit axial flow along free transport -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialTransport

def flightFoot (σ α γ s z v t : ℝ) : ℝ := foot σ α γ s t (z + t * v)

def flightVelocity (σ α γ s z v t : ℝ) : ℝ := velocity σ α γ s t (z + t * v)

theorem velocity_abs_le {σ α γ s t z : ℝ} (hα : 0 ≤ α) :
    |velocity σ α γ s t z| ≤ |σ| + α := by
  have h := velocity_sub_center_le (σ := σ) (γ := γ) (s := s) (t := t) (z := z) hα
  have htri := abs_add_le (velocity σ α γ s t z - σ) σ
  rw [sub_add_cancel] at htri
  linarith

theorem flightFoot_distance {σ α γ s t₀ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht₀ : 0 ≤ t₀) (z v t : ℝ) :
    |flightFoot σ α γ s z v t - flightFoot σ α γ s z v t₀| ≤
      |t - t₀| * (|v| + |σ| + α) := by
  have hi := characteristic_inverse_lipschitz (σ := σ) (t := t₀)
    (x := flightFoot σ α γ s z v t) (y := flightFoot σ α γ s z v t₀) hα hγ hs ht₀
  have he : characteristic σ α γ s t₀ (flightFoot σ α γ s z v t) =
      z + t * v + (t₀ - t) * flightVelocity σ α γ s z v t := by
    unfold characteristic flightFoot flightVelocity foot
    rw [← velocity_spec hα]
    ring
  have he₀ : characteristic σ α γ s t₀ (flightFoot σ α γ s z v t₀) = z + t₀ * v :=
    characteristic_foot hα
  rw [he, he₀] at hi
  have he' : z + t * v + (t₀ - t) * flightVelocity σ α γ s z v t - (z + t₀ * v) =
      (t - t₀) * (v - flightVelocity σ α γ s z v t) := by ring
  rw [he', abs_mul] at hi
  have hu := velocity_abs_le (σ := σ) (γ := γ) (s := s) (t := t) (z := z + t * v) hα
  change |flightVelocity σ α γ s z v t| ≤ |σ| + α at hu
  have htri := abs_sub v (flightVelocity σ α γ s z v t)
  exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))

end BoltzmannNonuniqueness.AxialTransport

end

end

section

/-! # Joint time and position continuity of the implicit axial flow -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AxialFlow

theorem foot_time_space_bound {σ α γ s t₀ z₀ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht₀ : 0 ≤ t₀) (t z : ℝ) :
    |foot σ α γ s t z-foot σ α γ s t₀ z₀| ≤
      |t-t₀| *(|σ|+α)+|z-z₀| := by
  have htime := AxialTransport.flightFoot_distance (σ := σ) hα hγ hs ht₀ z 0 t
  simp only [AxialTransport.flightFoot,zero_add,abs_zero,add_zero,mul_zero] at htime
  have hspace := foot_lipschitz (σ := σ) (z := z) (w := z₀) hα hγ hs ht₀
  calc
    _ ≤ |foot σ α γ s t z-foot σ α γ s t₀ z|+
        |foot σ α γ s t₀ z-foot σ α γ s t₀ z₀| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add htime hspace

theorem foot_joint_continuousAt {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    ContinuousAt (fun p : ℝ × ℝ => foot σ α γ s p.1 p.2) (t,z) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ p : ℝ × ℝ,
      0 ≤ dist (foot σ α γ s p.1 p.2) (foot σ α γ s t z) := fun _ => dist_nonneg
  have hu (p : ℝ × ℝ) :
      dist (foot σ α γ s p.1 p.2) (foot σ α γ s t z) ≤
        |p.1-t| *(|σ|+α)+|p.2-z| := by
    simpa only [Real.dist_eq] using foot_time_space_bound hα hγ hs ht p.1 p.2
  apply squeeze_zero hb hu
  have h₁ := ((continuous_fst.tendsto (t,z)).sub_const t).abs.mul_const (|σ|+α)
  have h₂ := ((continuous_snd.tendsto (t,z)).sub_const z).abs
  simpa only [sub_self,abs_zero,zero_mul,zero_add] using h₁.add h₂

theorem clamped_foot_continuous {σ α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) :
    Continuous (fun p : ℝ × ℝ => foot σ α γ s (max 0 p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hg : ContinuousAt (fun u : ℝ × ℝ => (max 0 u.1,u.2)) p :=
    ((continuous_const.max continuous_fst).prodMk continuous_snd).continuousAt
  have hh : Tendsto (fun u : ℝ × ℝ => foot σ α γ s u.1 u.2)
      (𝓝 (max 0 p.1,p.2)) (𝓝 (foot σ α γ s (max 0 p.1) p.2)) :=
    foot_joint_continuousAt hα hγ hs (le_max_left 0 p.1)
  exact Tendsto.comp hh hg

theorem clamped_velocity_continuous {σ α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) :
    Continuous (fun p : ℝ × ℝ => velocity σ α γ s (max 0 p.1) p.2) := by
  have he : (fun p : ℝ × ℝ => velocity σ α γ s (max 0 p.1) p.2) =
      profile σ α γ s ∘ (fun p : ℝ × ℝ => foot σ α γ s (max 0 p.1) p.2) := by
    funext p
    exact velocity_spec hα
  rw [he]
  exact (continuous_profile σ α γ s).comp (clamped_foot_continuous hα hγ hs)

end BoltzmannNonuniqueness.AxialFlow

end

end

section

/-! # Joint analyticity of the cold flow in scale, time, and position -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialAnalytic

abbrev FlowParameters := (ℝ × ℝ) × ℝ

def jointCharacteristic (σ α γ : ℝ) (p : FlowParameters) : FlowParameters :=
  (p.1, characteristic σ α γ p.1.1 p.1.2 p.2)

def jointFoot (σ α γ : ℝ) (p : FlowParameters) : FlowParameters :=
  (p.1, foot σ α γ p.1.1 p.1.2 p.2)

end BoltzmannNonuniqueness.AxialAnalytic

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarrierKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The exact axial thermal-coordinate map for a free core -/

noncomputable section

open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.JetCoreMap

def axialMap (σ α γ s d t z w : ℝ) : ℝ :=
  d * w + velocity σ α γ s t (z - t * d * w)

def axialInverse (σ α γ s d t z p : ℝ) : ℝ :=
  (p - profile σ α γ s (z - t * p)) / d

def sourceFoot (σ α γ s d t z w : ℝ) : ℝ :=
  foot σ α γ s t (z - t * d * w)

theorem sourceFoot_eq (σ α γ s d t z w : ℝ) :
    sourceFoot σ α γ s d t z w = z - t * axialMap σ α γ s d t z w := by
  unfold sourceFoot foot axialMap
  ring

theorem axialMap_spec {α : ℝ} (hα : 0 ≤ α) (σ γ s d t z w : ℝ) :
    axialMap σ α γ s d t z w = profile σ α γ s (z - t * axialMap σ α γ s d t z w) + d * w := by
  have hu := velocity_spec (σ := σ) (γ := γ) (s := s) (t := t) (z := z - t * d * w) hα
  rw [← sourceFoot_eq]
  change d * w + velocity σ α γ s t (z - t * d * w) =
    profile σ α γ s (z - t * d * w - t * velocity σ α γ s t (z - t * d * w)) + d * w
  rw [← hu]
  ring

theorem inverse_map {α d : ℝ} (hα : 0 ≤ α) (hd : d ≠ 0) (σ γ s t z w : ℝ) :
    axialInverse σ α γ s d t z (axialMap σ α γ s d t z w) = w := by
  unfold axialInverse
  apply (div_eq_iff hd).mpr
  have h := axialMap_spec hα σ γ s d t z w
  linarith

theorem map_inverse {α γ s t d : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (hd : d ≠ 0) (σ z p : ℝ) :
    axialMap σ α γ s d t z (axialInverse σ α γ s d t z p) = p := by
  let w := axialInverse σ α γ s d t z p
  have hw : d * w = p - profile σ α γ s (z - t * p) := by
    dsimp only [w, axialInverse]
    field_simp
  have hu : p - d * w = velocity σ α γ s t (z - t * d * w) := by
    apply velocity_unique hα hγ hs ht
    rw [show z - t * d * w - t * (p - d * w) = z - t * p by ring]
    linarith
  change d * w + velocity σ α γ s t (z - t * d * w) = p
  rw [← hu]
  ring

theorem axialMap_derivative {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    HasDerivAt (axialMap σ α γ s d t z)
      (d / (1 + t * A α γ s (sourceFoot σ α γ s d t z w))) w := by
  have hu := velocity_derivative (σ := σ) hα hγ hs ht (z - t * d * w)
  have hl : HasDerivAt (fun y : ℝ => z - t * d * y) (-(t * d)) w := by
    refine ((hasDerivAt_const w z).sub ((hasDerivAt_id w).const_mul (t * d))).congr_deriv ?_
    simp only [mul_one, zero_sub]
  have h := ((hasDerivAt_id w).const_mul d).add (hu.comp w hl)
  have ha := A_nonneg hα hγ hs.le (sourceFoot σ α γ s d t z w)
  have hden : 1 + t * A α γ s (sourceFoot σ α γ s d t z w) ≠ 0 := by positivity
  refine h.congr_deriv ?_
  · symm
    change d / (1 + t * A α γ s (sourceFoot σ α γ s d t z w)) =
      d * 1 + (A α γ s (sourceFoot σ α γ s d t z w) /
        (1 + t * A α γ s (sourceFoot σ α γ s d t z w))) * -(t * d)
    field_simp [hden]
    ring

def axialHomeomorph {α γ s t d : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (hd : d ≠ 0) (σ z : ℝ) : ℝ ≃ₜ ℝ where
  toFun := axialMap σ α γ s d t z
  invFun := axialInverse σ α γ s d t z
  left_inv := inverse_map hα hd σ γ s t z
  right_inv := map_inverse hα hγ hs ht hd σ z
  continuous_toFun := continuous_iff_continuousAt.mpr fun w =>
    (axialMap_derivative hα hγ hs ht σ d z w).continuousAt
  continuous_invFun := by
    unfold axialInverse
    exact (continuous_id.sub ((continuous_profile σ α γ s).comp
      (continuous_const.sub (continuous_const.mul continuous_id)))).div_const d

end BoltzmannNonuniqueness.JetCoreMap

end

end

section

/-! # The exact one-dimensional core Jacobian and compression bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreJacobian

def jacobian (σ α γ s d t z w : ℝ) : ℝ :=
  d / (1 + t * A α γ s (sourceFoot σ α γ s d t z w))

theorem compression_bound {K s t k S : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (ht : 0 ≤ t)
    (hk : 0 < k) (hS : 0 ≤ S) (hSmax : S ≤ 1) :
    K * S / (s + t * k * S) ≤ (K * max 1 k⁻¹) / (s + t) := by
  have hden : 0 < s + t * k * S := by positivity
  have hsk : 0 < s + t * k := by positivity
  have hst : 0 < s + t := by positivity
  have hfirst : K * S / (s + t * k * S) ≤ K / (s + t * k) := by
    apply (div_le_div_iff₀ hden hsk).mpr
    nlinarith [mul_le_mul_of_nonneg_left hSmax (mul_nonneg hK hs.le)]
  have hmax1 : 1 ≤ max (1 : ℝ) k⁻¹ := le_max_left _ _
  have hmaxk : 1 ≤ max (1 : ℝ) k⁻¹ * k := by
    calc
      1 = k⁻¹ * k := (inv_mul_cancel₀ hk.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hk.le
  have hcover : s + t ≤ max (1 : ℝ) k⁻¹ * (s + t * k) := by
    nlinarith [mul_le_mul_of_nonneg_right hmax1 hs.le, mul_le_mul_of_nonneg_right hmaxk ht]
  apply hfirst.trans
  apply (div_le_div_iff₀ hsk hst).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcover hK]

end BoltzmannNonuniqueness.JetCoreJacobian

end

end

section

/-! # Kinetic exponent in the transported cold-jet barrier -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.AxialTransport

namespace BoltzmannNonuniqueness.JetBarrierKinetic

def compression (σ α γ s z v t : ℝ) : ℝ :=
  A α γ s (flightFoot σ α γ s z v t) / (1 + t * A α γ s (flightFoot σ α γ s z v t))

def squaredError (σ α γ s z : ℝ) (v : Velocity) (t : ℝ) : ℝ :=
  ‖transverse v‖ ^ 2 + (axial v - flightVelocity σ α γ s z (axial v) t) ^ 2

end BoltzmannNonuniqueness.JetBarrierKinetic

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FiveGainRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The explicit nondegenerate five-collision configuration

These algebraic witnesses allow arbitrary axial cold velocities. The first
three increments are independent; after the fourth increment the final two
collision normals are not parallel. Derivative and analytic-null-set arguments
are separate from these algebraic statements.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

abbrev V := Fin 3 → ℝ

def transverseSquare (R : ℝ) : ℝ := (R+1)^2+(1-R)^2

def smallFactor (R b : ℝ) : ℝ := (2*(1+b^2+transverseSquare R))⁻¹

def first : V := ![0,1,0]
def second (R : ℝ) : V := ![1,-R,0]
def third (R b : ℝ) : V :=
  ![-smallFactor R b*b*(R+1),-smallFactor R b*b*(1-R),
    smallFactor R b*transverseSquare R]

def afterThirdX (R b : ℝ) : ℝ := (1-smallFactor R b*b)*(R+1)
def afterThirdY (R b : ℝ) : ℝ := (1-smallFactor R b*b)*(1-R)

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # The actual recursive five-gain characteristic map -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialAnalytic

namespace BoltzmannNonuniqueness.FiveGainMap

abbrev V := Fin 3 → ℝ
abbrev State := ℝ × (V × V)
abbrev Parameters := (Fin 5 → ℝ) × (Fin 5 → V)

def axis (a : ℝ) : V := ![0,0,a]

def step (σ α γ s t : ℝ) (L : V) (z : State) : State :=
  let x := z.2.1-(z.1-t) • z.2.2
  let n := z.2.2-axis (velocity σ α γ s t (x 2))
  (t,x,z.2.2+n ⨯₃ L)

/-- Only the first five stages change the state. -/
def path (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) : ℕ → State
  | 0 => z
  | k+1 => if h : k < 5 then
      step (σ ⟨k,h⟩) α γ (s ⟨k,h⟩) (q.1 ⟨k,h⟩) (q.2 ⟨k,h⟩)
        (path σ s α γ z q k)
    else path σ s α γ z q k

def map (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) : State :=
  path σ s α γ z q 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The thermal collision map, including the zero-width limit -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialAnalytic

namespace BoltzmannNonuniqueness.FiveGainMap

def thermalCenter (σ α γ s d t : ℝ) (x w : V) : V :=
  ![d*w 0,d*w 1,JetCoreMap.axialMap σ α γ s d t (x 2) (w 2)]

def thermalStep (σ α γ s d t : ℝ) (L w : V) (z : State) : State :=
  let x := z.2.1-(z.1-t) • z.2.2
  (t,x,z.2.2+(z.2.2-thermalCenter σ α γ s d t x w) ⨯₃ L)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Joint analytic dependence of the five thermal collision steps -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

abbrev ThermalEnvironment := (Fin 5 → ℝ) × ((Fin 5 → ℝ) × State)
abbrev ThermalControls := Parameters × (Fin 5 → V)
abbrev ThermalInput := ThermalEnvironment × ThermalControls

def thermalPath (σ : Fin 5 → ℝ) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) : ℕ → State
  | 0 => env.2.2
  | k+1 => if h : k < 5 then
      thermalStep (σ ⟨k,h⟩) α γ (env.1 ⟨k,h⟩) (env.2.1 ⟨k,h⟩)
        (q.1.1 ⟨k,h⟩) (q.1.2 ⟨k,h⟩) (q.2 ⟨k,h⟩)
        (thermalPath σ α γ env q k)
    else thermalPath σ α γ env q k

def thermalMap (σ : Fin 5 → ℝ) (α γ : ℝ) (p : ThermalInput) : State :=
  thermalPath σ α γ p.1 p.2 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact C1 convergence of the actual thermal five-gain maps -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalMap

abbrev PositiveEnvironment := {e : ThermalEnvironment // ∀ i, 0 < e.1 i}

def controlDerivative (σ : Fin 5 → ℝ) (α γ : ℝ) (p : ThermalInput) :
    ThermalControls →L[ℝ] State :=
  (fderiv ℝ (thermalMap σ α γ) p).comp (ContinuousLinearMap.inr ℝ _ _)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact reduction of the five-gain map at equal collision times -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.FiveGainMap

def velocityStep (a : ℝ) (L v : V) : V := v+(v-axis a) ⨯₃ L

def velocityPath (a : Fin 5 → ℝ) (L : Fin 5 → V) (v : V) : ℕ → V
  | 0 => v
  | k+1 => if h : k < 5 then velocityStep (a ⟨k,h⟩) (L ⟨k,h⟩)
      (velocityPath a L v k) else velocityPath a L v k

def commonPosition (τ : ℝ) (z : State) : V := z.2.1-(z.1-τ) • z.2.2

def equalTimeSpeeds (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State) : Fin 5 → ℝ :=
  fun i => velocity (σ i) α γ (s i) τ (commonPosition τ z 2)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Position derivatives at the equal-time five-collision configuration -/

noncomputable section

open Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def endPosition (t₀ : ℝ) (x₀ v₀ : W) (t : Fin 5 → ℝ) (v : Fin 4 → W) : W :=
  x₀-(t₀-t 0) • v₀-∑ i : Fin 4, (t i.castSucc-t i.succ) • v i

def positionDirection (v₀ : W) (dt : Fin 5 → ℝ) (v : Fin 4 → W) : W :=
  dt 0 • v₀-∑ i : Fin 4, (dt i.castSucc-dt i.succ) • v i

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # Rotations about the cold velocity axis -/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

def rotationLinear (c s : ℝ) : V →ₗ[ℝ] V where
  toFun v := ![c*v 0-s*v 1,s*v 0+c*v 1,v 2]
  map_add' v w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a v := by
    ext i
    fin_cases i <;> simp <;> ring

def rotation (c s : ℝ) : V →L[ℝ] V := (rotationLinear c s).toContinuousLinearMap

@[simp] theorem rotation_axial (c s : ℝ) (v : V) : rotation c s v 2 = v 2 := rfl

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Covariance of the actual five-gain map under axial rotations -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

def rotateAngles (c s : ℝ) : (Fin 5 → V) →L[ℝ] (Fin 5 → V) :=
  ContinuousLinearMap.pi (fun i => (rotation c s).comp (ContinuousLinearMap.proj i))

def rotateParameters (c s : ℝ) : Parameters →L[ℝ] Parameters :=
  (ContinuousLinearMap.id ℝ (Fin 5 → ℝ)).prodMap (rotateAngles c s)

def rotateState (c s : ℝ) : State →L[ℝ] State :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap ((rotation c s).prodMap (rotation c s))

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The connected positive-time domain of the five-gain map -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.FiveGainMap

def positiveDomain : Set Parameters := {q | ∀ i, 0 < q.1 i}

def timeProjection (i : Fin 5) : Parameters →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Angular parameters realizing the nondegenerate five-collision path -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

def witnessVelocities (R z b : ℝ) : Fin 6 → V :=
  ![![R,0,z], ![R,1,z], ![R+1,1-R,z],
    ![afterThirdX R b,afterThirdY R b,z+smallFactor R b*transverseSquare R],
    ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,
      z+smallFactor R b*transverseSquare R],
    ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,
      z+smallFactor R b*transverseSquare R]]

def witnessNormal (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) : V :=
  witnessVelocities R z (z-a 2) i.castSucc-axis (a i)

def witnessIncrement (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) : V :=
  witnessVelocities R z (z-a 2) i.succ-witnessVelocities R z (z-a 2) i.castSucc

def witnessAngles (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) : V :=
  (-(witnessNormal R z a i ⬝ᵥ witnessNormal R z a i)⁻¹) •
    (witnessNormal R z a i ⨯₃ witnessIncrement R z a i)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The last two angular derivatives of the actual equal-time collision path -/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

def finalVelocity (a₄ a₅ : ℝ) (v₃ L₄ L₅ : V) : V :=
  let v₄ := velocityStep a₄ L₄ v₃
  velocityStep a₅ L₅ v₄

def varyLastTwo (L : Fin 5 → V) (A B : V) (r : ℝ) : Fin 5 → V :=
  ![L 0,L 1,L 2,L 3+r • A,r • B]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Derivative blocks of the actual five-gain map -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

def lastAngularDirection (A B : V) : Parameters := (0,![0,0,0,A,B])

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The first three time directions span all positions at the witness -/

noncomputable section

open Matrix Function
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

def firstTimeDirection (c : V) : Parameters := (![c 0,c 1,c 2,0,0],0)

def witnessPosition (R b : ℝ) (c : V) : V :=
  -(c 0 • first+c 1 • second R+c 2 • third R b)

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RedundantPlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A nonsingular three-dimensional coordinate map for a collision plane

The third coordinate is the coefficient of the normal, rather than distance
along the unit normal. This normalization cancels the length of the normal in
the redundant-parameter density. The transverse normal must be nonzero, just
as in the graph chart used by the actual gain kernel.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

abbrev V := Fin 3 → ℝ

def normSq (n : V) : ℝ := n 0^2+n 1^2+n 2^2

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Bounded redundant parameters for bounded collision increments -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

def normalDensity : ℝ → ℝ≥0∞ := (Icc 0 1).indicator (fun _ => 1)

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanNormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Normal and tangent coordinates for the Carleman change of variables -/
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ENNReal
namespace BoltzmannNonuniqueness.CarlemanCoordinates

abbrev V := Fin 3 → ℝ

def frameMatrix (n : V) (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-n 0, -n 2*n 0/r^2, -n 1/r;
      -n 1, -n 2*n 1/r^2, n 0/r;
      -n 2, 1, 0]

def frame (n : V) (r : ℝ) : V →ₗ[ℝ] V := (frameMatrix n r).toLin'

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weight transfer on a collision plane

The exact Gaussian identity and polynomial transfer turn the normalized
gain weight into the tilted cold measure used in `ker:tilted-kernel`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.VelocityWeight

def W (q : ℝ) (v : Velocity) : ℝ := 1 + singularity q (transverse v)

def tiltConstant : ℝ := Real.exp 1 * (Nat.factorial 50 : ℝ)

end BoltzmannNonuniqueness.VelocityWeight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative Carleman gain

Gamba, Panferov and Villani, *Upper Maxwellian bounds for the spatially
homogeneous Boltzmann equation*, Arch. Ration. Mech. Anal. 194 (2009),
253–282, Appendix C, Lemma 16 and the hard-sphere remark. The author's
preprint https://www.csun.edu/~panferov/research/umb_5.pdf gives the formula
on pp. 23–24. Their hard-sphere rate is `|g|/(4π)` in outgoing-direction
coordinates. Multiplication by `2π` gives the present absolute-normal
kernel and the coefficient `2` below.

The nonnegative measurable form of that identity is expressed in an explicit
plane chart. Its density formulation includes the plane-chart measure
identification and allows arbitrary nonnegative measurable densities.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.PlaneChart
open scoped ENNReal

namespace BoltzmannNonuniqueness

/-- The nonnegative symmetric gain in the original normal-sphere variables. -/
def nonnegativeGain (f g : Velocity → ℝ≥0∞) (v : Velocity) : ℝ≥0∞ :=
  ∫⁻ p : Velocity × Sphere,
    (ENNReal.ofReal (collisionKernel v p.1 p.2) / 2) *
      (f (scatterLeft v p.1 p.2) * g (scatterRight v p.1 p.2) +
        g (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2)) ∂gainPairMeasure

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The loss frequency of the normalized barrier Gaussian -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetGaussianMoments

namespace BoltzmannNonuniqueness.GaussianFrequency

def density (c b d : ℝ) (u : Velocity) (v : Velocity) : ℝ :=
  c * JetThermalLaw.scaled d u (kernel b) v

end BoltzmannNonuniqueness.GaussianFrequency

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainNonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positivity and domination for the original gain integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainOrder

def integrand (f : Velocity → ℝ) (v : Velocity) (p : Velocity × Sphere) : ℝ :=
  collisionKernel v p.1 p.2 * f (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2)

end BoltzmannNonuniqueness.GainOrder

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Measure preservation for a hard-sphere collision

For each fixed unit normal, the pre/post-collisional map is an orthogonal
involution on the six-dimensional velocity-pair space. Its Euclidean norm is
implemented with `WithLp 2`; the final measure statement uses the ordinary
product of the two three-dimensional Lebesgue measures.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- The pre/post-collisional map, with the collision normal fixed. -/
def scatterPair (ω : Velocity) (p : Velocity × Velocity) : Velocity × Velocity :=
  (scatterLeft p.1 p.2 ω, scatterRight p.1 p.2 ω)

theorem scatterPair_involutive (ω : Velocity) (hω : ‖ω‖ = 1) :
    Function.Involutive (scatterPair ω) := by
  intro p
  exact Prod.ext (scatterLeft_involutive p.1 p.2 ω hω)
    (scatterRight_involutive p.1 p.2 ω hω)

/-- The Euclidean velocity-pair space, whose norm squared is total kinetic energy. -/
abbrev EuclideanVelocityPair := WithLp 2 (Velocity × Velocity)

end BoltzmannNonuniqueness

end

end

section

/-! # The relative-speed cutoff used in the finite approximations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCutoff

def rate (b : ℝ) (v w : Velocity) : ℝ := if ‖v - w‖ < b then ‖v - w‖ else 0

def kernel (b : ℝ) (v w : Velocity) (ω : Sphere) : ℝ :=
  if ‖v - w‖ < b then collisionKernel v w ω else 0

def frequency (b : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  2 * Real.pi * ∫ w, rate b v w * f w

def integrand (b : ℝ) (f : Velocity → ℝ) (v : Velocity) (p : Velocity × Sphere) : ℝ :=
  kernel b v p.1 p.2 * f (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2)

def gain (b : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  ∫ p, integrand b f v p ∂((volume : Measure Velocity).prod sphereArea)

end BoltzmannNonuniqueness.CollisionCutoff

end

end

section

/-! # Collision operators respect almost-everywhere representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.CollisionNullSets

def left (p : Velocity × (Velocity × Sphere)) : Velocity := scatterLeft p.1 p.2.1 p.2.2
def right (p : Velocity × (Velocity × Sphere)) : Velocity := scatterRight p.1 p.2.1 p.2.2

end BoltzmannNonuniqueness.CollisionNullSets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDensityMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure-preserving grouping of physical time and phase coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def kineticDensity (F : Evolution) (z : (ℝ × Position) × Velocity) : ℝ :=
  F z.1.1 (z.1.2,z.2)

end BoltzmannNonuniqueness

end

end

section

/-! # Collision representative invariance with space and time parameters -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.KineticCollisionNullSets

variable {X : Type*} [MeasurableSpace X]

def left (p : (X × Velocity) × (Velocity × Sphere)) : X × Velocity :=
  (p.1.1, scatterLeft p.1.2 p.2.1 p.2.2)

def right (p : (X × Velocity) × (Velocity × Sphere)) : X × Velocity :=
  (p.1.1, scatterRight p.1.2 p.2.1 p.2.2)

def gain (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  CollisionCutoff.gain b (fun v => f (p.1, v)) p.2

def frequency (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  CollisionCutoff.frequency b (fun v => f (p.1, v)) p.2

end BoltzmannNonuniqueness.KineticCollisionNullSets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Centered Gaussians as mixtures of uniform disks

The mixing density in Section 3 is `2 a³ / d⁴ * exp (-a²/d²)` on positive
radii. The formulas below retain the ordinary, unnormalized Lebesgue density
of each disk so that the normalization factors remain explicit.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransverseAverage
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.GaussianDiskMixture

def gaussianDensity (d : ℝ) (p : Transverse) : ℝ :=
  (Real.pi * d ^ 2)⁻¹ * Real.exp (-‖p‖ ^ 2 / d ^ 2)

def diskDensity (a : ℝ) (p : Transverse) : ℝ :=
  (ball (0 : Transverse) a).indicator (fun _ => (Real.pi * a ^ 2)⁻¹) p

def mixingDensity (d a : ℝ) : ℝ :=
  2 * a ^ 3 / d ^ 4 * Real.exp (-a ^ 2 / d ^ 2)

def gaussianLaw (d : ℝ) : Measure Transverse :=
  volume.withDensity (fun p => ENNReal.ofReal (gaussianDensity d p))

def uniformDiskLaw (a : ℝ) : Measure Transverse :=
  volume.withDensity (fun p => ENNReal.ofReal (diskDensity a p))

end BoltzmannNonuniqueness.GaussianDiskMixture

end

end

section

/-!
# Gaussian parameter laws for compressed sheets

The probability and exponential-moment assertions in `ker:parameter-sheets`
use only measurable axial maps. Both the original axial Gaussian (variance
`1 / 2`) and the widened Gaussian (variance `1`) satisfy the bounds below.
The collision gain estimate is not assumed or asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace BoltzmannNonuniqueness.GaussianSheets

open Classical in
/-- The axial image law, with variance parameter as in Mathlib's Gaussian. -/
def axialLaw (v : ℝ≥0) (Φ : ℝ → ℝ) : Measure ℝ :=
  if AEMeasurable Φ (gaussianReal 0 v) then (gaussianReal 0 v).map Φ else Measure.dirac 0

instance axialLaw_isProbabilityMeasure (v : ℝ≥0) (Φ : ℝ → ℝ) :
    IsProbabilityMeasure (axialLaw v Φ) := by
  unfold axialLaw
  split_ifs with h
  · exact Measure.isProbabilityMeasure_map h
  · infer_instance

end BoltzmannNonuniqueness.GaussianSheets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_ScalarEntropyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The scalar power singularity in an axial slice

The exponent `r = 1-q` lies between `-1` and `0`. The interval estimate
below is uniform in the location of its singularity. Values at the
single singular point use the real-power convention and are immaterial.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AxialSlices

def scalarConstant (r : ℝ) : ℝ := (2 : ℝ) ^ (-r) * ((2 : ℝ) ^ (-r) + 2 / (r + 1))

end BoltzmannNonuniqueness.AxialSlices

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Degenerate slices and nonnegative singular integrals

The line integral through the velocity axis is infinite. Its exceptional transverse
parameters form an affine line of two-dimensional measure zero. These results keep
that extended value explicit and justify the almost-everywhere scalar estimates,
including products with arbitrary axial probability measures.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GaussianDiskMixture
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness.GeometricSlice

/-- Signed distance of the transverse collision line from the velocity axis. -/
def sliceOffset (v p : Transverse) : ℝ := inner ℝ (direction (v - p)) v

def RegularTransverse (v p : Transverse) : Prop :=
  v - p ≠ 0 ∧ sliceOffset v p ≠ 0

/-- The scalar line singularity retains its infinite value on a zero-distance slice. -/
def extendedPower (q x : ℝ) : ℝ≥0∞ :=
  if x = 0 then ∞ else ENNReal.ofReal (|x| ^ (1 - q))

/-- Extended expectation kernel, infinite on degenerate transverse slices. -/
def extendedKernel (q : ℝ) (v p : Transverse) : ℝ≥0∞ := by
  classical
  exact if RegularTransverse v p then ENNReal.ofReal (kernel q (direction v) (v - p)) else ∞

/-- Integration over the coordinate rectangle; this is an explicit upper bound,
not a definition of the original ball restriction. -/
def rectangleLineMass (q : ℝ) (e : Transverse) (A B m R a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioc a b, ∫⁻ s in Icc (m - R) (m + R),
    ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)

/-- The ball restriction in transverse-line and axial-displacement coordinates. -/
def ballLineRegion (e v : Transverse) (D z R : ℝ) : Set ℝ :=
  {s | ‖TransverseLine.line e D s - v‖ ^ 2 + z ^ 2 ≤ R ^ 2}

def ballLineMass (q : ℝ) (e v : Transverse) (A B R a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioc a b, ∫⁻ s in ballLineRegion e v (A - B * z) z R,
    ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)

def transverseWeight (q : ℝ) (v : Transverse) : ℝ := 1 + ‖v‖ ^ (-q)

def intervalCoefficient (q R ell : ℝ) : ℝ :=
  AxialSlices.lineConstant q * (AxialSlices.scalarConstant (1 - q) *
    (R ^ (q - 1) * ell ^ (2 - q)))

def averagingCoefficient (q R ell r : ℝ) : ℝ :=
  (2 * R * ell + intervalCoefficient q R ell * r ^ (1 - q)) / (1 + r ^ (-q))

/-- The ball-restricted chart integral with factor `1 / (W(v) * ‖v-p‖)`.
Identifying this chart factor with the collision-plane measure is a separate
change-of-variables statement. Degenerate parameters retain the value infinity. -/
def normalizedBallSlice (q : ℝ) (v : Transverse) (t : ℝ) (p : Transverse)
    (alpha R a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if RegularTransverse v p then
    ENNReal.ofReal (1 / (transverseWeight q v * ‖v - p‖)) *
      ballLineMass q (direction (v - p)) v (sliceOffset v p)
        ((t - alpha) / ‖v - p‖) R a b
  else ∞

def geometricConstant (q : ℝ) : ℝ :=
  expectationConstant q * (2 + AxialSlices.lineConstant q * AxialSlices.scalarConstant (1 - q))

def geometricTotalConstant (q : ℝ) : ℝ := (2 + (2 : ℝ) ^ (2 - q)) * geometricConstant q

end BoltzmannNonuniqueness.GeometricSlice

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Probability sheets and their exponential tilts

An elementary sheet is the coordinate pushforward of a centered transverse
Gaussian (or the atom at zero) and an arbitrary axial probability law. The axial
exponential-moment hypothesis is recorded explicitly. All domination statements
below are inequalities of measures, so they also apply to nonnegative kernels.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.SheetMeasures

/-- Coordinates are ordered transverse, then axial. -/
def join : Transverse × ℝ ≃ᵐ Velocity :=
  (MeasurableEquiv.prodComm : Transverse × ℝ ≃ᵐ ℝ × Transverse).trans split.symm

end BoltzmannNonuniqueness.SheetMeasures

end

end

section

/-!
# Geometric and Gaussian bounds for the gain of an elementary sheet

The ball integrals below use the actual three-dimensional collision chart.
The sheet laws may have an atomic transverse component and arbitrary axial
probability laws. No gain bound is included among the hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures

namespace BoltzmannNonuniqueness.SheetGain

def ballRegion (v : Velocity) (R : ℝ) : Set (Velocity × (ℝ × ℝ)) :=
  {y | ‖PlaneChart.chart v y.1 y.2.1 y.2.2 - v‖ ≤ R}

end BoltzmannNonuniqueness.SheetGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ChartPointLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The normalized gain as a measure on chart coordinates

This measure retains the incoming velocity and both plane coordinates. Its
restriction equals the chart gain, so countable shell
estimates concern the full normalized kernel of the manuscript.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

abbrev Coordinates := Velocity × (ℝ × ℝ)

@[fun_prop] theorem measurable_transverse : Measurable transverse := by
  simpa only [Function.comp_def, split_apply] using measurable_snd.comp split.measurable

@[fun_prop] theorem measurable_axial : Measurable axial := by
  simpa only [Function.comp_def, split_apply] using measurable_fst.comp split.measurable

theorem measurable_point (v : Velocity) :
    Measurable (fun y : Coordinates => chart v y.1 y.2.1 y.2.2) := by
  have hn : Measurable (fun p : Velocity => normal v p) :=
    measurable_transverse.comp (measurable_const.sub measurable_id)
  have ha : Measurable (fun p : Velocity => axial (v - p)) :=
    measurable_axial.comp (measurable_const.sub measurable_id)
  have hj : Measurable (fun p : Transverse × ℝ => PlaneChart.join p.1 p.2) :=
    SheetMeasures.join.measurable
  have hf : Measurable (fun y : Coordinates =>
      TransverseLine.line (TransverseAverage.direction (normal v y.1))
        (offset v y.1 - PlaneChart.slope v y.1 * y.2.1) y.2.2) := by
    unfold TransverseLine.line TransverseLine.quarterTurn offset PlaneChart.slope
    unfold TransverseAverage.direction
    fun_prop
  exact hj.comp (hf.prodMk (measurable_const.add (measurable_fst.comp measurable_snd)))

def density (h : Velocity → ℝ≥0∞) (v : Velocity) (y : Coordinates) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (‖normal v y.1‖⁻¹) * h (chart v y.1 y.2.1 y.2.2)

def measure (c : Measure Velocity) (h : Velocity → ℝ≥0∞) (v : Velocity) :
    Measure Coordinates :=
  (c.prod (volume.prod volume)).withDensity (density h v)

def normalizedMeasure (c : Measure Velocity) (q : ℝ) (v : Velocity) : Measure Coordinates :=
  measure c (fun ξ => ENNReal.ofReal (H q ξ / H q v)) v

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Joint measurability of the collision-plane chart and normalized density -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

theorem measurable_joint_point : Measurable (fun p : Velocity × Coordinates =>
    chart p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hj : Measurable (fun p : Transverse × ℝ => PlaneChart.join p.1 p.2) :=
    SheetMeasures.join.measurable
  have hf : Measurable (fun p : Velocity × Coordinates =>
      TransverseLine.line (TransverseAverage.direction (normal p.1 p.2.1))
        (offset p.1 p.2.1-PlaneChart.slope p.1 p.2.1*p.2.2.1) p.2.2.2) := by
    unfold TransverseLine.line TransverseLine.quarterTurn offset PlaneChart.slope
    unfold TransverseAverage.direction normal
    fun_prop
  exact hj.comp (hf.prodMk ((measurable_axial.comp measurable_fst).add
    measurable_snd.snd.fst))

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Pulling the joint chart through a kinetic base projection -/

noncomputable section
open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.ChartKernel
variable {X : Type*} [MeasurableSpace X]

theorem measurable_lifted_point : Measurable (fun p : (X × Velocity) × Coordinates =>
    PlaneChart.chart p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  let f : (X × Velocity) × Coordinates → Velocity × Coordinates := fun p => (p.1.2,p.2)
  have hf : Measurable f := measurable_fst.snd.prodMk measurable_snd
  simpa only [Function.comp_def,f] using measurable_joint_point.comp hf

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform elementary-sheet gain estimates

The incoming exponential tilt and the Gaussian in the companion velocity
are kept separate. All regions below refer to the complete normalized
kernel, including its singular velocity weight.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.UniformGain

def ballBound (q R : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (GeometricSlice.geometricTotalConstant q * R ^ 2)

def radius (v : Velocity) (y : Coordinates) : ℝ :=
  ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖

def shellConstant (q L : ℝ) : ℝ :=
  96 * tiltConstant * GeometricSlice.geometricTotalConstant q * L

end BoltzmannNonuniqueness.UniformGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Summing the normalized sheet kernel

The Gaussian shell estimate yields a finite constant independent of the
transverse width, the axial law, and the output velocity off the axis.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SheetTotal

def shellTerm (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * Real.exp (-(3 / 32) * ((n : ℝ) + 1) ^ 2)

def bound (q L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * ballBound q 2 +
    ∑' n : ℕ, ENNReal.ofReal (shellConstant q L * shellTerm n)

end BoltzmannNonuniqueness.SheetTotal

end

end

section

/-!
# Axial interval bounds for the full sheet kernel

The chart coordinate is shifted by the outgoing axial velocity. The interval
restriction below is therefore exactly a restriction on the incoming axial
velocity, and its bound is uniform over all axial probability laws.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SheetIntervals

def intervalBound (q R ell : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (geometricConstant q * (R * ell + R ^ (q - 1) * ell ^ (2 - q)))

end BoltzmannNonuniqueness.SheetIntervals

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialAtomicSheet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Uniform axial nonconcentration

The small-interval estimate and the vanishing velocity tails give one
modulus for every elementary sheet and every outgoing velocity off the axis.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.SheetIntervals

namespace BoltzmannNonuniqueness.AxialModulus

def axialRegion (v : Velocity) (a b : ℝ) : Set Coordinates :=
  {y | axial (PlaneChart.chart v y.1 y.2.1 y.2.2) ∈ Ioc a b}

def intervalMajorant (q L R ell : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * intervalBound q R ell

end BoltzmannNonuniqueness.AxialModulus

end

end

section

/-! # The limiting axial atoms belong to the proved zero-width sheet class -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AxialAtomicSheet

theorem velocity_abs_le {σ α γ μ t z : ℝ} (hα : 0 ≤ α) :
    |AxialFlow.velocity σ α γ μ t z| ≤ |σ|+α := by
  have h := AxialFlow.velocity_sub_center_le (σ := σ) (γ := γ) (s := μ) (t := t) (z := z) hα
  calc
    _ = |(AxialFlow.velocity σ α γ μ t z-σ)+σ| := by congr 1; ring
    _ ≤ |AxialFlow.velocity σ α γ μ t z-σ|+|σ| := abs_add_le _ _
    _ ≤ _ := by linarith

end BoltzmannNonuniqueness.AxialAtomicSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotGainReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Algebraic reduction of the quadratic hot gain

Symmetry allows the output polynomial weight to be assigned to either
incoming velocity. The resulting mixed gain has only one polynomial factor,
while its two Gaussian factors cancel by collision energy conservation.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotWeight

def G (q : ℝ) (v : Velocity) : ℝ := Real.exp (-‖v‖ ^ 2) * W q v

def polynomial (v : Velocity) : ℝ := (1 + ‖v‖ ^ 2) ^ (50 : ℕ)

end BoltzmannNonuniqueness.HotWeight

end

end

section

/-! # Polynomial decay on collision shells

Eight powers suffice after the five-dimensional geometric estimate;
the manuscript's fixed polynomial exponent fifty supplies these powers.
-/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight

namespace BoltzmannNonuniqueness.HotShellWeight

def constant : ℝ := 4 ^ (8 : ℕ) + 4 ^ (4 : ℕ) * Nat.factorial 4

end BoltzmannNonuniqueness.HotShellWeight

end

end

section

/-!
# Reduction of the original quadratic gain to a mixed gain

The reduction is proved in the original collision variables and uses no
additional change-of-variables hypothesis. This retains the bilinear form
covered by the published Carleman identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight

namespace BoltzmannNonuniqueness.HotGainReduction

def coefficient (q : ℝ) (v : Velocity) : ℝ :=
  (2 : ℝ) ^ (51 : ℕ) * (H q v / G q v)

end BoltzmannNonuniqueness.HotGainReduction

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PowerDiskMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The positive disk mixture for the truncated transverse power

The hot-gain estimate uses the finite measure with density
`(1 + ‖p‖⁻ᑫ) 1_{‖p‖ < D}`. Its singular part is a positive radius mixture
of centered disks. Values at the origin are irrelevant for this identity.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.PowerDiskMixture

def cutoffDensity (q D : ℝ) (p : Transverse) : ℝ :=
  (ball (0 : Transverse) D).indicator (fun p => 1 + ‖p‖ ^ (-q)) p

def boundaryMass (q D : ℝ) : ℝ := (1 + D ^ (-q)) * (Real.pi * D ^ 2)

end BoltzmannNonuniqueness.PowerDiskMixture

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotQuadraticGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Normalized truncated transverse weights

The positive disk mixture transfers the existing disk kernel expectation
bound to the truncated singular density needed by the quadratic hot gain.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.PowerDiskMixture

namespace BoltzmannNonuniqueness.HotDiskEstimate

def radiusMass (q D : ℝ) : ℝ := Real.pi * q / (2 - q) * D ^ (2 - q)

def cutoffMass (q D : ℝ) : ℝ := boundaryMass q D + radiusMass q D

def cutoffLaw (q D : ℝ) : Measure Transverse :=
  volume.withDensity (fun p => ENNReal.ofReal (cutoffDensity q D p))

def normalizedCutoff (q D : ℝ) : Measure Transverse :=
  (ENNReal.ofReal (cutoffMass q D))⁻¹ • cutoffLaw q D

end BoltzmannNonuniqueness.HotDiskEstimate

end

end

section

/-!
# Collision-chart bounds for truncated hot weights

The transverse singular density is normalized explicitly. The axial factor is
normalized Lebesgue measure on a bounded interval. This supplies the geometric
ball estimate used in the polynomial shell summation.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotChartBalls

def intervalLaw (D : ℝ) : Measure ℝ := volume.restrict (Ioo (-D) D)

def normalizedInterval (D : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * D))⁻¹ • intervalLaw D

def rectangleLaw (q D : ℝ) : Measure Velocity :=
  ((cutoffLaw q D).prod (intervalLaw D)).map join

def normalizedRectangle (q D : ℝ) : Measure Velocity :=
  ((normalizedCutoff q D).prod (normalizedInterval D)).map join

def massConstant (q : ℝ) : ℝ := 2 * Real.pi + Real.pi * q / (2 - q)

end BoltzmannNonuniqueness.HotChartBalls

end

end

section

/-! # The truncated hot rectangle in physical velocity coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.HotChartBalls

namespace BoltzmannNonuniqueness.HotRectangleDensity

def rectangle (D : ℝ) : Set Velocity :=
  {p | ‖transverse p‖ < D ∧ axial p ∈ Ioo (-D) D}

def weight (q D : ℝ) : Velocity → ℝ≥0∞ :=
  (rectangle D).indicator (fun p => ENNReal.ofReal (W q p))

end BoltzmannNonuniqueness.HotRectangleDensity

end

end

section

/-! # Restricting the mixed hot gain to polynomial shells -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.HotChartBalls
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.HotMixedGain

def mixedMeasure (q : ℝ) (v : Velocity) : Measure Coordinates :=
  ChartKernel.measure (volume.withDensity (fun p => ENNReal.ofReal (H q p)))
    (fun ξ => ENNReal.ofReal (G q ξ / G q v)) v

def core (v : Velocity) : Set Coordinates := {y | radius v y ≤ 2}

end BoltzmannNonuniqueness.HotMixedGain

end

end

section

/-! # Summation of the mixed hot gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.HotChartBalls
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.HotMixedGain
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.HotTotal

def shellConstant (q : ℝ) : ℝ :=
  432 * HotShellWeight.constant * massConstant q * geometricTotalConstant q

def baseBound (q : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (cutoffMass q 3) * ENNReal.ofReal 6) *
    (2 * ENNReal.ofReal (geometricTotalConstant q * 2 ^ (2 : ℕ)))

def bound (q : ℝ) : ℝ≥0∞ := baseBound q +
  ∑' n : ℕ, ENNReal.ofReal (shellConstant q / ((n : ℝ) + 1) ^ (3 : ℕ))

end BoltzmannNonuniqueness.HotTotal

end

end

section

/-!
# The quadratic hot-gain bound

The geometric shell estimates and their summation transfer through the
Carleman identity to the original hard-sphere collision variables.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.HotMixedGain

namespace BoltzmannNonuniqueness.HotApplication

def realBound (q : ℝ) : ℝ :=
  (ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q).toReal + 1

end BoltzmannNonuniqueness.HotApplication

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MixedRealGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real symmetric mixed gain and its nonnegative bounds -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.MixedRealGain

def integrand (f g : Velocity → ℝ) (v : Velocity) (p : Velocity × Sphere) : ℝ :=
  collisionKernel v p.1 p.2 / 2 *
    (f (scatterLeft v p.1 p.2) * g (scatterRight v p.1 p.2) +
      g (scatterLeft v p.1 p.2) * f (scatterRight v p.1 p.2))

def gain (f g : Velocity → ℝ) (v : Velocity) : ℝ :=
  ∫ p, integrand f g v p ∂gainPairMeasure

end BoltzmannNonuniqueness.MixedRealGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual unshifted cold-jet density and its mass bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetPrototype

abbrev Space := Transverse × ℝ
abbrev Phase := Space × Velocity

abbrev spaceVolume : Measure Space := volume.prod volume

def sign (positive : Bool) : ℝ := if positive then 1 else -1

def center (α γ s : ℝ) (positive : Bool) (z : ℝ) : Velocity :=
  PlaneChart.join 0 (AxialFlow.profile (sign positive) α γ s z)

def axialAmplitude (K γ s : ℝ) (z : ℝ) : ℝ :=
  (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (fun z => (K / s) * S (γ * z / s)) z

def spatial (η K γ s : ℝ) (positive : Bool) (x : Space) : ℝ :=
  (mask η s positive).indicator (fun _ => (1 : ℝ)) x.1 * axialAmplitude K γ s x.2

def density (η K α γ s d : ℝ) (positive : Bool) (p : Phase) : ℝ :=
  spatial η K γ s positive p.1 * JetThermalLaw.density d (center α γ s positive p.1.2) p.2

end BoltzmannNonuniqueness.JetPrototype

end

end

section

/-! # Absolute entropy of the cold datum's spatial factor -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetSpatialEntropy

def massConstant : ℝ := ∫ z, S z

def entropyConstant : ℝ := ∫ z, entropy (S z)

def axialMajorant (K γ s z : ℝ) : ℝ :=
  S (γ * z / s) * entropy (K / s) + (K / s) * entropy (S (γ * z / s))

end BoltzmannNonuniqueness.JetSpatialEntropy

end

end

section

/-! # Thermal and distance bounds on actual free cold-core flights -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreFlight

def axialCenter (α γ s t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  AxialFlow.velocity (sign a) α γ s t (p.1.2 + t * axial p.2)

def error (α γ s t : ℝ) (a : Bool) (p : JetPrototype.Phase) : Velocity :=
  p.2 - PlaneChart.join 0 (axialCenter α γ s t a p)

end BoltzmannNonuniqueness.JetCoreFlight

end

end

section

/-! # The actual Gaussian barrier and free-core domination -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetCoreFlight

namespace BoltzmannNonuniqueness.JetBarrier

def centerVelocity (α γ s t : ℝ) (a : Bool) (x : Space) : Velocity :=
  PlaneChart.join 0 (AxialFlow.velocity (sign a) α γ s t x.2)

def distanceSquared (η α γ s t : ℝ) (a : Bool) (x : Space) : ℝ :=
  infDist x.1 (JetGeometry.mask η s a) ^ 2 +
    infDist (AxialFlow.foot (sign a) α γ s t x.2) (Icc (-(1 / 8 : ℝ)) (1 / 8)) ^ 2

def flight (t : ℝ) (p : JetPrototype.Phase) : JetPrototype.Phase :=
  ((p.1.1 + t • transverse p.2, p.1.2 + t * axial p.2), p.2)

def exponent (η α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  t - (2 - t) * ‖p.2 - centerVelocity α γ s t a p.1‖ ^ 2 / d ^ 2 -
    (1 / 8 : ℝ) * distanceSquared η α γ s t a p.1 / (d ^ 2 * t)

def barrier (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ *
    Real.exp (exponent η α γ s d t a p)

end BoltzmannNonuniqueness.JetBarrier

end

end

section

/-! # Self-collision and the uniform loss-frequency bound of the actual barrier -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierCollision

def massScale (η K α γ s d t : ℝ) (a : Bool) (x : Space) : ℝ :=
  (Real.exp 3 * JetThermalKernel.bound) * (K / s) *
    Real.exp (t - (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t))

def frequencyConstant : ℝ :=
  2 * Real.pi * Real.exp 4 * JetThermalKernel.bound *
    (JetGaussianMoments.mass + JetGaussianMoments.moment)

end BoltzmannNonuniqueness.JetBarrierCollision

end

end

section

/-! # Gaussian decay of a cold barrier away from its spatial core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetGaussianEscape

def constant (α : ℝ) : ℝ :=
  Real.exp 4 * JetThermalKernel.bound * Real.exp (8 * (1 + α) ^ 2)

end BoltzmannNonuniqueness.JetGaussianEscape

end

end

section

/-! # Almost-everywhere distance derivatives along the cold-jet flights -/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialTransport

namespace BoltzmannNonuniqueness.JetDistanceDerivative

def transverseDistance (η s : ℝ) (a : Bool) (y w : Transverse) (t : ℝ) : ℝ :=
  infDist (y + t • w) (JetGeometry.mask η s a)

def axialDistance (σ α γ s z v t : ℝ) : ℝ :=
  infDist (flightFoot σ α γ s z v t) (Icc (-(1 / 8 : ℝ)) (1 / 8))

end BoltzmannNonuniqueness.JetDistanceDerivative

end

end

section

/-! # Local mass bounds for the Gaussian cold barrier, uniform in thermal width -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierLocalMass

def massConstant : ℝ := Real.exp 4*JetThermalKernel.bound*JetGaussianMoments.mass

end BoltzmannNonuniqueness.JetBarrierLocalMass

end

end

section

/-! # Arbitrary polynomial decay of the escaped-scale exponential -/

noncomputable section

namespace BoltzmannNonuniqueness.JetEscapePower

def tail (β s t : ℝ) : ℝ := (s ^ 31)⁻¹ * Real.exp (-β / (s ^ 16 * t))

end BoltzmannNonuniqueness.JetEscapePower

end

end

section

/-! # The escaped barrier has the actual s⁻³¹ exp(-β/(s¹⁶t)) tail -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetEscapedBarrier

def rate (η d₀ : ℝ) : ℝ := (gapCoefficient η / 4) ^ 2 / (8 * d₀ ^ 2)

def coefficient (α K d₀ : ℝ) : ℝ := JetGaussianEscape.constant α * K * (d₀ ^ 3)⁻¹

end BoltzmannNonuniqueness.JetEscapedBarrier

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A centered fundamental cube for the periodic spatial variable -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusChart

def coordinate (x : AddCircle (1 : ℝ)) : ℝ :=
  ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) x : ℝ)

def representative (x : Position) : Velocity := WithLp.toLp 2 (fun i => coordinate (x i))

def phaseRepresentative (p : Phase) : Velocity × Velocity := (representative p.1, p.2)

end BoltzmannNonuniqueness.TorusChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integration of spatial weights against the cold thermal kernel -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetWeightedKernel

def weighted (d α γ s : ℝ) (a : Bool) (w : Space → ℝ) (f : Velocity → ℝ)
    (p : JetPrototype.Phase) : ℝ := w p.1 * scaled d (center α γ s a p.1.2) f p.2

end BoltzmannNonuniqueness.JetWeightedKernel

end

end

section

/-! # Absolute entropy of each actual cold-jet prototype -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetWeightedKernel

namespace BoltzmannNonuniqueness.JetPrototypeEntropy

def spatialWeight (η K γ s d : ℝ) (a : Bool) (x : Space) : ℝ :=
  entropy (spatial η K γ s a x) + (3 * |Real.log d|) * spatial η K γ s a x

def majorant (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  weighted d α γ s a (spatialWeight η K γ s d a) J p +
    weighted d α γ s a (spatial η K γ s a) (fun v => entropy (J v)) p

end BoltzmannNonuniqueness.JetPrototypeEntropy

end

end

section

/-! # The scale-uniform, summable cold-jet entropy bound -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetEntropyBound

def spatialConstant (K γ : ℝ) : ℝ :=
  4 * Real.pi * (K / γ) * ((|Real.log K| + 1) * JetSpatialEntropy.massConstant +
    JetSpatialEntropy.entropyConstant)

def constant (K γ d₀ : ℝ) : ℝ := spatialConstant K γ +
  (3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (8 * Real.pi * K / γ)

end BoltzmannNonuniqueness.JetEntropyBound

end

end

section

/-! # A coordinate box lower bound for periodic barrier distances -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetSpatialBox

def shifted (x : Velocity) (n : Lattice) : Space :=
  (transverse x - transverseShift n, axial x - axialShift n)

def gap (x : Velocity) (n : Lattice) (k : Fin 3) : ℝ := max (|x k - (n k : ℝ)| - 1) 0

end BoltzmannNonuniqueness.JetSpatialBox

end

end

section

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

abbrev Index := ℕ × Bool

def term (s₀ η K α γ d₀ : ℝ) (i : Index) : JetPrototype.Phase → ℝ :=
  density η K α γ (jetScale s₀ η i.1) (d₀ * jetScale s₀ η i.1 ^ 10) i.2

def datum (s₀ η K α γ d₀ : ℝ) (p : JetPrototype.Phase) : ℝ :=
  ∑' i : Index, term s₀ η K α γ d₀ i p

end BoltzmannNonuniqueness.JetDatum

end

end

section

/-! # Pointwise stabilization of the annular truncations -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetTruncation

def truncated (s₀ η K α γ d₀ : ℝ) (N : ℕ) (p : JetPrototype.Phase) : ℝ :=
  ∑' i : Index, if i.1 < N then term s₀ η K α γ d₀ i p else 0

end BoltzmannNonuniqueness.JetTruncation

end

end

section

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

@[simp] theorem flight_zero (p : JetPrototype.Phase) : flight 0 p = p := by
  simp only [flight, zero_smul, zero_mul, add_zero, Prod.eta]

def free (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  density η K α γ s d a (flight (-t) p)

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Gaussian summation over the actual periodic-copy distances -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetLatticeTail

def outside (η s t : ℝ) (a : Bool) (x : Velocity) (n : Lattice) : Prop :=
  ¬((shifted x n).1 ∈ enlargement η s a ∧ |(shifted x n).2| ≤ 1 / 8 + 2 * t + 1 / 16)

end BoltzmannNonuniqueness.JetLatticeTail

end

end

section

/-! # A uniform, explicit coefficient for cold-color comparison -/

noncomputable section

open BoltzmannNonuniqueness.JetBarrierCollision

namespace BoltzmannNonuniqueness.JetComparisonCoefficient

def coefficient (K : ℝ) : ℝ := 8 * frequencyConstant * K + 1

end BoltzmannNonuniqueness.JetComparisonCoefficient

end

end

section

/-! # The completed-square estimate for the barrier logarithmic derivative -/

noncomputable section

namespace BoltzmannNonuniqueness.JetBarrierDifferential

def spatialTerm (t y z dy dz : ℝ) : ℝ :=
  (y ^ 2 + z ^ 2) / t ^ 2 - 2 * (y * dy + z * dz) / t

end BoltzmannNonuniqueness.JetBarrierDifferential

end

end

section

/-! # The escaped Gaussian barrier summed over all periodic copies -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedCopies

def halfRate (d t : ℝ) : ℝ := 1 / (16 * d ^ 2 * t)

end BoltzmannNonuniqueness.JetEscapedCopies

end

end

section

/-! # The cold datum on the actual unit spatial torus -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetPeriodicDatum

def spatialMap (x : Velocity) : Space := (transverse x, axial x)

def phaseMap (p : Velocity × Velocity) : JetPrototype.Phase := (spatialMap p.1, p.2)

def pullback (f : JetPrototype.Phase → ℝ) (p : Phase) : ℝ :=
  f (phaseMap (TorusChart.phaseRepresentative p))

def datum (s₀ η K α γ d₀ : ℝ) : Density := pullback (JetDatum.datum s₀ η K α γ d₀)

theorem spatialMap_measurePreserving : MeasurePreserving spatialMap volume spaceVolume := by
  convert Measure.measurePreserving_swap.comp split_measurePreserving using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change (transverse x, axial x) = (split x).swap
  rw [split_apply]
  rfl

theorem phaseMap_measurePreserving : MeasurePreserving phaseMap volume (spaceVolume.prod volume) :=
  spatialMap_measurePreserving.prod (MeasurePreserving.id (volume : Measure Velocity))

end BoltzmannNonuniqueness.JetPeriodicDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetSupersolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The full logarithmic barrier derivative along free flights -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDistanceDerivative
open BoltzmannNonuniqueness.JetBarrierKinetic
open BoltzmannNonuniqueness.JetBarrierDifferential
open BoltzmannNonuniqueness.AxialTransport

namespace BoltzmannNonuniqueness.JetLogDerivative

def Y (η s : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ → ℝ :=
  transverseDistance η s a p.1.1 (transverse p.2)

def Z (α γ s : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ → ℝ :=
  axialDistance (sign a) α γ s p.1.2 (axial p.2)

def rawExponent (η α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) : ℝ :=
  t - (2 - t) * squaredError (sign a) α γ s p.1.2 p.2 t / d ^ 2 -
    ((Y η s a p t ^ 2 + Z α γ s a p t ^ 2) / t) / (8 * d ^ 2)

def logSlope (η α γ s d t dy dz : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  1 + (squaredError (sign a) α γ s p.1.2 p.2 t +
    2 * (2 - t) * compression (sign a) α γ s p.1.2 (axial p.2) t *
      (axial p.2 - flightVelocity (sign a) α γ s p.1.2 (axial p.2) t) ^ 2) / d ^ 2 +
    spatialTerm t (Y η s a p t) (Z α γ s a p t) dy dz / (8 * d ^ 2)

end BoltzmannNonuniqueness.JetLogDerivative

end

end

section

/-! # The differential lower bound for the actual transported Gaussian barrier -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLogDerivative
open BoltzmannNonuniqueness.JetBarrierKinetic

namespace BoltzmannNonuniqueness.JetBarrierDerivative

def along (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) : ℝ :=
  barrier η K α γ s d t a (flight t p)

def amplitude (K s d : ℝ) : ℝ :=
  (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹

end BoltzmannNonuniqueness.JetBarrierDerivative

end

end

section

/-! # The actual free-core plus Gaussian supersolution -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetFreeTransport
open BoltzmannNonuniqueness.JetBarrierCollision
open BoltzmannNonuniqueness.JetComparisonCoefficient

namespace BoltzmannNonuniqueness.JetSupersolution

def epsilon (K s d : ℝ) : ℝ := coefficient K * d / s

def U (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  free η K α γ s d t a p + epsilon K s d * barrier η K α γ s d t a p

def along (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) : ℝ :=
  U η K α γ s d t a (flight t p)

end BoltzmannNonuniqueness.JetSupersolution

end

end

section

/-! # The full velocity measure under the thermal-coordinate map -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreJacobian

namespace BoltzmannNonuniqueness.JetCoreMeasure

def parameterMeasure (σ α γ s d t z : ℝ) : Measure (Transverse × ℝ) :=
  (ENNReal.ofReal (d ^ 2) • (volume : Measure Transverse)).prod
    (volume.withDensity (fun w => ENNReal.ofReal (jacobian σ α γ s d t z w)))

def velocityMap (σ α γ s d t z : ℝ) (w : Transverse × ℝ) : Velocity :=
  PlaneChart.join (d • w.1) (axialMap σ α γ s d t z w.2)

end BoltzmannNonuniqueness.JetCoreMeasure

end

end

section

/-! # The exact compressed density of a transported cold core -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreJacobian
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def compressed (K α γ s t ζ : ℝ) : ℝ :=
  K * S (γ * ζ / s) / (s + t * α * γ * S (γ * ζ / s))

def weight (η K α γ s d t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) : ℝ :=
  (JetGeometry.mask η s a).indicator (fun _ => (1 : ℝ)) (x.1 - t • (d • w.1)) *
    (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (compressed K α γ s t)
      (sourceFoot (sign a) α γ s d t x.2 w.2) * JetThermalKernel.J (SheetMeasures.join w)


theorem compressed_nonneg {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (ζ : ℝ) :
    0 ≤ compressed K α γ s t ζ := by
  unfold compressed
  have := (S_pos (γ * ζ / s)).le
  positivity

theorem compressed_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t) (ζ : ℝ) :
    compressed K α γ s t ζ ≤ (K * max 1 (α * γ)⁻¹) / (s + t) := by
  have h := compression_bound hK hs ht (mul_pos hα hγ)
    (S_pos (γ * ζ / s)).le (S_le_one (γ * ζ / s))
  simpa only [compressed, mul_assoc] using h

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Fixed-scale uniform bounds for the cold envelope -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeBound

def amplitude (K s d : ℝ) : ℝ :=
  Real.exp 4 * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹

def gainAmplitude (K α s d : ℝ) (v : Velocity) : ℝ :=
  (4 * JetBarrierCollision.frequencyConstant * (K / s) * (d + ‖v‖ + (1 + α))) * amplitude K s d

end BoltzmannNonuniqueness.JetEnvelopeBound

end

end

section

/-! # Joint measurability of the transported cold envelope -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetTimeRegularity

def positiveFoot (σ α γ s : ℝ) (p : ℝ × ℝ) : ℝ :=
  AxialFlow.foot σ α γ s (max p.1 0) p.2

def positiveU (η K α γ s d : ℝ) (a : Bool) (p : ℝ × JetPrototype.Phase) : ℝ :=
  JetFreeTransport.free η K α γ s d p.1 a p.2 +
    JetSupersolution.epsilon K s d * JetBarrier.barrier η K α γ s d (max p.1 0) a p.2

end BoltzmannNonuniqueness.JetTimeRegularity

end

end

section

/-! # Gaussian parameter laws for the actual axial core map -/

noncomputable section

open MeasureTheory
open scoped NNReal
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetAxialLaw

def law (σ α γ s d t z : ℝ) : Measure ℝ :=
  GaussianSheets.axialLaw (1 / 2) (axialMap σ α γ s d t z)

end BoltzmannNonuniqueness.JetAxialLaw

end

end

section

/-! # Gaussian product domination in the actual core coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreMeasure

namespace BoltzmannNonuniqueness.JetGaussianProduct

def density (w : Transverse × ℝ) : ℝ :=
  gaussianDensity 1 w.1 * gaussianPDFReal 0 (1 / 2) w.2

def coefficient : ℝ := JetThermalKernel.bound * Real.exp 1 * (Real.pi * Real.sqrt Real.pi)

def parameterLaw : Measure (Transverse × ℝ) :=
  (gaussianLaw 1).prod (gaussianReal 0 (1 / 2))

end BoltzmannNonuniqueness.JetGaussianProduct

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_AnnularEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Disjoint radial annuli and their scale-uniform area bounds -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.AnnularEnvelope

def shell (s₀ η : ℝ) (j : ℕ) : Set Transverse :=
  {y | jetScale s₀ η j < ‖y‖ ∧ ‖y‖ < Real.exp η*jetScale s₀ η j}

def term (s₀ η : ℝ) (j : ℕ) (t : ℝ) (y : Transverse) : ℝ :=
  (shell s₀ η j).indicator (fun _ => 1/(t+jetScale s₀ η j)) y

def finiteEnvelope (s₀ η : ℝ) (s : Finset ℕ) (t : ℝ) (y : Transverse) : ℝ :=
  ∑ j ∈ s, term s₀ η j t y

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # An integrable squared envelope for all finite annular truncations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.AnnularEnvelope

def timeSpaceVolume (T : ℝ) : Measure (ℝ × Transverse) :=
  (volume.restrict (Icc (0:ℝ) T)).prod volume

def squareEnvelope (s₀ η : ℝ) (u : ℝ × Transverse) : ℝ :=
  ∑' j : ℕ, (term s₀ η j u.1 u.2)^2

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Uniform integrability of affine annular moment envelopes in a finite cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def cell (r : ℝ) : Set (ℝ × Transverse) := {u | u.2 ∈ Metric.ball 0 r}

def momentMajorant (s₀ η A B r : ℝ) (u : ℝ × Transverse) : ℝ :=
  2*A^2*(cell r).indicator (fun _ => (1:ℝ)) u+2*B^2*squareEnvelope s₀ η u

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # The small spatial annuli disappear pointwise and in every integrable majorant -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def tailRegion (s₀ η : ℝ) (J : ℕ) : Set (ℝ × Transverse) :=
  {u | ∃ j : ℕ, J ≤ j ∧ u.2 ∈ shell s₀ η j}

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusAnnularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting annular integrable bounds to time times the spatial torus -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def timePositionVolume (T : ℝ) : Measure (ℝ × Position) :=
  (volume.restrict (Icc (0:ℝ) T)).prod volume

def torusChart (u : ℝ × Position) : ℝ × Transverse :=
  (u.1,transverse (TorusChart.representative u.2))

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CommonMomentEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common square-integrable envelope for all capped velocity moments -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

def commonMoment (s₀ η A B : ℝ) (u : ℝ × Transverse) : ℝ :=
  A+B*Real.sqrt (squareEnvelope s₀ η u)

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusTailRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing small-annulus collision bounds on the spatial torus -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.AnnularEnvelope

instance instIsFiniteMeasureProdRealPositionTimePositionVolume (T : ℝ) : IsFiniteMeasure (timePositionVolume T) := by
  dsimp [timePositionVolume]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def torusTail (s₀ η : ℝ) (J : ℕ) : Set (ℝ × Position) :=
  torusChart ⁻¹' tailRegion s₀ η J

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Published weak compactness input for the two kinetic measure spaces

N. Dunford and B. J. Pettis, *Linear operations on summable functions*,
Transactions of the AMS 47 (1940), 323–392, Theorem 3.2.1, p. 376,
DOI 10.1090/S0002-9947-1940-0002020-4.
Publisher: https://www.ams.org/journals/tran/1940-047-03/S0002-9947-1940-0002020-4/S0002-9947-1940-0002020-4.pdf

The hypothesis below is the sequential weak-compactness consequence for the
one- and two-velocity spaces used here. `UniformIntegrable` includes the common
L¹ bound; `UnifTight` supplies the necessary control at infinity. We require
both, including on the infinite velocity spaces. No Boltzmann equation,
nonlinear identification, or admissible solution is assumed by this input.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

def WeakL1Converges (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
  Measurable g ∧ Integrable g μ ∧
    ∀ ψ : X → ℝ, Measurable ψ → (∃ C : ℝ, ∀ x, |ψ x| ≤ C) →
      Tendsto (fun n => ∫ x, ψ x*f n x ∂μ) atTop (𝓝 (∫ x, ψ x*g x ∂μ))

theorem WeakL1Converges.comp {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    WeakL1Converges μ (fun n => f (φ n)) g :=
  ⟨h.1,h.2.1,fun ψ hψ hB => (h.2.2 ψ hψ hB).comp hφ⟩

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The time primitive is weakly continuous on a finite time interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

def timePrimitive (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : ℝ × P) : ℝ :=
  ∫ s, if s ≤ z.1 then f (s,z.2) else 0 ∂μ

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Removing a finite prefix without changing the common sequence index -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

def zeroPrefix {X : Type*} (N : ℕ) (f : ℕ → X → ℝ) (n : ℕ) : X → ℝ :=
  if N ≤ n then f n else 0

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The normalized Carleman gain as a measurable velocity kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

def coordinateKernel (c : Kernel X Velocity) (q : ℝ) : Kernel (X × Velocity) Coordinates :=
  ((c.comap Prod.fst measurable_fst) ×ₖ
    Kernel.const (X × Velocity) ((volume : Measure ℝ).prod volume)).withDensity
      (fun z y => density (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)) z.2 y)

instance coordinateKernel_sFinite (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    IsSFiniteKernel (coordinateKernel c q) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => by
    unfold density
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top)

def inputMeasure (c : Kernel X Velocity) (q : ℝ) (z : X × Velocity) : Measure Velocity :=
  (coordinateKernel c q z).map (fun y => PlaneChart.chart z.2 y.1 y.2.1 y.2.2)

theorem inputMeasure_measurable (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    Measurable (inputMeasure c q) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hi := (((measurable_const : Measurable (fun _ : Velocity => (1 : ℝ≥0∞))).indicator hs).comp
      (measurable_lifted_point (X := X))).lintegral_kernel_prod_right'
      (κ := coordinateKernel c q)
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    unfold inputMeasure
    rw [Measure.map_apply (measurable_point z.2) hs]
    dsimp only [Function.comp_def]
    change _ = ∫⁻ y, ((fun y : Coordinates =>
      PlaneChart.chart z.2 y.1 y.2.1 y.2.2) ⁻¹' s).indicator
      (fun _ => (1 : ℝ≥0∞)) y ∂coordinateKernel c q z
    simpa only [one_mul] using
      (lintegral_indicator_const (μ := coordinateKernel c q z)
        (hs.preimage (measurable_point z.2)) (1 : ℝ≥0∞)).symm

def inputKernel (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    Kernel (X × Velocity) Velocity where
  toFun := inputMeasure c q
  measurable' := inputMeasure_measurable c q

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Conditional tensor products controlled by a single mass marginal -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def normalizedTensor (d : X → ℝ) (f g : X × Y → ℝ) (z : X × (Y × Y)) : ℝ :=
  f (z.1,z.2.1)*g (z.1,z.2.2)/(1+d z.1)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Truncating a mass-normalized velocity pair costs only its L1 tail -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

def fiberMass (ν : Measure Y) (f : X × Y → ℝ) (x : X) : ℝ := ∫ v, f (x,v) ∂ν

def normalizedPair (ν : Measure Y) (f : X × Y → ℝ) : X × (Y × Y) → ℝ :=
  normalizedTensor (fiberMass ν f) f f

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The normalized gain action respects spacetime representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

def action (K : Kernel (X × Velocity) Velocity) (f : X × Velocity → ℝ≥0∞)
    (z : X × Velocity) : ℝ≥0∞ := ∫⁻ v, f (z.1,v) ∂K z

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetEnvelopeTimeIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The transported core is dominated by an admissible Gaussian sheet -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCoreSheet

def amplitude (K α γ s t : ℝ) : ℝ :=
  ((K * max 1 (α * γ)⁻¹) / (s + t)) * JetGaussianProduct.coefficient

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Finite time integrals of the cold-envelope gain -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeTimeIntegral

def positiveGain (η K α γ s d b : ℝ) (a : Bool) (p : JetPrototype.Phase) (r : ℝ) : ℝ :=
  CollisionCutoff.gain b (fun v => JetTimeRegularity.positiveU η K α γ s d a
    (r, ((JetBarrier.flight r p).1, v))) p.2

end BoltzmannNonuniqueness.JetEnvelopeTimeIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_FreeCoreGainKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual free cold core supplies a normalized positive gain kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def coreKernel (η K α γ s d : ℝ) (a : Bool) : Kernel (ℝ × JetPrototype.Space) Velocity :=
  (Kernel.const _ (volume : Measure Velocity)).withDensity
    (fun p v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d p.1 a (p.2,v)))

instance coreKernel_sFinite (η K α γ s d : ℝ) (a : Bool) :
    IsSFiniteKernel (coreKernel η K α γ s d a) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

def normalizedCoreKernel (η K α γ s d q : ℝ) (a : Bool) :
    Kernel ((ℝ × JetPrototype.Space) × Velocity) Velocity :=
  ChartKernel.inputKernel (coreKernel η K α γ s d a) q

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialSecondMismatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The two atomic velocity measures on one limiting mesh annulus -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AxialBackground

/-- The stripe fraction is exactly one quarter in the supplied manuscript. -/
def weight (K α γ μ t σ z : ℝ) : ℝ :=
  (1/4)*JetCoreDensity.compressed K α γ μ t (AxialFlow.foot σ α γ μ t z)

def atom (K α γ μ t σ z : ℝ) : Measure Velocity :=
  ENNReal.ofReal (weight K α γ μ t σ z) •
    Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))

def cell (K α γ μ t z : ℝ) : Measure Velocity :=
  atom K α γ μ t 1 z+atom K α γ μ t (-1) z

theorem weight_nonneg {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t) (σ z : ℝ) :
    0 ≤ weight K α γ μ t σ z :=
  mul_nonneg (by norm_num) (JetCoreDensity.compressed_nonneg hK hα hγ hμ ht _)

theorem weight_bound {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t) (σ z : ℝ) :
    weight K α γ μ t σ z ≤ (1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)) :=
  mul_le_mul_of_nonneg_left (JetCoreDensity.compressed_bound hK hα hγ hμ ht _) (by norm_num)

theorem integrable_atom (K α γ μ t σ z : ℝ) (ψ : Velocity → ℝ) :
    Integrable ψ (atom K α γ μ t σ z) :=
  (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem integral_atom {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t) (σ z : ℝ) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂atom K α γ μ t σ z) =
      weight K α γ μ t σ z*ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)) := by
  rw [atom,integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (weight_nonneg hK hα hγ hμ ht σ z),smul_eq_mul]

theorem integral_cell {K α γ μ t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t) (z : ℝ) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂cell K α γ μ t z) =
      weight K α γ μ t 1 z*ψ (PlaneChart.join 0 (AxialFlow.velocity 1 α γ μ t z))+
      weight K α γ μ t (-1) z*ψ (PlaneChart.join 0 (AxialFlow.velocity (-1) α γ μ t z)) := by
  rw [cell,integral_add_measure (integrable_atom _ _ _ _ _ _ _ _) (integrable_atom _ _ _ _ _ _ _ _),
    integral_atom hK hα hγ hμ ht,integral_atom hK hα hγ hμ ht]

end BoltzmannNonuniqueness.AxialBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Thermal L1 convergence before spatial stripe averaging -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def testCoefficient (K α γ s d t σ z : ℝ) (ψ : Velocity → ℝ) (w : Transverse × ℝ) : ℝ :=
  compressed K α γ s t (JetCoreMap.sourceFoot σ α γ s d t z w.2) *
    ψ (JetCoreMeasure.velocityMap σ α γ s d t z w)

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Reduction of the actual dilated free core to its spatial mask average -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreDensity

def dilatedMask (r η s d t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) : ℝ :=
  (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
    (r • x.1-(r*t) • (d • w.1))

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # A centered thermal Gaussian as an admissible product sheet -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetAffineSheet

def center (u : ℝ) : Velocity := PlaneChart.join 0 u

def affineMap (d u : ℝ) (w : Transverse × ℝ) : Velocity :=
  PlaneChart.join (d • w.1) (u + d * w.2)

end BoltzmannNonuniqueness.JetAffineSheet

end

end

section

/-! # Removing the annular margins in local thermal L1 -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def scaleShell (η μ : ℝ) : Set Transverse := {y | μ < ‖y‖ ∧ ‖y‖ < Real.exp η*μ}

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # The Gaussian remainder has the smaller sheet amplitude d/s² -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetSupersolution
open BoltzmannNonuniqueness.JetBarrierCollision
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetRemainderSheet

def remainder (η K α γ s d t : ℝ) (a : Bool) (x : Space) (v : Velocity) : ℝ :=
  epsilon K s d * barrier η K α γ s d t a (x, v)

def amplitude (η K α γ s d t : ℝ) (a : Bool) (x : Space) : ℝ :=
  (epsilon K s d * massScale η K α γ s d t a x) * (Real.pi * Real.sqrt Real.pi)

def uniformConstant (K : ℝ) : ℝ :=
  JetComparisonCoefficient.coefficient K * Real.exp 4 * JetThermalKernel.bound * K *
    (Real.pi * Real.sqrt Real.pi)

end BoltzmannNonuniqueness.JetRemainderSheet

end

end

section

/-! # Mixed gain of the complete cold supersolution -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetEnvelopeGain

def amplitude (η K α γ s d t : ℝ) (a : Bool) (x : Space) : ℝ :=
  JetCoreSheet.amplitude K α γ s t + JetRemainderSheet.amplitude η K α γ s d t a x

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Arbitrary-power bounds for the complete escaped-barrier sum -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedTotal

def annulus (η K α γ s d₀ t : ℝ) (x v : Velocity) : ℝ≥0∞ :=
  ∑' a : Bool, ∑' n : Lattice, {n | outside η s t a x n}.indicator
    (fun n => ENNReal.ofReal (barrier η K α γ s (d₀ * s ^ 10) t a (shifted x n, v))) n

def total (s₀ η K α γ d₀ t : ℝ) (x v : Velocity) : ℝ≥0∞ :=
  ∑' j : ℕ, annulus η K α γ (jetScale s₀ η j) d₀ t x v

def coefficient (α K d₀ : ℝ) : ℝ :=
  2 * JetEscapedBarrier.coefficient α K d₀ * JetLatticeGaussian.constant ^ 3

def powerConstant (s₀ η α K d₀ : ℝ) (m : ℕ) : ℝ :=
  coefficient α K d₀ * ((m.factorial : ℝ) / (JetEscapedBarrier.rate η d₀ / 2) ^ m) *
    ∑' j : ℕ, jetScale s₀ η j ^ (16 * m - 31)

end BoltzmannNonuniqueness.JetEscapedTotal

end

end

section

/-! # Escaped sums for arbitrary retained cold colors

The comparison hypothesis here is a pointwise bound for a color family. It is
kept explicit for application to the solutions of the finite labeled system.
All constants are independent of the retained subset.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedEnvelope

def escapedSum (s₀ η t : ℝ) (x : Velocity)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, ∑' a : Bool, ∑' n : Lattice,
    {n | S j a n ∧ outside η (jetScale s₀ η j) t a x n}.indicator
      (fun n => ENNReal.ofReal (F j a n)) n

def constant (s₀ η α K d₀ : ℝ) (m : ℕ) : ℝ :=
  2 * JetEscapedTotal.powerConstant s₀ η α K d₀ m * tiltConstant

def exponent (A : ℝ) : ℕ := ⌈A⌉₊ + 2

end BoltzmannNonuniqueness.JetEscapedEnvelope

end

end

section

/-! # The real mixed-gain estimate for the main cold color -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetMainGain

def sheetConstant (α q : ℝ) : ℝ :=
  (SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2))).toReal + 1

def coefficient (K α γ q : ℝ) : ℝ :=
  (K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K) *
    sheetConstant α q

end BoltzmannNonuniqueness.JetMainGain

end

end

section

/-! # Annular mask error after integrating out the thermal variable -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def maskError (r η s d μ t : ℝ) (a : Bool) (p : Transverse × (Transverse × ℝ)) : ℝ :=
  ((mask η s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))-
    (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1*
      (stripe s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1))))*
    JetThermalKernel.J (SheetMeasures.join p.2)

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Scale-uniform mass and Gaussian velocity tails below a cold supersolution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeGain

def momentConstant (K α γ : ℝ) : ℝ :=
  (K*max 1 (α*γ)⁻¹*JetGaussianProduct.coefficient+JetRemainderSheet.uniformConstant K)*
    (8*Real.exp (16*(1+α)^2))

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HalfGaussianMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half-Gaussian velocity moments for the hot weight and cold cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.VelocityMoment

def weight (v : Velocity) : ℝ := Real.exp (‖v‖^2/2)

def hotConstant (q : ℝ) : ℝ := ∫ v, weight v*H q v

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_SpatialCutoffIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing small spatial regions in the collision-integrability argument -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν]

def outerCutoff (S : Set X) (f : X × Y → ℝ) : X × Y → ℝ :=
  (Prod.fst ⁻¹' Sᶜ).indicator f

end BoltzmannNonuniqueness.Compactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable velocity majorants for hard-sphere pair densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

def pairKernel (q : ℝ) (p : Velocity × Velocity) : ℝ :=
  (1+‖p.1‖+‖p.2‖)*H q p.1*H q p.2

variable {X : Type*} [MeasurableSpace X]

def pairDensity (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  (1+‖z.2.1‖+‖z.2.2‖)*f (z.1,z.2.1)*f (z.1,z.2.2)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Measure preservation and integrability for the full hard-sphere collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def scatterTriple (z : (X × (Velocity × Velocity)) × Sphere) :
    (X × (Velocity × Velocity)) × Sphere :=
  ((z.1.1,scatterPair z.2 z.1.2),z.2)

theorem scatterTriple_measurable : Measurable (scatterTriple (X := X)) := by
  unfold scatterTriple scatterPair scatterLeft scatterRight normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem scatterTriple_involutive : Function.Involutive (scatterTriple (X := X)) := by
  intro z
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have hi := scatterPair_involutive (z.2 : Velocity) hw z.1.2
  change ((z.1.1,scatterPair z.2 (scatterPair z.2 z.1.2)),z.2) = z
  rw [hi]

def scatterTripleEquiv : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    ((X × (Velocity × Velocity)) × Sphere) where
  toFun := scatterTriple
  invFun := scatterTriple
  left_inv := scatterTriple_involutive
  right_inv := scatterTriple_involutive
  measurable_toFun := scatterTriple_measurable
  measurable_invFun := scatterTriple_measurable

def preRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)

def postRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  preRate f (scatterTriple z)


end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r5fcdae_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def collisionGrouping : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    ((X × Velocity) × (Velocity × Sphere)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.prodAssoc.symm) (MeasurableEquiv.refl Sphere)).trans
    MeasurableEquiv.prodAssoc

def gainDensity (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, postRate f (collisionGrouping.symm (p,q)) ∂((volume : Measure Velocity).prod sphereArea)

def lossDensity (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, preRate f (collisionGrouping.symm (p,q)) ∂((volume : Measure Velocity).prod sphereArea)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Weak convergence of the actual full collision rates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def normalizedKernel (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  collisionKernel z.1.2.1 z.1.2.2 z.2/(1+‖z.1.2.1‖+‖z.1.2.2‖)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RawPairCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness bounds for the unweighted collision pair product -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def pairProduct (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  f (z.1,z.2.1)*f (z.1,z.2.2)

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_IncomingLossRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Continuous incoming-velocity tests for the symmetric gain and loss

These use the original normal-sphere parametrization, so no new change of
variables is needed to handle the diagonal where the two velocities coincide.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.CollisionCompactness

def incomingGainTest (φ : Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  (1/2 : ℝ) * ∫ ω : Sphere, collisionKernel p.1 p.2 ω *
    (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω)) ∂sphereArea

def incomingLossTest (φ : Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  (2*Real.pi*‖p.1-p.2‖)*φ p.2

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Incoming collision measures, including atomic cold partners -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*}

def incomingRate (z : X × (Velocity × Velocity)) : ℝ :=
  2*Real.pi*‖z.2.1-z.2.2‖

variable [MeasurableSpace X]

def incomingCollisionMeasure (μ : Measure (X × (Velocity × Velocity))) :
    Measure ((X × (Velocity × Velocity)) × Sphere) :=
  (μ.prod sphereArea).withDensity
    (fun z => ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2))

def incomingLeft (z : (X × (Velocity × Velocity)) × Sphere) : X × Velocity :=
  (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)

def incomingRight (z : (X × (Velocity × Velocity)) × Sphere) : X × Velocity :=
  (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)

def incomingGainMeasure (μ : Measure (X × (Velocity × Velocity))) : Measure (X × Velocity) :=
  (1/2 : ℝ≥0∞) • ((incomingCollisionMeasure μ).map incomingLeft+
    (incomingCollisionMeasure μ).map incomingRight)

def incomingLossMeasure (μ : Measure (X × (Velocity × Velocity))) : Measure (X × Velocity) :=
  (incomingCollisionMeasure μ).map (fun z => (z.1.1,z.1.2.2))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalGainMeasureActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual normal-angle gain kernel for measurable cold partner measures -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def normalChild (left : Bool) (z : (X × Velocity) × (Velocity × Sphere)) : Velocity :=
  if left then scatterLeft z.2.1 z.1.2 z.2.2 else scatterRight z.2.1 z.1.2 z.2.2

def normalParameters (K : Kernel X Velocity) : Kernel (X × Velocity) (Velocity × Sphere) :=
  (K.comap Prod.fst measurable_fst) ×ₖ Kernel.const _ sphereArea

def normalRate (z : (X × Velocity) × (Velocity × Sphere)) : ℝ≥0∞ :=
  ENNReal.ofReal (collisionKernel z.2.1 z.1.2 z.2.2)

def normalChildKernel (K : Kernel X Velocity) (left : Bool) : Kernel (X × Velocity) Velocity :=
  (Kernel.withDensity (Kernel.id ×ₖ normalParameters K)
    (fun _ z => normalRate z)).map (normalChild left)

def normalGainKernel (K : Kernel X Velocity) : Kernel (X × Velocity) Velocity :=
  normalChildKernel K true+normalChildKernel K false

end BoltzmannNonuniqueness

end

end

section

/-! # The physical gain kernel, retaining the collision's spacetime location -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def normalPhaseGainKernel (K : Kernel X Velocity) : Kernel (X × Velocity) (X × Velocity) :=
  (Kernel.id ×ₖ normalGainKernel K).map (fun z => (z.1.1,z.2))

instance normalPhaseGainKernel_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (normalPhaseGainKernel K) := by
  unfold normalPhaseGainKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # Finite positive measures associated with integrable collision densities -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def positiveDensityMeasure (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

end BoltzmannNonuniqueness

end

end

section

/-! # A countable positive smooth family determining finite phase measures -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

abbrev PositivePhaseTest (n : ℕ) :=
  {f : C(Velocity × Velocity,ℝ) // ContDiff ℝ (⊤ : ℕ∞) (f : _ → ℝ) ∧
    tsupport (f : _ → ℝ) ⊆ Metric.closedBall 0 (n+1 : ℝ) ∧ ∀ p, 0 ≤ f p}

instance instNonemptyPositivePhaseTest (n : ℕ) : Nonempty (PositivePhaseTest n) :=
  ⟨⟨0,contDiff_const,by simp,by simp⟩⟩

instance instSecondCountableTopologyPositivePhaseTest (n : ℕ) : SecondCountableTopology (PositivePhaseTest n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

def positivePhaseSeq (n m : ℕ) : PositivePhaseTest n :=
  TopologicalSpace.denseSeq (PositivePhaseTest n) m

def positivePhaseTest (j : ℕ) : Velocity × Velocity → ℝ :=
  (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).1

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A positive gain-and-retention kernel acting on an occupation density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def positiveSourceKernel (K : Kernel X X) [IsSFiniteKernel K] (b r : X → ℝ) : Kernel X X :=
  K.withDensity (fun _ x => ENNReal.ofReal (b x))+
    Kernel.id.withDensity (fun _ x => ENNReal.ofReal (b x*r x))

instance positiveSourceKernel_sFinite (K : Kernel X X) [IsSFiniteKernel K] (b r : X → ℝ) :
    IsSFiniteKernel (positiveSourceKernel K b r) := by
  have : IsSFiniteKernel (K.withDensity (fun _ x => ENNReal.ofReal (b x))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  have : IsSFiniteKernel (Kernel.id.withDensity (fun (_ : X) x => ENNReal.ofReal (b x*r x))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold positiveSourceKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLossFrequency
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cutoff collision terms are dominated by the physical collision marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_4_r5fcdae_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def cutoffLossDensity (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1)
    ∂((volume : Measure Velocity).prod sphereArea)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionDissipation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The moving relative-speed cutoff has the full collision limit -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_6_r5fcdae_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def truncatedPreRate (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  {z | ‖z.1.2.1-z.1.2.2‖ < b}.indicator (preRate f) z

def truncatedPostRate (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  {z | ‖z.1.2.1-z.1.2.2‖ < b}.indicator (postRate f) z

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Particle interchange and elastic substitution for the cutoff collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def particleSwap : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    ((X × (Velocity × Velocity)) × Sphere) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl X) MeasurableEquiv.prodComm)
    (MeasurableEquiv.refl Sphere)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The symmetric weak collision identity with the invariant speed cutoff -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def collisionJump (ψ : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)+
    ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-ψ (z.1.1,z.1.2.1)-ψ (z.1.1,z.1.2.2)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceAngularCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local unit-sphere coordinates at the minorization collision -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def incomingTangent : V →L[ℝ] V := (EuclideanSpace.proj 0).smulRight beamAxis
def normalTangent : V →L[ℝ] V :=
  (EuclideanSpace.proj 1).smulRight secondAxis +
    ((1 / Real.sqrt 2 : ℝ) • EuclideanSpace.proj 2).smulRight (firstAxis-beamAxis)

def incomingChart (z : V) : V := NormedSpace.normalize (firstAxis+incomingTangent z)
def normalChart (z : V) : V := NormedSpace.normalize (minorizationNormal+normalTangent z)

@[simp] theorem incomingChart_zero : incomingChart 0 = firstAxis := by
  simp [incomingChart,NormedSpace.normalize_eq_self_of_norm_eq_one axis_norms.1]

@[simp] theorem normalChart_zero : normalChart 0 = minorizationNormal := by
  simp [normalChart,NormedSpace.normalize_eq_self_of_norm_eq_one minorizationNormal_norm]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Free transport and its measure-preserving characteristic coordinates on the torus -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

def flight (t : ℝ) (p : Phase) : Phase := (p.1+torusProjection (t • p.2),p.2)

theorem continuous_flight : Continuous (fun z : ℝ × Phase => flight z.1 z.2) := by
  unfold flight torusProjection
  fun_prop

theorem measurable_flight : Measurable (fun z : ℝ × Phase => flight z.1 z.2) :=
  continuous_flight.measurable

theorem flight_add (t s : ℝ) (p : Phase) : flight t (flight s p) = flight (t+s) p := by
  apply Prod.ext
  · funext i
    change (p.1 i+(s*p.2 i : ℝ))+(t*p.2 i : ℝ) = p.1 i+((t+s)*p.2 i : ℝ)
    rw [add_mul,AddCircle.coe_add]
    abel
  · rfl

@[simp] theorem flight_zero (p : Phase) : flight 0 p = p := by
  apply Prod.ext
  · funext i
    simp [flight,torusProjection]
  · rfl

@[simp] theorem flight_neg (t : ℝ) (p : Phase) : flight (-t) (flight t p) = p := by
  rw [flight_add,neg_add_cancel,flight_zero]

@[simp] theorem neg_flight (t : ℝ) (p : Phase) : flight t (flight (-t) p) = p := by
  rw [flight_add,add_neg_cancel,flight_zero]

def along (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ := F (z.1,flight z.1 z.2)

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Time-translated periodic tests for pasting a global continuation -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem time_shift_support {R τ t : ℝ} (h : R+|τ| < |t|) : R < |t+τ| := by
  have ht : |t| ≤ |t+τ|+|τ| := by
    calc
      _ = |(t+τ)+(-τ)| := by congr 1; ring
      _ ≤ |t+τ|+|-τ| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  linarith

def KineticTest.timeShift (φ : KineticTest) (τ : ℝ) : KineticTest where
  toFun t x v := φ.toFun (t+τ) x v
  regular := φ.regular.comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun z : LiftedSpaceTimePhase => (z.1+τ,z.2)) from by fun_prop)
  compact_time_velocity := by
    obtain ⟨R,hR,hzero⟩ := φ.compact_time_velocity
    refine ⟨R+|τ|,by positivity,?_⟩
    intro t x v ht
    apply hzero
    rcases ht with ht | hv
    · exact Or.inl (time_shift_support ht)
    · exact Or.inr (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg τ)) hv)

@[simp] theorem KineticTest.timeShift_toFun (φ : KineticTest) (τ t : ℝ) (x : Position) (v : Velocity) :
    (φ.timeShift τ).toFun t x v = φ.toFun (t+τ) x v := rfl

def MassTest.timeShift (φ : MassTest) (τ : ℝ) : MassTest where
  toFun t x := φ.toFun (t+τ) x
  regular := φ.regular.comp
    (show ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × Velocity => (z.1+τ,z.2)) from by fun_prop)
  compact_time := by
    obtain ⟨R,hR,hzero⟩ := φ.compact_time
    exact ⟨R+|τ|,by positivity,fun t x ht => hzero (t+τ) x (time_shift_support ht)⟩

@[simp] theorem MassTest.timeShift_toFun (φ : MassTest) (τ t : ℝ) (x : Position) :
    (φ.timeShift τ).toFun t x = φ.toFun (t+τ) x := rfl

end BoltzmannNonuniqueness

end

end

section

/-! # Measurable representatives for periodic kinetic and mass tests -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

@[fun_prop] theorem measurable_torusRepresentative : Measurable torusRepresentative := by
  have hm : Measurable (fun x : Position => fun i : Fin 3 =>
      ((AddCircle.equivIco (1:ℝ) 0) (x i) : ℝ)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (T := (1:ℝ)) 0).measurable.comp (measurable_pi_apply i))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hm

@[fun_prop] theorem MassTest.measurable_transportDerivative (φ : MassTest) :
    Measurable (fun p : ℝ × Phase => φ.transportDerivative p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × Phase => (p.1,torusRepresentative p.2.1)) :=
    measurable_fst.prodMk (measurable_torusRepresentative.comp measurable_snd.fst)
  have hd := (φ.regular.continuous_fderiv (by simp)).measurable.comp hm
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.measurable.comp
    (hd.prodMk (measurable_const.prodMk measurable_snd.snd))

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_RenormalizedIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrability of the full collision pre-rate after renormalization -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def normalizedPreRate (f : X × Velocity → ℝ)
    (z : (X × Velocity) × (Velocity × Sphere)) : ℝ :=
  preRate f (collisionGrouping.symm z)/(1+f z.1/maxwellian z.1.2)

def normalizedPostRate (f : X × Velocity → ℝ)
    (z : (X × Velocity) × (Velocity × Sphere)) : ℝ :=
  postRate f (collisionGrouping.symm z)/(1+f z.1/maxwellian z.1.2)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedCollisionRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The first-velocity-moment weight of the normalized pair is integrable -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def pairVelocityWeight (z : X × (Velocity × Velocity)) : ℝ := 1+‖z.2.1‖+‖z.2.2‖

def weightedNormalizedPair (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  pairVelocityWeight z*normalizedPair volume f z

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform velocity-tail control of the moment-weighted normalized pair -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def pairVelocityCut (R : ℝ) (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then weightedNormalizedPair f z else 0

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Actual pre- and post-collision rates normalized by the spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def massNormalizedPreRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  preRate f z/(1+fiberMass volume f z.1.1)

def massNormalizedPostRate (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  postRate f z/(1+fiberMass volume f z.1.1)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedPairUniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive two-collision entry weight with measurable beam coefficients -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def accessWeight (v : V) (w₁ w₂ : Sphere × Sphere → V)
    (b₁ b₂ : Sphere × Sphere → ℝ) (κ ρ : ℝ) (a : Sphere × Sphere) : ℝ≥0∞ :=
  let u := child v (w₁ a) a.1.1
  let z := child u (w₂ a) a.2.1
  ENNReal.ofReal (4*Real.pi*b₁ a*‖v-w₁ a‖)*
    ENNReal.ofReal (4*Real.pi*b₂ a*‖u-w₂ a‖)*
      (ball (κ • firstAxis) ρ).indicator (fun _ => 1) z

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairPatchIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded tests of a velocity-pair density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def pairTestAverage (k : Velocity × Velocity → ℝ) (P : X × (Velocity × Velocity) → ℝ)
    (x : X) : ℝ := ∫ y : Velocity × Velocity, k y*P (x,y)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DoubleCollisionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Surjectivity of the two-output collision variation away from grazing and parallel normals -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness

def normalPlaneLift (n m : Velocity) (u v : ℝ) : Velocity :=
  ((u-(inner ℝ n m)*v)/(1-(inner ℝ n m)^2)) • n+
    ((v-(inner ℝ n m)*u)/(1-(inner ℝ n m)^2)) • m

/-- The derivative when the first normal varies through unit vectors. The normal
component of its variation is included, so the formula also applies to the
radially normalized extension off the sphere. -/
def doubleOutgoingVariation (d n m : Velocity) (z : (Velocity × Velocity) × Velocity) :
    Velocity × Velocity :=
  (z.1.1-(inner ℝ z.1.2 n+inner ℝ d z.2-2*(inner ℝ d n)*inner ℝ n z.2) • n-
      (inner ℝ d n) • z.2,
    z.1.1-(inner ℝ z.1.2 m) • m)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The genuine doubled collision map has the surjective outgoing variation -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness
namespace DoubleGain

abbrev Domain := (Velocity × Velocity) × Velocity

def velocityProjection : Domain →L[ℝ] Velocity :=
  (ContinuousLinearMap.fst ℝ Velocity Velocity).comp
    (ContinuousLinearMap.fst ℝ (Velocity × Velocity) Velocity)

def relativeProjection : Domain →L[ℝ] Velocity :=
  (ContinuousLinearMap.snd ℝ Velocity Velocity).comp
    (ContinuousLinearMap.fst ℝ (Velocity × Velocity) Velocity)

def normalProjection : Domain →L[ℝ] Velocity :=
  ContinuousLinearMap.snd ℝ (Velocity × Velocity) Velocity

def coefficientDifferential (d n : Velocity) : Domain →L[ℝ] ℝ :=
  (innerSL ℝ n).comp relativeProjection+(innerSL ℝ d).comp normalProjection-
    (2*inner ℝ d n) • ((innerSL ℝ n).comp normalProjection)

def differential (d n m : Velocity) : Domain →L[ℝ] (Velocity × Velocity) :=
  (velocityProjection-((inner ℝ d n) • normalProjection+
    (coefficientDifferential d n).smulRight n)).prod
    (velocityProjection-((innerSL ℝ m).comp relativeProjection).smulRight m)

def outgoing (m : Velocity) (z : Domain) : Velocity × Velocity :=
  (z.1.1-((inner ℝ z.1.2 z.2)*(inner ℝ z.2 z.2)⁻¹) • z.2,
    z.1.1-(inner ℝ z.1.2 m) • m)

def numeratorDifferential (d n : Velocity) : Domain →L[ℝ] ℝ :=
  (innerSL ℝ n).comp relativeProjection+(innerSL ℝ d).comp normalProjection

def denominatorDifferential (n : Velocity) : Domain →L[ℝ] ℝ :=
  (2 : ℝ) • ((innerSL ℝ n).comp normalProjection)

def coefficient (z : Domain) : ℝ := inner ℝ z.1.2 z.2*(inner ℝ z.2 z.2)⁻¹

end DoubleGain
end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The two-output submersion for nonzero, unnormalized collision normals -/
noncomputable section
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def scaleNormal (r : ℝ) : Domain →L[ℝ] Domain :=
  (ContinuousLinearMap.fst ℝ (Velocity × Velocity) Velocity).prod
    (r • normalProjection)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Full rank for almost every doubled outgoing collision parameter -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def good (m d n : Velocity) : Prop := n ≠ 0 ∧
  1-(inner ℝ (NormedSpace.normalize n) m)^2 ≠ 0 ∧
    inner ℝ d (NormedSpace.normalize n) ≠ 0

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Local smoothness of the doubled outgoing map off the zero normal -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def normalDomain : Set Domain := {z | z.2 ≠ 0}

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The doubled outgoing law with the physical surface-area normal measure -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def angularOutgoing (m : Velocity) (z : (Velocity × Velocity) × Sphere) : Velocity × Velocity :=
  outgoing m (z.1,z.2.1)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Absolute continuity for two physical outgoing velocities with common incoming pair -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doublePhysicalSFinite_r5fcdae_1 :
    SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) :=
  Measure.prod.instSFinite
def relativePair (p : Velocity × Velocity) : Velocity × Velocity := (p.1,p.1-p.2)

def physicalPairAt (m : Velocity) (z : (Velocity × Velocity) × Sphere) : Velocity × Velocity :=
  (scatterLeft z.1.1 z.1.2 z.2.1,scatterLeft z.1.1 z.1.2 m)

def physicalDoubleOutgoing (z : ((Velocity × Velocity) × Sphere) × Sphere) : Velocity × Velocity :=
  physicalPairAt z.2.1 z.1

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Finite, absolutely continuous physical two-output reference measures -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

abbrev Parameters := ((Velocity × Velocity) × Sphere) × Sphere

def incomingBall (R : ℝ) : Set (Velocity × Velocity) :=
  Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R

def parameterMeasure (R : ℝ) : Measure Parameters :=
  (((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea).prod sphereArea

instance parameterMeasureFinite (R : ℝ) : IsFiniteMeasure (parameterMeasure R) := by
  have : IsFiniteMeasure ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) :=
    isFiniteMeasure_restrict.mpr ((isCompact_closedBall (0 : Velocity) R).prod
      (isCompact_closedBall (0 : Velocity) R)).measure_lt_top.ne
  unfold parameterMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

local instance doubleReferenceSFinite_r5fcdae_1 :
    SFinite ((volume : Measure (Velocity × Velocity)).prod sphereArea) := Measure.prod.instSFinite
def rateProduct (z : Parameters) : ℝ :=
  collisionKernel z.1.1.1 z.1.1.2 z.1.2.1*collisionKernel z.1.1.1 z.1.1.2 z.2.1

def physicalReferenceMeasure (R : ℝ) : Measure (Velocity × Velocity) :=
  Measure.map physicalDoubleOutgoing ((parameterMeasure R).withDensity (fun z => ENNReal.ofReal (rateProduct z)))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The integrable physical two-output density and its translation continuity -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

def referenceDensity (R : ℝ) (p : Velocity × Velocity) : ℝ :=
  ((physicalReferenceMeasure R).rnDeriv volume p).toReal

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Physical two-output tests and the squared angular adjoint -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

local instance doubleTestInnerSFinite_r5fcdae_1 (R : ℝ) :
    SFinite (((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)).prod sphereArea) :=
  Measure.prod.instSFinite
def angularAdjoint (ψ : Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  ∫ n : Sphere, collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n) ∂sphereArea

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularGainTranslationTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact incoming-velocity bounds for bounded angular tests -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

instance incomingBallFinite (R : ℝ) :
    IsFiniteMeasure ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) :=
  isFiniteMeasure_restrict.mpr ((isCompact_closedBall (0 : Velocity) R).prod
    (isCompact_closedBall (0 : Velocity) R)).measure_lt_top.ne

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Angular translation control with a measurable spacetime parameter -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

def angularFamily (ψ : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  angularAdjoint (fun v => ψ (z.1,v)) z.2

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairBoundedTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The physical linear gain operator on incoming pair densities -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

local instance pairGainSphereSFinite_r5fcdae_1 : SFinite ((volume : Measure Velocity).prod sphereArea) :=
  Measure.prod.instSFinite
def pairPreRate (g : X × (Velocity × Velocity) → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  collisionKernel z.1.2.1 z.1.2.2 z.2*g z.1

def pairPostRate (g : X × (Velocity × Velocity) → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ := pairPreRate g (scatterTriple z)

def pairGain (g : X × (Velocity × Velocity) → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, pairPostRate g (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The relative-velocity cutoff error vanishes under the product Gaussian moment -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

def relativeCutoff (b : ℝ) (f : Velocity × Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  if ‖p.1-p.2‖ < b then f p else 0

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The linear velocity moment controls the physical pair-to-gain operator -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def momentPair (g : X × (Velocity × Velocity) → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  (1+‖z.2.1‖+‖z.2.2‖)*g z

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Bounded compact truncation in the incoming pair moment norm -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

def momentVelocityCut (R : ℝ) (g : X × (Velocity × Velocity) → ℝ) : X × (Velocity × Velocity) → ℝ :=
  (univ ×ˢ incomingBall R).indicator (momentPair g)

def boundedPairCut (R : ℝ) (B : ℝ≥0) (g : X × (Velocity × Velocity) → ℝ)
    (z : X × (Velocity × Velocity)) : ℝ := by
  classical
  exact if z.2 ∈ incomingBall R ∧ ‖momentPair g z‖ < (B:ℝ) then g z else 0

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocitySmoothingError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Moving velocity translations onto bounded measurable tests -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

def velocityShift (a : Velocity) : (X × Velocity) ≃ᵐ (X × Velocity) where
  toFun p := (p.1,p.2+a)
  invFun p := (p.1,p.2-a)
  left_inv p := by simp only [add_sub_cancel_right]
  right_inv p := by simp only [sub_add_cancel]
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add_const a)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub_const a)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # A countable smooth exhaustion of velocity space -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

def velocityExhaustionBump (j : ℕ) : ContDiffBump (0 : Velocity) :=
  ⟨(j:ℝ)+1,(j:ℝ)+2,by positivity,by linarith⟩

def velocityExhaustion (j : ℕ) : Velocity → ℝ := velocityExhaustionBump j

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integration of velocity translations against a finite convolution kernel -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def parameterShift (z : Velocity × (X × Velocity)) : Velocity × (X × Velocity) :=
  (z.1,(z.2.1,z.2.2-z.1))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # An L1 error bound for velocity smoothing by a probability kernel -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def velocitySmooth (χ : Velocity → ℝ) (F : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ a : Velocity, χ a*F (p.1,p.2-a)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmoothedPrePostIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A compact incoming cutoff and a translated outgoing velocity smoothing kernel -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Compactness

def translatedVelocityTest (χ : C(Velocity,ℝ)) (z : Velocity) : C(Velocity,ℝ) :=
  ⟨fun v => χ (z-v),χ.continuous.comp (continuous_const.sub continuous_id)⟩

def smoothedAngularKernel (η χ : C(Velocity,ℝ)) (p : Velocity × (Velocity × Velocity)) : ℝ :=
  (η p.2.1*η p.2.2)*∫ ω : Sphere,
    collisionKernel p.2.1 p.2.2 ω*χ (p.1-scatterLeft p.2.1 p.2.2 ω) ∂sphereArea

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TransportCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of smooth kinetic cutoffs along free characteristics -/

noncomputable section

open Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def characteristic (p : _root_.OAI.BoltzmannNonuniqueness.Published.Velocity × _root_.OAI.BoltzmannNonuniqueness.Published.Velocity) (t : ℝ) : KineticPhase :=
  ((t,p.1+t • p.2),p.2)

end BoltzmannNonuniqueness.TransportCutoff

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MixedPhysicalMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Polarized cutoff rates and their exact collision-map symmetries -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def mixedPreRate (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2*c (z.1.1,z.1.2.1)*h (z.1.1,z.1.2.2)

def mixedPostRate (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  mixedPreRate b c h (scatterTriple z)

def mixedGainDensity (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  (1/2 : ℝ)*((∫ q : Velocity × Sphere, mixedPostRate b c h (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea)+
    (∫ q : Velocity × Sphere, mixedPostRate b h c (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identification of the polarized loss marginal with hot density times cold frequency -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_10_r5fcdae_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def mixedLossDensity (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, CollisionCutoff.kernel b p.2 q.1 q.2*h p*c (p.1,q.1)
    ∂(volume : Measure Velocity).prod sphereArea

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite positive measures of the actual cutoff mixed gain and loss -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def mixedGainMeasure (μ : Measure X) (b : ℝ) (c h : X × Velocity → ℝ) :
    Measure (X × Velocity) := positiveDensityMeasure (μ.prod volume) (mixedGainDensity b c h)

def mixedLossMeasure (μ : Measure X) (b : ℝ) (c h : X × Velocity → ℝ) :
    Measure (X × Velocity) := positiveDensityMeasure (μ.prod volume) (mixedLossDensity b c h)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedPairCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local uniform integrability of the mass-normalized physical collision rates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X]

def velocityPairBox (R : ℝ) : Set (X × (Velocity × Velocity)) :=
  univ ×ˢ (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R)

def angularPairBox (R : ℝ) : Set ((X × (Velocity × Velocity)) × Sphere) :=
  velocityPairBox R ×ˢ univ

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedGainSmoothingAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Incoming-velocity localization of the actual physical gain -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def localizedPostRate (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (η (scatterLeft z.1.2.1 z.1.2.2 z.2)*η (scatterRight z.1.2.1 z.1.2.2 z.2))*
    massNormalizedPostRate f z

def localizedPhysicalGain (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, localizedPostRate η f (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identifying the localized physical gain with the linear pair operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness
variable {X : Type*}

def localizedPair (η : C(Velocity,ℝ)) (f : X × Velocity → ℝ)
    (z : X × (Velocity × Velocity)) : ℝ :=
  (η z.2.1*η z.2.2)*normalizedPair volume f z

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local weighted Lipschitz bounds for the finite-cutoff equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CutoffLipschitz

def frequencyConstant (q b : ℝ) : ℝ := 2 * Real.pi * b * ∫ w, H q w

def collision (b : ℝ) (f : Velocity → ℝ) (v : Velocity) : ℝ :=
  CollisionCutoff.gain b f v - f v * CollisionCutoff.frequency b f v

end BoltzmannNonuniqueness.CutoffLipschitz

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of the actual cutoff equation's right-hand side -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def collisionSource (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  KineticCollisionNullSets.gain b f p-f p*KineticCollisionNullSets.frequency b f p

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # L1 contraction for marginalizing a collision rate -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_11_r5fcdae_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
def collisionMarginal (h : (X × (Velocity × Velocity)) × Sphere → ℝ)
    (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, h (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceBranchingHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cutting the first-event formula at an intermediate time -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def clockSurvival (rate : ℝ≥0) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(rate : ℝ)*s))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Coupled positive histories with two beam marks and self-retention marks -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev HistoryMark := Fin 3

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PerturbedFiniteBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive marked histories in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

structure BeamCoefficients where
  plusPartner : ℝ × V → V
  minusPartner : ℝ × V → V
  plusDensity : ℝ × V → ℝ
  minusDensity : ℝ × V → ℝ
  plusPartner_measurable : Measurable plusPartner
  minusPartner_measurable : Measurable minusPartner
  plusDensity_measurable : Measurable plusDensity
  minusDensity_measurable : Measurable minusDensity

abbrev PhysicalFlightState := ℝ × (V × V)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricMesh
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A compact logarithmic phase for the dilated geometric mesh -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

def phase (a η : ℝ) : ℝ := Real.exp (η*Int.fract (Real.log a/η))

def index (a η : ℝ) : ℤ := ⌊Real.log a/η⌋

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Fixed limiting mesh points arise from actual annular indices -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

def annularIndex (s₀ η : ℝ) (r : ℕ → ℝ) (k : ℤ) (n : ℕ) : ℕ :=
  (index (s₀/r n) η-k).toNat

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Disjoint annuli in the limiting geometric mesh -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

def point (θ η : ℝ) (k : ℤ) : ℝ := θ*Real.exp (η*(k:ℝ))

theorem point_pos {θ : ℝ} (hθ : 0 < θ) (η : ℝ) (k : ℤ) : 0 < point θ η k :=
  mul_pos hθ (Real.exp_pos _)

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # The atomic background on the limiting geometric mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def scale (θ η : ℝ) (y : Transverse) : ℝ :=
  GeometricMesh.point θ η (GeometricMesh.index (‖y‖/θ) η)

/-- Here `l` is the limit of the first excluded scale `scale (N+1) / r`.
The retained colors have strictly larger scales. -/
def active (θ η l : ℝ) (y : Transverse) : Prop :=
  l < scale θ η y ∧ y ∈ JetGeometry.scaleShell η (scale θ η y)

def background (θ η l K α γ t : ℝ) (x : JetPrototype.Space) : Measure Velocity := by
  classical
  exact if active θ η l x.1 then AxialBackground.cell K α γ (scale θ η x.1) t x.2 else 0

theorem scale_pos {θ : ℝ} (hθ : 0 < θ) (η : ℝ) (y : Transverse) : 0 < scale θ η y :=
  GeometricMesh.point_pos hθ η _

theorem scale_measurable (θ η : ℝ) : Measurable (scale θ η) := by
  unfold scale GeometricMesh.point GeometricMesh.index
  fun_prop

theorem active_measurableSet (θ η l : ℝ) : MeasurableSet {y | active θ η l y} :=
  (measurableSet_lt measurable_const (scale_measurable θ η)).inter
    ((measurableSet_lt (scale_measurable θ η) measurable_norm).inter
      (measurableSet_lt measurable_norm ((scale_measurable θ η).const_mul _)))

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The annular label uses the geometric scale with index shifted by one -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

def jetIndex (s₀ η : ℝ) (r : ℕ → ℝ) (k : ℤ) (n : ℕ) : ℕ :=
  annularIndex s₀ η r k n-1

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Only finitely many geometric shells meet a fixed radial window -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

/-- The integer mesh coordinate of an actual jet label. -/
def jetMeshIndex (s₀ η r : ℝ) (j : ℕ) : ℤ := index (s₀/r) η-(j+1:ℕ)

end BoltzmannNonuniqueness.GeometricMesh

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BackgroundCappedLoss
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform polynomial velocity moments of the limiting background -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.AxialBackground

theorem axial_velocity_norm_le {σ α γ μ t z : ℝ} (hα : 0 ≤ α) (hσ : |σ| = 1) :
    ‖PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)‖ ≤ 1+α := by
  have hs := PlaneChart.norm_join_sq 0 (AxialFlow.velocity σ α γ μ t z)
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add] at hs
  have he : ‖PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)‖ =
      |AxialFlow.velocity σ α γ μ t z| := by
    nlinarith [norm_nonneg (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)),
      abs_nonneg (AxialFlow.velocity σ α γ μ t z),sq_abs (AxialFlow.velocity σ α γ μ t z)]
  rw [he]
  simpa only [hσ] using AxialAtomicSheet.velocity_abs_le (σ := σ) (γ := γ)
    (μ := μ) (t := t) (z := z) hα

theorem integral_cell_abs_le {K α γ μ t C : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (z : ℝ) (ψ : Velocity → ℝ)
    (hψ : ∀ v, ‖v‖ ≤ 1+α → |ψ v| ≤ C) :
    |∫ v, ψ v ∂cell K α γ μ t z| ≤
      2*((1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)))*C := by
  let B := (1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t))
  have hB : 0 ≤ B := by
    apply mul_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) (by linarith)
  have hs (σ : ℝ) (hσ : |σ| = 1) :
      |weight K α γ μ t σ z*ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))| ≤ B*C := by
    rw [abs_mul,abs_of_nonneg (weight_nonneg hK hα.le hγ.le hμ ht σ z)]
    exact mul_le_mul (weight_bound hK hα hγ hμ ht σ z)
      (hψ _ (axial_velocity_norm_le hα.le hσ)) (abs_nonneg _) hB
  rw [integral_cell hK hα.le hγ.le hμ ht]
  apply (abs_add_le _ _).trans
  have h := add_le_add (hs 1 (by norm_num)) (hs (-1) (by norm_num))
  simpa only [← two_mul,mul_assoc,B] using h

theorem moment_cell_bound {K α γ μ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (z : ℝ) (k : ℕ) :
    (∫ v, (1+‖v‖)^k ∂cell K α γ μ t z) ≤
      2*((1/4)*((K*max 1 (α*γ)⁻¹)/(μ+t)))*(2+α)^k := by
  apply (le_abs_self _).trans
  apply integral_cell_abs_le hK hα hγ hμ ht z
  intro v hv
  rw [abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ 1+‖v‖) k)]
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

end BoltzmannNonuniqueness.AxialBackground

namespace BoltzmannNonuniqueness.GeometricBackground

theorem moment_bound {θ η l K α γ t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (ht : 0 < t)
    (x : JetPrototype.Space) (k : ℕ) :
    (∫ v, (1+‖v‖)^k ∂background θ η l K α γ t x) ≤
      2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*(2+α)^k := by
  classical
  have hcoef : 0 ≤ K*max 1 (α*γ)⁻¹ :=
    mul_nonneg hK (le_max_of_le_left zero_le_one)
  by_cases ha : active θ η l x.1
  · rw [background,ite_eq_left ha]
    apply (AxialBackground.moment_cell_bound hK hα hγ (scale_pos hθ η x.1) ht.le x.2 k).trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) k)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left hcoef (by linarith) (by linarith [ha.1])
  · rw [background,ite_eq_right ha,integral_zero_measure]
    positivity

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Measurable velocity averages of the limiting atomic background -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem clamped_weight_measurable {α γ μ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (K σ : ℝ) :
    Measurable (fun p : ℝ × ℝ => weight K α γ μ (max 0 p.1) σ p.2) := by
  have hf := (AxialFlow.clamped_foot_continuous (σ := σ) hα hγ hμ).measurable
  have hS : Measurable (fun p : ℝ × ℝ => S (γ*AxialFlow.foot σ α γ μ (max 0 p.1) p.2/μ)) :=
    continuous_S.measurable.comp ((hf.const_mul γ).div_const μ)
  exact ((hS.const_mul K).div (measurable_const.add
    ((((measurable_const.max measurable_fst).mul_const α).mul_const γ).mul hS))).const_mul (1/4)

theorem clamped_atom_test_measurable {K α γ μ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    (σ : ℝ) {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × ℝ => ∫ v, ψ v ∂atom K α γ μ (max 0 p.1) σ p.2) := by
  have hv := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hμ).measurable
  have hj : Measurable (fun p : ℝ × ℝ =>
      PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1) p.2)) :=
    VelocityWeight.split.symm.measurable.comp (hv.prodMk measurable_const)
  have he : (fun p : ℝ × ℝ => ∫ v, ψ v ∂atom K α γ μ (max 0 p.1) σ p.2) =
      (fun p => weight K α γ μ (max 0 p.1) σ p.2*
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1) p.2))) := by
    funext p
    exact integral_atom hK hα hγ hμ (le_max_left 0 p.1) σ p.2 ψ
  rw [he]
  exact (clamped_weight_measurable hα hγ hμ K σ).mul (hψ.comp hj)

theorem clamped_cell_test_measurable {K α γ μ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × ℝ => ∫ v, ψ v ∂cell K α γ μ (max 0 p.1) p.2) := by
  have he : (fun p : ℝ × ℝ => ∫ v, ψ v ∂cell K α γ μ (max 0 p.1) p.2) =
      (fun p => (∫ v, ψ v ∂atom K α γ μ (max 0 p.1) 1 p.2)+
        ∫ v, ψ v ∂atom K α γ μ (max 0 p.1) (-1) p.2) := by
    funext p
    exact integral_add_measure (integrable_atom _ _ _ _ _ _ _ _)
      (integrable_atom _ _ _ _ _ _ _ _)
  rw [he]
  exact (clamped_atom_test_measurable hK hα hγ hμ 1 hψ).add
    (clamped_atom_test_measurable hK hα hγ hμ (-1) hψ)

end BoltzmannNonuniqueness.AxialBackground

namespace BoltzmannNonuniqueness.GeometricBackground

theorem clamped_background_test_measurable {θ K α γ : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × JetPrototype.Space =>
      ∫ v, ψ v ∂background θ η l K α γ (max 0 p.1) p.2) := by
  let f : ℤ × (ℝ × ℝ) → ℝ := fun p =>
    ∫ v, ψ v ∂AxialBackground.cell K α γ (GeometricMesh.point θ η p.1) (max 0 p.2.1) p.2.2
  have hf : Measurable f := measurable_from_prod_countable_right (fun k =>
    AxialBackground.clamped_cell_test_measurable hK hα hγ (GeometricMesh.point_pos hθ η k) hψ)
  have hi : Measurable (fun p : ℝ × JetPrototype.Space =>
      (GeometricMesh.index (‖p.2.1‖/θ) η,(p.1,p.2.2))) := by
    unfold GeometricMesh.index
    fun_prop
  have hm := hf.comp hi
  have ha : MeasurableSet {p : ℝ × JetPrototype.Space | active θ η l p.2.1} :=
    (active_measurableSet θ η l).preimage measurable_snd.fst
  have he : (fun p : ℝ × JetPrototype.Space =>
      ∫ v, ψ v ∂background θ η l K α γ (max 0 p.1) p.2) =
      {p : ℝ × JetPrototype.Space | active θ η l p.2.1}.indicator
        (fun p => f (GeometricMesh.index (‖p.2.1‖/θ) η,(p.1,p.2.2))) := by
    funext p
    by_cases hp : active θ η l p.2.1 <;> simp [background,hp,f,scale]
  rw [he]
  exact hm.indicator ha

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The loss frequency of the limiting atomic medium -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.GeometricBackground

def frequency (θ η l K α γ t : ℝ) (x : JetPrototype.Space) (v : Velocity) : ℝ :=
  2*Real.pi*∫ p, ‖v-p‖ ∂background θ η l K α γ t x

theorem integrable_test (θ η l K α γ t : ℝ) (x : JetPrototype.Space) (ψ : Velocity → ℝ) :
    Integrable ψ (background θ η l K α γ t x) := by
  classical
  unfold background
  split_ifs
  · exact (AxialBackground.integrable_atom _ _ _ _ _ _ _ _).add_measure
      (AxialBackground.integrable_atom _ _ _ _ _ _ _ _)
  · exact integrable_zero_measure

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Relative weights of the actual compressed cold beams -/

noncomputable section

open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

def relativeWeight (r α γ μ t σ z : ℝ) : ℝ :=
  r/μ * S (γ*AxialFlow.foot σ α γ μ t z/μ) /
    (1+(t*α*γ/μ)*S (γ*AxialFlow.foot σ α γ μ t z/μ))

end BoltzmannNonuniqueness.AxialBackground

end

end

section

/-! # The limiting medium as a measurable finite kernel on positive-time slabs -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.GeometricBackground

theorem background_finite (θ η l K α γ t : ℝ) (x : JetPrototype.Space) :
    IsFiniteMeasure (background θ η l K α γ t x) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ) ≠ 0)).mp
    (integrable_test θ η l K α γ t x (fun _ => 1))

theorem clamped_background_measurable {θ K α γ : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ) :
    Measurable (fun p : ℝ × JetPrototype.Space =>
      background θ η l K α γ (max 0 p.1) p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm := (clamped_background_test_measurable hθ hK hα hγ η l
    (measurable_const.indicator hs : Measurable (s.indicator (fun _ : Velocity => (1:ℝ))))).ennreal_ofReal
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  let _ := background_finite θ η l K α γ (max 0 p.1) p.2
  rw [integral_indicator_const (1:ℝ) hs]
  simp only [smul_eq_mul,mul_one]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ s)).symm

def slabKernel {a θ K α γ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (η l : ℝ) : Kernel (ℝ × JetPrototype.Space) Velocity where
  toFun p := background θ η l K α γ (max a p.1) p.2
  measurable' := by
    have hi : Measurable (fun p : ℝ × JetPrototype.Space => (max a p.1,p.2)) :=
      (measurable_const.max measurable_fst).prodMk measurable_snd
    have hm := (clamped_background_measurable hθ hK hα.le hγ.le η l).comp hi
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    change background θ η l K α γ (max a p.1) p.2 =
      background θ η l K α γ (max 0 (max a p.1)) p.2
    rw [max_eq_right (ha.le.trans (le_max_left a p.1))]

theorem slabKernel_finite {a θ K α γ l : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (η : ℝ) (hl : 0 ≤ l) :
    IsFiniteKernel (slabKernel ha hθ hK hα hγ η l) := by
  let C := 2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))
  refine ⟨⟨ENNReal.ofReal C,ENNReal.ofReal_lt_top,fun p => ?_⟩⟩
  let _ := background_finite θ η l K α γ (max a p.1) p.2
  have hb := moment_bound (η := η) hθ hl hK hα hγ (ha.trans_le (le_max_left a p.1)) p.2 0
  simp only [pow_zero,mul_one] at hb
  rw [integral_const] at hb
  simp only [smul_eq_mul,mul_one] at hb
  have hc : 2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+max a p.1))) ≤ C := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha
      (by linarith [le_max_left a p.1])
  change background θ η l K α γ (max a p.1) p.2 univ ≤ ENNReal.ofReal C
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ univ)]
  exact ENNReal.ofReal_le_ofReal (hb.trans hc)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A quantitative positive cold weight on bounded time and scale intervals -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

def compactWeightLower (K α γ m M T Z : ℝ) : ℝ :=
  (1/4)*(K*S (γ*(Z+T*(1+α))/m)/(M+T*α*γ))

end BoltzmannNonuniqueness.AxialBackground

end

end

section

/-! # The hot cap cancels the inverse-time background loss coefficient -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def lossCoefficient (K α γ : ℝ) : ℝ :=
  (2*Real.pi)*(2*((1/4)*(K*max 1 (α*γ)⁻¹)))

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricPositiveCompact
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable two-beam coefficients from the actual geometric cold profiles -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def beamVelocity (θ η α γ σ : ℝ) (p : ℝ × Velocity) : Velocity :=
  PlaneChart.join 0 (AxialFlow.velocity σ α γ (scale θ η (transverse p.2))
    (max 0 p.1) (axial p.2))

def beamDensity (θ η α γ r σ : ℝ) (p : ℝ × Velocity) : ℝ :=
  4*r*AxialBackground.weight 1 α γ (scale θ η (transverse p.2))
    (max 0 p.1) σ (axial p.2)

theorem beamVelocity_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η σ : ℝ) : Measurable (beamVelocity θ η α γ σ) := by
  let f : ℤ × (ℝ × ℝ) → Velocity := fun p =>
    PlaneChart.join 0 (AxialFlow.velocity σ α γ (GeometricMesh.point θ η p.1)
      (max 0 p.2.1) p.2.2)
  have hf : Measurable f := measurable_from_prod_countable_right (fun k =>
    split.symm.measurable.comp
      (((AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ
        (GeometricMesh.point_pos hθ η k)).measurable).prodMk measurable_const))
  have hs : Measurable (fun p : ℝ × Velocity => (axial p.2,transverse p.2)) := by
    simpa only [Function.comp_def,split_apply] using split.measurable.comp
      (show Measurable (Prod.snd : ℝ × Velocity → Velocity) from measurable_snd)
  have hi : Measurable (fun p : ℝ × Velocity =>
      (GeometricMesh.index (‖transverse p.2‖/θ) η,(p.1,axial p.2))) := by
    unfold GeometricMesh.index
    exact ((hs.snd.norm.div_const θ).log.div_const η).floor.prodMk
      (measurable_fst.prodMk hs.fst)
  change Measurable (fun p : ℝ × Velocity => PlaneChart.join 0
    (AxialFlow.velocity σ α γ (GeometricMesh.point θ η (GeometricMesh.index (‖transverse p.2‖/θ) η))
      (max 0 p.1) (axial p.2)))
  simpa only [Function.comp_def,f] using hf.comp hi

theorem beamDensity_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η r σ : ℝ) : Measurable (beamDensity θ η α γ r σ) := by
  let f : ℤ × (ℝ × ℝ) → ℝ := fun p =>
    4*r*AxialBackground.weight 1 α γ (GeometricMesh.point θ η p.1)
      (max 0 p.2.1) σ p.2.2
  have hf : Measurable f := measurable_from_prod_countable_right (fun k =>
    (AxialBackground.clamped_weight_measurable hα hγ (GeometricMesh.point_pos hθ η k) 1 σ).const_mul (4*r))
  have hs : Measurable (fun p : ℝ × Velocity => (axial p.2,transverse p.2)) := by
    simpa only [Function.comp_def,split_apply] using split.measurable.comp
      (show Measurable (Prod.snd : ℝ × Velocity → Velocity) from measurable_snd)
  have hi : Measurable (fun p : ℝ × Velocity =>
      (GeometricMesh.index (‖transverse p.2‖/θ) η,(p.1,axial p.2))) := by
    unfold GeometricMesh.index
    exact ((hs.snd.norm.div_const θ).log.div_const η).floor.prodMk
      (measurable_fst.prodMk hs.fst)
  change Measurable (fun p : ℝ × Velocity => 4*r*AxialBackground.weight 1 α γ
    (GeometricMesh.point θ η (GeometricMesh.index (‖transverse p.2‖/θ) η))
      (max 0 p.1) σ (axial p.2))
  simpa only [Function.comp_def,f] using hf.comp hi

def beamCoefficients {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η r : ℝ) : ReferenceGeometry.BeamCoefficients where
  plusPartner := beamVelocity θ η α γ 1
  minusPartner := beamVelocity θ η α γ (-1)
  plusDensity := beamDensity θ η α γ r 1
  minusDensity := beamDensity θ η α γ r (-1)
  plusPartner_measurable := beamVelocity_measurable hθ hα hγ η 1
  minusPartner_measurable := beamVelocity_measurable hθ hα hγ η (-1)
  plusDensity_measurable := beamDensity_measurable hθ hα hγ η r 1
  minusDensity_measurable := beamDensity_measurable hθ hα hγ η r (-1)

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedCollisionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Complete sup-norm space of bounded measurable representatives

This space is used for the fixed-cutoff positive iteration. It retains
pointwise representatives, so every iterated collision integral is defined.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.BoundedMeasurable

variable (X : Type*) [MeasurableSpace X]

abbrev SupSpace := lp (fun _ : X => ℝ) ⊤

def measurableSet : Set (SupSpace X) := {f | Measurable (fun x => f x)}

theorem measurableSet_closed : IsClosed (measurableSet X) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u f hu hf
  apply measurable_of_tendsto_metrizable (fun n => hu n)
  exact (lp.uniformContinuous_coe (p := ⊤)).continuous.tendsto f |>.comp hf

abbrev Space := {f : SupSpace X // f ∈ measurableSet X}

instance instCompleteSpaceSpace : CompleteSpace (Space X) := (measurableSet_closed X).isComplete.completeSpace_coe

instance instCoeFunSpaceForallReal : CoeFun (Space X) (fun _ => X → ℝ) := ⟨fun f => f.val⟩

theorem measurable (f : Space X) : Measurable (fun x => f x) := f.property

def ofBounded (f : X → ℝ) (hm : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Space X := ⟨⟨f, memℓp_infty ⟨C, by rintro _ ⟨x, rfl⟩; simpa only [Real.norm_eq_abs] using hC x⟩⟩, hm⟩

@[simp] theorem ofBounded_apply (f : X → ℝ) (hm : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (x : X) : ofBounded X f hm C hC x = f x := rfl

theorem dist_apply_le (f g : Space X) (x : X) : |f x - g x| ≤ dist f g := by
  simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_one, one_mul] using
    (lp.lipschitzWith_one_eval (E := fun _ : X => ℝ) ⊤ x).dist_le_mul f.val g.val

theorem dist_le {f g : Space X} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f x - g x| ≤ C) :
    dist f g ≤ C := by
  change dist f.val g.val ≤ C
  rw [dist_eq_norm]
  apply lp.norm_le_of_forall_le hC
  intro x
  exact (Real.norm_eq_abs _).symm ▸ h x

def positiveBall (R : ℝ) : Set (Space X) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R}

theorem positiveBall_closed (R : ℝ) : IsClosed (positiveBall X R) := by
  have he (x : X) : Continuous (fun f : Space X => f x) :=
    (lp.lipschitzWith_one_eval (E := fun _ : X => ℝ) ⊤ x).continuous.comp continuous_subtype_val
  convert isClosed_iInter (fun x => (isClosed_le (f := fun _ => (0 : ℝ)) continuous_const (he x)).inter
    (isClosed_le (he x) (g := fun _ => R) continuous_const)) using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  simp only [positiveBall, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]

abbrev PositiveBall (R : ℝ) := {f : Space X // f ∈ positiveBall X R}

instance instCompleteSpacePositiveBall (R : ℝ) : CompleteSpace (PositiveBall X R) :=
  (positiveBall_closed X R).isComplete.completeSpace_coe

end BoltzmannNonuniqueness.BoundedMeasurable

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1ToWeakStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The weak-star cold / strong-L1 hot product passage -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

def WeakStarLInfConverges {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : ℕ → X → ℝ) (b : X → ℝ) : Prop :=
  Measurable b ∧ ∀ ψ : X → ℝ, Integrable ψ μ →
    Tendsto (fun n => ∫ x, ψ x*a n x ∂μ) atTop (𝓝 (∫ x, ψ x*b x ∂μ))

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive integral contraction along measurable characteristics

This lemma constructs a fixed point of a bounded positive source map.
The collision source and its quantitative estimates are supplied separately.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

abbrev Domain (P : Type*) := ℝ × P

def time (T t : ℝ) : ℝ := max 0 (min T t)

theorem time_bounds {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    0 ≤ time T t ∧ time T t ≤ T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

def value (T L : ℝ) (flow : ℝ → P → P) (f₀ : P → ℝ)
    (g : Domain P → ℝ) (z : Domain P) : ℝ :=
  Real.exp (-L * time T z.1) * f₀ (flow (-time T z.1) z.2) +
    ∫ r in 0..time T z.1,
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)

theorem measurable_value {T L : ℝ} (hT : 0 ≤ T) {flow : ℝ → P → P}
    (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀ : Measurable f₀) {g : Domain P → ℝ} (hg : Measurable g) :
    Measurable (value T L flow f₀ g) := by
  have ht : Measurable (fun z : Domain P => time T z.1) := by unfold time; fun_prop
  have hm : Measurable (fun z : Domain P =>
      ∫ r : ℝ, if 0 < r ∧ r ≤ time T z.1 then
        Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) else 0) := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    have hfl : Measurable (fun q : Domain P × ℝ => flow (q.2 - time T q.1.1) q.1.2) :=
      hflow.comp ((measurable_snd.sub (ht.comp measurable_fst)).prodMk measurable_fst.snd)
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (ht.comp measurable_fst))
    · have he : Measurable (fun q : Domain P × ℝ => Real.exp (-L * (time T q.1.1 - q.2))) := by
        unfold time
        fun_prop
      exact he.mul (hg.comp (measurable_snd.prodMk hfl))
    · exact measurable_const
  have he (z : Domain P) : (∫ r in 0..time T z.1,
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)) =
      ∫ r : ℝ, if 0 < r ∧ r ≤ time T z.1 then
        Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) else 0 := by
    rw [intervalIntegral.integral_of_le (time_bounds hT z.1).1, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by simp only [Set.indicator_apply, Set.mem_Ioc])
  unfold value
  simp_rw [he]
  have he : Measurable (fun z : Domain P => Real.exp (-L * time T z.1)) := by
    unfold time
    fun_prop
  exact (he.mul (hf₀.comp (hflow.comp ((ht.neg).prodMk measurable_snd)))).add hm

omit [MeasurableSpace P] in
theorem value_bounds {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (_hA : 0 ≤ A)
    (hS : 0 ≤ S) (flow : ℝ → P → P) {f₀ : P → ℝ}
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) {g : Domain P → ℝ}
    (hg : ∀ z, 0 ≤ g z ∧ g z ≤ S)
    (z : Domain P) : 0 ≤ value T L flow f₀ g z ∧ value T L flow f₀ g z ≤ A + T * S := by
  have ht := time_bounds hT z.1
  have he (r : ℝ) (hr : r ∈ Icc 0 (time T z.1)) :
      0 ≤ Real.exp (-L * (time T z.1 - r)) ∧ Real.exp (-L * (time T z.1 - r)) ≤ 1 := by
    exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [hr.2])⟩
  have hi : (∫ r in 0..time T z.1,
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)) ≤ S * time T z.1 := by
    apply (le_abs_self _).trans
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0)
      (b := time T z.1) (C := S) (f := fun r =>
        Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2))
      (fun r hr => by
        rw [uIoc_of_le ht.1] at hr
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg _).1)]
        exact (mul_le_mul_of_nonneg_right (he r ⟨hr.1.le, hr.2⟩).2 (hg _).1).trans
          (by simpa using (hg _).2))
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using h
  constructor
  · exact add_nonneg (mul_nonneg (Real.exp_pos _).le (hf₀ _).1)
      (intervalIntegral.integral_nonneg ht.1 (fun r _ => mul_nonneg (Real.exp_pos _).le (hg _).1))
  · have hinit : Real.exp (-L * time T z.1) * f₀ (flow (-time T z.1) z.2) ≤ A :=
      (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith)) (hf₀ _).1).trans
        (by simpa using (hf₀ _).2)
    exact (add_le_add hinit hi).trans (by nlinarith)

theorem damped_integrable {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {g : Domain P → ℝ} (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S)
    (z : Domain P) : IntervalIntegrable (fun r =>
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2)) volume 0 (time T z.1) := by
  apply (intervalIntegrable_const (c := S)).mono_fun'
  · have hm : Measurable (fun r : ℝ => flow (r - time T z.1) z.2) :=
      hflow.comp ((measurable_id.sub measurable_const).prodMk measurable_const)
    have he : Measurable (fun r : ℝ => Real.exp (-L * (time T z.1 - r))) := by fun_prop
    exact (he.mul (hgm.comp (measurable_id.prodMk hm))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    rw [uIoc_of_le (time_bounds hT z.1).1] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hg _)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Removing the auxiliary exponential weight from a mild solution -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.PositiveIntegral
variable {P : Type*}

theorem value_rescale {T : ℝ} (hT : 0 ≤ T) (a L : ℝ) (flow : ℝ → P → P)
    (f₀ : P → ℝ) (g : Domain P → ℝ) (z : Domain P) :
    Real.exp (a*time T z.1) * value T (a+L) flow f₀
      (fun w => Real.exp (-a*time T w.1)*g w) z = value T L flow f₀ g z := by
  have ht := time_bounds hT z.1
  have hi : Real.exp (a*time T z.1)*Real.exp (-(a+L)*time T z.1) =
      Real.exp (-L*time T z.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he (r : ℝ) : Real.exp (a*time T z.1)*Real.exp (-(a+L)*(time T z.1-r))*Real.exp (-a*r) =
      Real.exp (-L*(time T z.1-r)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold value
  rw [mul_add,← mul_assoc,hi,← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  have hrT : r ≤ T := hr.2.trans ht.2
  have hrt : time T r = r := by
    unfold time
    rw [min_eq_right hrT,max_eq_right hr.1]
  dsimp only
  rw [hrt]
  calc
    _ = (Real.exp (a*time T z.1)*Real.exp (-(a+L)*(time T z.1-r))*Real.exp (-a*r))*
      g (r,flow (r-time T z.1) z.2) := by ring
    _ = _ := by rw [he]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedCollisionHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Time-uniform contraction estimates for the positive damped integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PositiveIntegral

theorem exponential_integral {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (∫ r in 0..t, Real.exp (-L*(t-r))) = (1-Real.exp (-L*t))/L := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (-L*(t-r))/L)
      (Real.exp (-L*(t-r))) r := by
    refine ((((hasDerivAt_const r t).sub (hasDerivAt_id r)).const_mul (-L)).exp.div_const L).congr_deriv (Eq.symm ?_)
    · dsimp only [Pi.sub_apply, id_eq]
      field_simp [hL.ne']
      ring
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-L*(t-r))) volume 0 t :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (-L*(t-r)))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi
  simpa only [sub_self,mul_zero,Real.exp_zero,sub_zero,div_sub_div_same] using h

variable {P : Type*} [MeasurableSpace P]

theorem value_damped_bound {T L R : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hR : 0 ≤ R)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ R)
    {g : Domain P → ℝ} (hgm : Measurable g) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ L*R)
    (z : Domain P) : 0 ≤ value T L flow f₀ g z ∧ value T L flow f₀ g z ≤ R := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL.le hflow hgm
    (fun z => (abs_of_nonneg (hg z).1).trans_le (hg z).2) z
  have hci : IntervalIntegrable (fun r : ℝ => Real.exp (-L*(time T z.1-r))*(L*R))
      volume 0 (time T z.1) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on ht.1 hgi hci (fun r _ =>
    mul_le_mul_of_nonneg_left (hg _).2 (Real.exp_pos _).le)
  have he : (∫ r in 0..time T z.1, Real.exp (-L*(time T z.1-r))*(L*R)) =
      R*(1-Real.exp (-L*time T z.1)) := by
    rw [intervalIntegral.integral_mul_const,exponential_integral hL]
    field_simp [hL.ne']
  rw [he] at hb
  have hinit := mul_le_mul_of_nonneg_left (hf₀ (flow (-time T z.1) z.2)).2
    (Real.exp_pos (-L*time T z.1)).le
  exact ⟨(value_bounds hT hL.le hR (mul_nonneg hL.le hR) flow hf₀ hg z).1,by
    unfold value
    linarith⟩

theorem value_damped_difference {T L S D : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z-h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z-value T L flow f₀ h z| ≤ D/L := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL.le hflow hgm hg z
  have hhi := damped_integrable hT hL.le hflow hhm hh z
  unfold value
  rw [add_sub_add_left_eq_sub,← intervalIntegral.integral_sub hgi hhi]
  have hci : IntervalIntegrable (fun r : ℝ => Real.exp (-L*(time T z.1-r))*D)
      volume 0 (time T z.1) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (f := fun r => Real.exp (-L*(time T z.1-r))*g (r,flow (r-time T z.1) z.2)-
      Real.exp (-L*(time T z.1-r))*h (r,flow (r-time T z.1) z.2))
    (g := fun r => Real.exp (-L*(time T z.1-r))*D) (by
      filter_upwards [] with r
      intro _hr
      rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le) hci
  rw [Real.norm_eq_abs,intervalIntegral.integral_mul_const,exponential_integral hL] at hb
  have hn : 0 ≤ Real.exp (-L*time T z.1) := (Real.exp_pos _).le
  calc
    _ ≤ (1-Real.exp (-L*time T z.1))/L*D := hb
    _ ≤ 1/L*D := by gcongr; linarith
    _ = D/L := by ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Positive damped fixed points on arbitrary finite time intervals -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PositiveIntegral
variable {P : Type*} [MeasurableSpace P]

theorem exists_damped_fixed_point {T L R K : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hsmall : K < L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ R)
    (source : BoundedMeasurable.PositiveBall (Domain P) R → Domain P → ℝ)
    (hsm : ∀ f, Measurable (source f))
    (hsb : ∀ f z, 0 ≤ source f z ∧ source f z ≤ L*R)
    (hsl : ∀ f g z, |source f z-source g z| ≤ K*dist f g) :
    ∃ f : BoundedMeasurable.PositiveBall (Domain P) R,
      ∀ z, f.val z = value T L flow f₀ (source f) z := by
  let step : BoundedMeasurable.PositiveBall (Domain P) R →
      BoundedMeasurable.PositiveBall (Domain P) R := fun f =>
    ⟨BoundedMeasurable.ofBounded (Domain P) (value T L flow f₀ (source f))
      (measurable_value hT hflow hf₀m (hsm f)) R
      (fun z => by
        rw [abs_of_nonneg (value_damped_bound hT hL hR hflow hf₀ (hsm f) (hsb f) z).1]
        exact (value_damped_bound hT hL hR hflow hf₀ (hsm f) (hsb f) z).2),
      fun z => value_damped_bound hT hL hR hflow hf₀ (hsm f) (hsb f) z⟩
  have hc : ContractingWith ⟨K/L,div_nonneg hK hL.le⟩ step := by
    constructor
    · exact (div_lt_one hL).mpr hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro f g
      change dist (step f).val (step g).val ≤ (K/L)*dist f g
      apply BoundedMeasurable.dist_le (Domain P) (by positivity)
      intro z
      have h := value_damped_difference hT hL (mul_nonneg hK dist_nonneg) hflow f₀
        (hsm f) (hsm g)
        (fun z => (abs_of_nonneg (hsb f z).1).trans_le (hsb f z).2)
        (fun z => (abs_of_nonneg (hsb g z).1).trans_le (hsb g z).2) (hsl f g) z
      change |value T L flow f₀ (source f) z-value T L flow f₀ (source g) z| ≤ _
      exact h.trans_eq (by ring)
  let zero : BoundedMeasurable.PositiveBall (Domain P) R :=
    ⟨BoundedMeasurable.ofBounded (Domain P) (fun _ => 0) measurable_const 0
      (fun _ => by simp),fun _ => ⟨le_rfl,hR⟩⟩
  let : Nonempty (BoundedMeasurable.PositiveBall (Domain P) R) := ⟨zero⟩
  refine ⟨hc.fixedPoint,?_⟩
  intro z
  have he := congrArg (fun f : BoundedMeasurable.PositiveBall (Domain P) R => f.val z)
    hc.fixedPoint_isFixedPt
  exact he.symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Integrability along the actual damped transport lines in Fourier coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def dampedLineResolvent (f : FourierSpace → ℂ) (w x : FourierSpace) : ℂ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-s) • f (x-s • w)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBranchingBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak calculus for the actual damped characteristic formula -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

def damped (L c : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-L*t) * (c + ∫ r in 0..t, Real.exp (L*r)*g r)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveComparisonBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact entropy dissipation for positive bounded cutoff densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def positiveCutoffProduction (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (1/4:ℝ)*collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
    (truncatedPostRate b f z-truncatedPreRate b f z)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffEntropyMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The extended nonnegative cutoff dissipation agrees with positive production -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def cutoffExtendedProduction (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ≥0∞ :=
  if ‖z.1.2.1-z.1.2.2‖ < b then
    ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*
      extendedEntropyProduction
        (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))
  else 0

def cutoffExtendedDissipation (μ : Measure X) (b : ℝ) (f : X × Velocity → ℝ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹*∫⁻ z, cutoffExtendedProduction b f z
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite time measure equivalent to Lebesgue measure on every time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def timeWeight (t : ℝ) : ℝ := Real.exp (-(t^2))
def finiteTimeMeasure : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (timeWeight t))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Positive local cutoff iteration along the actual free transport -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

def state (f : ℝ × JetPrototype.Phase → ℝ) (z : (ℝ × Space) × Velocity) : ℝ :=
  f (z.1.1, (z.1.2, z.2))

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Actual positive mild solutions for bounded Gaussian cutoff data -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

theorem time_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : PositiveIntegral.time T t = t := by
  unfold PositiveIntegral.time
  rw [min_eq_right ht.2, max_eq_right ht.1]

end BoltzmannNonuniqueness.GaussianLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdGaussianFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The scalar integral Gronwall step in cold-color comparison -/

noncomputable section

open MeasureTheory Set Filter

namespace BoltzmannNonuniqueness.ColdGronwall

def primitive (z : ℝ → ℝ) (t : ℝ) : ℝ := ∫ r in 0..t, z r

end BoltzmannNonuniqueness.ColdGronwall

end

end

section

/-! # Polynomial smallness of a cold Gaussian away from the velocity axis -/
noncomputable section
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetSupersolution

def transverseDecayConstant (K d₀ ε : ℝ) : ℝ :=
  4*Real.exp 4*JetThermalKernel.bound*K*d₀/ε^4

end BoltzmannNonuniqueness.JetSupersolution

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FlightMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free-flight measure preservation and representative invariance -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

abbrev phaseVolume : Measure JetPrototype.Phase := JetPrototype.spaceVolume.prod volume

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (JetBarrier.flight t) phaseVolume phaseVolume := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : JetPrototype.Space) =>
      x + (t • VelocityWeight.transverse v,t * VelocityWeight.axial v))) := by
    unfold Function.uncurry VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  have hskew := (MeasurePreserving.id (volume : Measure Velocity)).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right JetPrototype.spaceVolume
      (t • VelocityWeight.transverse v,t * VelocityWeight.axial v)).map_eq))
  have hswap₁ : MeasurePreserving Prod.swap phaseVolume
      ((volume : Measure Velocity).prod JetPrototype.spaceVolume) := Measure.measurePreserving_swap
  have hswap₂ : MeasurePreserving Prod.swap
      ((volume : Measure Velocity).prod JetPrototype.spaceVolume) phaseVolume := Measure.measurePreserving_swap
  convert hswap₂.comp (hskew.comp hswap₁) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rfl

end BoltzmannNonuniqueness.FlightMeasure

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseDecompositionNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The essential supremum norm along free transport -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

open FlightMeasure

def size (f : JetPrototype.Phase → ℝ) : ℝ := (eLpNorm f ∞ phaseVolume).toReal

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Bounded representatives that realize the essential upper bound -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

def canonical (f : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  min (f u) (size (fun p => f (u.1,p)))

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPhysicalSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A fixed negligible velocity set for the weighted local construction

The exceptional set depends only on H and its proved quadratic gain bound,
not on a solution or an iterate. Setting the gain to zero there preserves
its almost-everywhere collision meaning and gives pointwise bounded sources.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRepresentative

def good (q : ℝ) : Set Velocity := {v |
  nonnegativeGain (fun w => ENNReal.ofReal (H q w)) (fun w => ENNReal.ofReal (H q w)) v ≤
    ENNReal.ofReal (HotApplication.realBound q * H q v)}

variable {X : Type*} [MeasurableSpace X]

def density (q : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := H q p.2 * f p

def gain (q b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := by
  classical
  exact if p.2 ∈ good q then KineticCollisionNullSets.gain b (density q f) p / H q p.2 else 0

def frequency (q b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  KineticCollisionNullSets.frequency b (density q f) p

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Bounded positive source for the H-weighted local equation -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

def source (q b L : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain q b f p + (L - frequency q b f p) * f p

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetColdLimitComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Gaussian control of the actual finite annular datum -/

noncomputable section

open MeasureTheory
open scoped BigOperators
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetFiniteGaussian

def indices (N : ℕ) : Finset JetDatum.Index := (Finset.range N).product Finset.univ

def coefficient (s₀ η K d₀ : ℝ) (j : ℕ) : ℝ :=
  Real.exp 8 * (K / jetScale s₀ η j) * ((d₀ * jetScale s₀ η j ^ 10) ^ 3)⁻¹ * JetThermalKernel.bound

def amplitude (s₀ η K d₀ : ℝ) (N : ℕ) : ℝ :=
  1 + ∑ i ∈ indices N, coefficient s₀ η K d₀ i.1

end BoltzmannNonuniqueness.JetFiniteGaussian

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive local iteration in the manuscript's singular weighted norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

def forcing (q b L : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  HotRepresentative.source q b L (GaussianLocal.state f) ((z.1,z.2.1),z.2.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Uniform frequency control by a cold core and the cap weight -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def weightFrequencyConstant (q V : ℝ) : ℝ :=
  2*Real.pi*(V*(∫ w, H q w)+(∫ w, ‖w‖*H q w))

end BoltzmannNonuniqueness

end

end

section

/-! # The actual finite periodic datum in the singular weighted space -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedFiniteSeed

def amplitude (s₀ η K d₀ : ℝ) (N : ℕ) : ℝ :=
  JetFiniteGaussian.amplitude s₀ η K d₀ N * tiltConstant

end BoltzmannNonuniqueness.WeightedFiniteSeed

end

end

section

/-! # Common-loss cold source in the singular weighted space -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

def coldSource (q b L : ℝ) (F c : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain q b c p + (L-frequency q b F p)*c p

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive cold iteration beneath the H-weighted total solution -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

def coldForcing (q b L : ℝ) (F c : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state c) ((z.1,z.2.1),z.2.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Spatial covariance of the constructed weighted cold solutions -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

def shift (y : Space) (p : JetPrototype.Phase) : JetPrototype.Phase := (p.1-y,p.2)

def pull (y : Space) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  f (z.1,shift y z.2)

end BoltzmannNonuniqueness.WeightedTranslation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongMassClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded mass coefficients preserve strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def massClip (K r : ℝ) : ℝ := min K (1+r)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotCollisionDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Replacing only the hot remainder by an essential-norm representative -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.HotCanonical

def replacement (F C : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  C u+PhaseEssSup.canonical (fun z => F z-C z) u

end BoltzmannNonuniqueness.HotCanonical

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedNetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Almost-everywhere invariance of the colored forcing along spacetime -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

def remainderForcing {I : Type*} (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c : I → ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  forcing q b L F u-∑' i, coldForcing q b L F (c i) u

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Mild equations stable under changing spatial representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.WeightedLocal

/-- The mild identity on every time slice, with spatial null sets allowed to depend on time. -/
def MildAE (q b L T : ℝ) (f₀ : JetPrototype.Phase → ℝ)
    (F : ℝ × JetPrototype.Phase → ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) (t,p))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdFiniteLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive cold iteration without a pointwise total fixed point -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

def clippedColdPicard (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) : ℕ → ℝ × JetPrototype.Phase → ℝ
  | 0 => fun _ => 0
  | n+1 => fun u => min (F u) (PositiveIntegral.value T L JetBarrier.flight c₀
      (coldForcing q b L F (clippedColdPicard q b L T F c₀ n)) u)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The bounded monotone cold limit for a measurable total state -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

def clippedColdLimit (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  ⨆ n, clippedColdPicard q b L T F c₀ n u

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotCanonicalFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A canonical representative above each cold color -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotCanonical

variable {I : Type*} [Countable I]

def familyReplacement (F : ℝ × JetPrototype.Phase → ℝ)
    (c : I → ℝ × JetPrototype.Phase → ℝ) : ℝ × JetPrototype.Phase → ℝ :=
  replacement F (fun u => ∑' i, c i u)

end BoltzmannNonuniqueness.HotCanonical

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdMildRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Pointwise dominated representatives of an almost-everywhere cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

def normalizedFamily (F : ℝ × JetPrototype.Phase → ℝ)
    (c : I → ℝ × JetPrototype.Phase → ℝ) (i : I) (u : ℝ × JetPrototype.Phase) : ℝ := by
  classical
  exact if ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u then c i u else 0

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Product-space integrability and measure change for the spatial dilation -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness.ColdDilationMeasure

def spaceEquiv (r : ℝ) (hr : r ≠ 0) : JetPrototype.Space ≃ᵐ JetPrototype.Space :=
  (Homeomorph.smul (Units.mk0 r hr)).toMeasurableEquiv

def phaseEquiv (r : ℝ) (hr : r ≠ 0) : JetPrototype.Phase ≃ᵐ JetPrototype.Phase :=
  (spaceEquiv r hr).prodCongr (MeasurableEquiv.refl Velocity)

end BoltzmannNonuniqueness.ColdDilationMeasure

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RebuiltHotInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A pointwise summable cold family over an almost-everywhere mild total state -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

def rebuiltColdFamily (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c₀ : I → JetPrototype.Phase → ℝ) : I → ℝ × JetPrototype.Phase → ℝ :=
  normalizedFamily F (fun i => clippedColdLimit q b L T F (c₀ i))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common positive local time for bounded weighted data -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocalControl

def damping (q b A : ℝ) : ℝ := 2*A*CutoffLipschitz.frequencyConstant q b

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_PeriodicJetFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably labeled periodic copies of the finite cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

instance instCountableLabel : Countable JetLattice.Label := Function.Injective.countable
  (f := fun i : JetLattice.Label => (i.annulus,i.positive,i.lattice)) (by
    intro i j h
    cases i; cases j
    simpa using h)

def displacement (n : JetLattice.Lattice) : Space :=
  (JetLattice.transverseShift n,JetLattice.axialShift n)

def color (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) : ℝ :=
  if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive) (shift (displacement i.lattice) p) / H q p.2
  else 0

def seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) : ℝ :=
  ∑' i, color s₀ η K α γ d₀ q N i p

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact periodicity of the labeled initial datum -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def relabel (n : JetLattice.Lattice) : JetLattice.Label ≃ JetLattice.Label where
  toFun i := ⟨i.annulus,i.positive,i.lattice+n⟩
  invFun i := ⟨i.annulus,i.positive,i.lattice-n⟩
  left_inv i := by cases i; simp
  right_inv i := by cases i; simp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual labeled periodic approximation on a common local interval -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def initial (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (h₀ : JetPrototype.Phase → ℝ) (p : JetPrototype.Phase) : ℝ :=
  seed s₀ η K α γ d₀ q N p+h₀ p

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The escaped-family estimate in the actual label indexing -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

def coordinates : Label ≃ ℕ × (Bool × Lattice) where
  toFun i := (i.annulus,i.positive,i.lattice)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv i := by cases i; rfl
  right_inv p := rfl

def escaped (s₀ η t : ℝ) (N : ℕ) (x : Velocity) (f : Label → ℝ) (i : Label) : ℝ :=
  by
    classical
    exact if i.annulus < N ∧ JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice
      then f i else 0

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Annular half-Gaussian moment bound for the periodic geometric decomposition -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

def escapedConstant (s₀ η K α d₀ : ℝ) : ℝ :=
  JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotSeedCoreLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A localized periodic thermal seed, normalized in the singular weighted norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

def centered (x : ℝ) : ℝ := Int.fract (x+1/2)-1/2

def centeredSpace (x : Space) : Space :=
  (WithLp.toLp 2 (fun i => centered (x.1 i)),centered x.2)

def raw (q δ : ℝ) (p : JetPrototype.Phase) : ℝ :=
  JetThermalKernel.J (δ⁻¹ • PlaneChart.join (centeredSpace p.1).1 (centeredSpace p.1).2)*
    (JetThermalKernel.J p.2/H q p.2)

def bound : ℝ := JetThermalKernel.bound^2*Real.exp 2*tiltConstant

def normalized (q δ : ℝ) (p : JetPrototype.Phase) : ℝ :=
  (δ/PhaseEssSup.size (raw q δ))*raw q δ p

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Scale-independent amplitude bound for the localized thermal seed -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotSeedProfile

def velocityCore : Set Velocity := {v | ‖v‖ < 1/2 ∧ 1/8 < ‖transverse v‖}

def velocityBound (q : ℝ) : ℝ := 1+(1/8 : ℝ)^(-q)

def normLower (q : ℝ) : ℝ := JetThermalKernel.bound^2/velocityBound q

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # Vanishing of the actual hot seed on the spatial torus -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotSeedProfile

def periodicDensity (q δ : ℝ) : Density :=
  fun p => JetPeriodicDatum.pullback (normalized q δ) p * H q p.2

end BoltzmannNonuniqueness.HotSeedProfile

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual periodic shooting data converge to the common cold datum in L¹ -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetPeriodicDatum

def truncated (s₀ η K α γ d₀ : ℝ) (N : ℕ) : Density :=
  pullback (JetTruncation.truncated s₀ η K α γ d₀ N)

end BoltzmannNonuniqueness.JetPeriodicDatum

namespace BoltzmannNonuniqueness.JetCopyDatum

def periodicInitial (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (ell : ℝ) : Density :=
  fun p => JetPeriodicDatum.pullback (initial s₀ η K α γ d₀ q N
    (fun z => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) z)) p * H q p.2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Essential-norm source estimate for the actual periodic hot remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def scalarMajorant (s₀ η K α γ d₀ q A : ℝ) (N : ℕ) (t z : ℝ) : ℝ :=
  (2*JetMainGain.coefficient K α γ q/(JetGeometry.jetScale s₀ η N+t))*z +
    2*HotApplication.realBound q*z^2 +
    (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      ((JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A)/t)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Spatial regularity of the two terms in thermal concentration -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def limitingCoefficient (K α γ μ t σ : ℝ) (ψ : Velocity → ℝ)
    (x : JetPrototype.Space) : ℝ :=
  compressed K α γ μ t (AxialFlow.foot σ α γ μ t x.2)*
    ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t x.2))

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # A finite cold-norm bound from one core and the escaped tail -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

def colorAmplitude (K α s d : ℝ) : ℝ :=
  2*JetGaussianEscape.constant α*(K/s)*(d^3)⁻¹*VelocityWeight.tiltConstant

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A finite uniform-in-time norm bound for the retained cold family -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

def finiteAmplitude (s₀ η K α d₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), colorAmplitude K α (JetGeometry.jetScale s₀ η j)
    (d₀*JetGeometry.jetScale s₀ η j^10)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A fixed-truncation bound for the full periodic cold sum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def coldNormBound (s₀ η K α d₀ : ℝ) (N : ℕ) : ℝ :=
  finiteAmplitude s₀ η K α d₀ N+
    JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The geometric cold family for an a.e. mild total solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def rebuilt (s₀ η K α γ d₀ q b L T : ℝ) (N : ℕ)
    (F : ℝ × JetPrototype.Phase → ℝ) : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ :=
  rebuiltColdFamily q b L T F (color s₀ η K α γ d₀ q N)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapDilationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The attained cap ratio and its uniform perturbation bound -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Cap

def peak (T δ : ℝ) (z : ℝ → ℝ) : ℝ := sSup ((fun t => z t/(t+δ)) '' Icc 0 T)

end BoltzmannNonuniqueness.Cap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMildApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive periodic mild states and finite-step continuation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

structure PeriodicMildState (q b L T R : ℝ) (f₀ : JetPrototype.Phase → ℝ) where
  value : ℝ × JetPrototype.Phase → ℝ
  measurable_value : Measurable value
  value_bounds : ∀ u, 0 ≤ value u ∧ value u ≤ R
  mild : MildAE q b L T f₀ value
  clamped : ∀ u, value (PositiveIntegral.time T u.1,u.2) = value u
  periodic : ∀ n, pull (JetCopyDatum.displacement n) value = value

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # A bounded collision window preserving the elastic symmetries -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def collisionWindow (N : ℝ) : Set ((X × (Velocity × Velocity)) × Sphere) :=
  {z | ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ N^2}

def windowKernel (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (collisionWindow N).indicator (fun z => collisionKernel z.1.2.1 z.1.2.2 z.2) z

theorem collisionWindow_measurable (N : ℝ) : MeasurableSet (collisionWindow (X := X) N) := by
  apply measurableSet_le _ measurable_const
  fun_prop

theorem windowKernel_measurable (N : ℝ) : Measurable (windowKernel (X := X) N) := by
  apply Measurable.indicator _ (collisionWindow_measurable N)
  unfold collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem collisionWindow_bounds {N : ℝ} (hN : 0 ≤ N)
    {z : (X × (Velocity × Velocity)) × Sphere} (hz : z ∈ collisionWindow N) :
    ‖z.1.2.1‖ ≤ N ∧ ‖z.1.2.2‖ ≤ N := by
  change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ N^2 at hz
  constructor <;> nlinarith [sq_nonneg ‖z.1.2.1‖,sq_nonneg ‖z.1.2.2‖,
    norm_nonneg z.1.2.1,norm_nonneg z.1.2.2]

omit [MeasurableSpace X] in
theorem windowKernel_bounds {N : ℝ} (hN : 0 ≤ N)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ windowKernel N z ∧ windowKernel N z ≤ 2*N := by
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem hz]
    have hb := collisionWindow_bounds hN hz
    exact ⟨collisionKernel_nonneg _ _ _, (collisionKernel_le_norm _ _ _).trans
      ((norm_sub_le _ _).trans (by linarith [hb.1,hb.2]))⟩
  · simp only [windowKernel,indicator_of_notMem hz]
    exact ⟨le_rfl,by positivity⟩

omit [MeasurableSpace X] in
theorem windowKernel_scatter (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    windowKernel N (scatterTriple z) = windowKernel N z := by
  have hω : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have he := scatter_energy z.1.2.1 z.1.2.2 z.2 hω
  have hw : scatterTriple z ∈ collisionWindow N ↔ z ∈ collisionWindow N := by
    change (‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2+
      ‖scatterRight z.1.2.1 z.1.2.2 z.2‖^2 ≤ N^2) ↔ _
    rw [he]
    rfl
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem (hw.mpr hz),windowKernel,indicator_of_mem hz]
    exact collisionKernel_scatter _ _ _ hω
  · rw [windowKernel,indicator_of_notMem (fun h => hz (hw.mp h)),
      windowKernel,indicator_of_notMem hz]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Closedness of the cap under convergence of bounded seed parameters -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

def hotPeak {I : Type*} [Countable I] {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (δ : ℝ) (c₀ : I → JetPrototype.Phase → ℝ) (F : PeriodicMildState q b L T R f₀) : ℝ :=
  Cap.peak T δ (fun t => PhaseEssSup.size (fun p =>
    F.value (t,p)-∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)))

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # A symmetric bounded-rate approximation for global periodic construction -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def rateSum (a b c d : ℝ) : ℝ := a+b+c+d

def pairRate (N a b c d : ℝ) : ℝ :=
  N^2*(a/(N+rateSum a b c d))*(b/(N+rateSum a b c d))

theorem rateSum_nonneg {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ rateSum a b c d := by unfold rateSum; positivity

theorem pairRate_nonneg {N a b c d : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ pairRate N a b c d := by
  have hs := rateSum_nonneg ha hb hc hd
  unfold pairRate
  positivity

theorem pairRate_le_square {N a b c d : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairRate N a b c d ≤ N^2 := by
  have hs := rateSum_nonneg ha hb hc hd
  have hpos : 0 < N+rateSum a b c d := add_pos_of_pos_of_nonneg hN hs
  have h₁ : a/(N+rateSum a b c d) ≤ 1 := (div_le_one hpos).mpr (by unfold rateSum; linarith)
  have h₂ : b/(N+rateSum a b c d) ≤ 1 := (div_le_one hpos).mpr (by unfold rateSum; linarith)
  unfold pairRate
  calc
    _ ≤ N^2*1*1 := by gcongr
    _ = _ := by ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform stability of the regularized collision fractions -/
noncomputable section
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem fraction_difference_le {N a b s t : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (has : a ≤ s) (hb : 0 ≤ b) (hbt : b ≤ t) :
    |a/(N+s)-b/(N+t)| ≤ (|a-b|+|s-t|)/N := by
  have hs : 0 ≤ s := ha.trans has
  have ht : 0 ≤ t := hb.trans hbt
  have hNs : 0 < N+s := add_pos_of_pos_of_nonneg hN hs
  have hNt : 0 < N+t := add_pos_of_pos_of_nonneg hN ht
  have hratio : 0 ≤ b/(N+t) := div_nonneg hb hNt.le
  have hratio1 : b/(N+t) ≤ 1 := (div_le_one hNt).mpr (by linarith)
  have he : a/(N+s)-b/(N+t) = (a-b)/(N+s)+(b/(N+t))*(t-s)/(N+s) := by
    field_simp [hNs.ne', hNt.ne']
    ring
  rw [he]
  calc
    _ ≤ |(a-b)/(N+s)|+|(b/(N+t))*(t-s)/(N+s)| := abs_add_le _ _
    _ = |a-b|/(N+s)+(b/(N+t))*|s-t|/(N+s) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hNs,abs_of_nonneg hratio,abs_sub_comm t s]
    _ ≤ |a-b|/(N+s)+|s-t|/(N+s) := by
      gcongr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hratio1 (abs_nonneg (s-t))
    _ = (|a-b|+|s-t|)/(N+s) := by ring
    _ ≤ (|a-b|+|s-t|)/N := by
      gcongr
      linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global Lipschitz and linear bounds for the bounded collision rates -/
noncomputable section
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem unit_product_difference {a b c d : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    |a*b-c*d| ≤ |b-d|+|a-c| := by
  have he : a*b-c*d = a*(b-d)+(a-c)*d := by ring
  rw [he]
  calc
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ = a*|b-d|+|a-c| *d := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hd]
    _ ≤ 1*|b-d|+|a-c| *1 := by gcongr
    _ = _ := by ring

theorem rateSum_difference_le (a b c d a' b' c' d' : ℝ) :
    |rateSum a b c d-rateSum a' b' c' d'| ≤
      |a-a'|+|b-b'|+|c-c'|+|d-d'| := by
  unfold rateSum
  calc
    _ = |((a-a')+(b-b'))+(c-c')+(d-d')| := by congr 1; ring
    _ ≤ |(a-a')+(b-b')+(c-c')|+|d-d'| := abs_add_le _ _
    _ ≤ (|(a-a')+(b-b')|+|c-c'|)+|d-d'| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a-a'|+|b-b'|+|c-c'|)+|d-d'| := by gcongr; exact abs_add_le _ _

theorem pairRate_difference_le {N a b c d a' b' c' d' : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d') :
    |pairRate N a b c d-pairRate N a' b' c' d'| ≤
      3*N*(|a-a'|+|b-b'|+|c-c'|+|d-d'|) := by
  let S := rateSum a b c d
  let S' := rateSum a' b' c' d'
  have hs : 0 ≤ S := rateSum_nonneg ha hb hc hd
  have hs' : 0 ≤ S' := rateSum_nonneg ha' hb' hc' hd'
  have has : a ≤ S := by dsimp [S,rateSum] <;> linarith
  have hbs : b ≤ S := by dsimp [S,rateSum] <;> linarith
  have has' : a' ≤ S' := by dsimp [S',rateSum] <;> linarith
  have hbs' : b' ≤ S' := by dsimp [S',rateSum] <;> linarith
  have hα : 0 ≤ a/(N+S) := div_nonneg ha (by linarith)
  have hα1 : a/(N+S) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hβ' : 0 ≤ b'/(N+S') := div_nonneg hb' (by linarith)
  have hβ'1 : b'/(N+S') ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hdiff := unit_product_difference (b := b/(N+S)) (c := a'/(N+S')) hα hα1 hβ' hβ'1
  have hfa := fraction_difference_le hN ha has ha' has'
  have hfb := fraction_difference_le hN hb hbs hb' hbs'
  have hsum := rateSum_difference_le a b c d a' b' c' d'
  change |N^2*(a/(N+S))*(b/(N+S))-N^2*(a'/(N+S'))*(b'/(N+S'))| ≤ _
  rw [show N^2*(a/(N+S))*(b/(N+S))-N^2*(a'/(N+S'))*(b'/(N+S')) =
    N^2*((a/(N+S))*(b/(N+S))-(a'/(N+S'))*(b'/(N+S'))) by ring,
    abs_mul,abs_of_nonneg (sq_nonneg N)]
  calc
    _ ≤ N^2*(|b/(N+S)-b'/(N+S')|+|a/(N+S)-a'/(N+S')|) := by gcongr
    _ ≤ N^2*((|b-b'|+|S-S'|)/N+(|a-a'|+|S-S'|)/N) := by gcongr
    _ ≤ N^2*((|b-b'|+(|a-a'|+|b-b'|+|c-c'|+|d-d'|))/N+
      (|a-a'|+(|a-a'|+|b-b'|+|c-c'|+|d-d'|))/N) := by gcongr
    _ ≤ 3*N*(|a-a'|+|b-b'|+|c-c'|+|d-d'|) := by
      field_simp
      nlinarith [abs_nonneg (a-a'),abs_nonneg (b-b'),abs_nonneg (c-c'),abs_nonneg (d-d')]

theorem pairRate_le_linear {N a b c d : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    pairRate N a b c d ≤ N*a := by
  have hs := rateSum_nonneg ha hb hc hd
  have hpos : 0 < N+rateSum a b c d := add_pos_of_pos_of_nonneg hN hs
  have hratio : b/(N+rateSum a b c d) ≤ 1 := (div_le_one hpos).mpr (by unfold rateSum; linarith)
  have haN : a/(N+rateSum a b c d) ≤ a/N := by gcongr; linarith
  unfold pairRate
  calc
    _ ≤ N^2*(a/N)*1 := by gcongr
    _ = N*a := by field_simp [hN.ne']

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual symmetric regularized hard-sphere collision rates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def regularizedPreRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  windowKernel N z * pairRate N (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))

def regularizedPostRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPreRate N f (scatterTriple z)

theorem regularizedPreRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (regularizedPreRate N f) := by
  apply (windowKernel_measurable N).mul
  unfold pairRate rateSum scatterLeft scatterRight normalComponent
  fun_prop

theorem regularizedPostRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (regularizedPostRate N f) :=
  (regularizedPreRate_measurable N hf).comp scatterTriple_measurable

omit [MeasurableSpace X] in
theorem regularizedPostRate_formula (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f z = windowKernel N z *
      pairRate N (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2)) := by
  have hω : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  unfold regularizedPostRate regularizedPreRate
  rw [windowKernel_scatter]
  change windowKernel N z * pairRate N _ _
    (f (z.1.1,scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2))
    (f (z.1.1,scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)) = _
  rw [scatterLeft_involutive _ _ _ hω,scatterRight_involutive _ _ _ hω]
  rfl

omit [MeasurableSpace X] in
theorem regularizedPreRate_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ regularizedPreRate N f z ∧ regularizedPreRate N f z ≤ 2*N^3 := by
  have hw := windowKernel_bounds hN.le z
  have hn := pairRate_nonneg hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hb := pairRate_le_square hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  exact ⟨mul_nonneg hw.1 hn,(mul_le_mul hw.2 hb hn (by positivity)).trans_eq (by ring)⟩

omit [MeasurableSpace X] in
theorem regularizedPreRate_linear {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPreRate N f z ≤ 2*N^2*f (z.1.1,z.1.2.1) := by
  have hw := windowKernel_bounds hN.le z
  have hn := pairRate_nonneg hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hb := pairRate_le_linear hN (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  exact (mul_le_mul hw.2 hb hn (by positivity)).trans_eq (by ring)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Bounded measurable gain and loss in the symmetric approximation -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def fiberMeasure (N : ℝ) : Measure (Velocity × Sphere) :=
  ((volume : Measure Velocity).restrict (Metric.closedBall 0 N)).prod sphereArea

instance fiberMeasure_finite (N : ℝ) : IsFiniteMeasure (fiberMeasure N) := by
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 N)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne
  unfold fiberMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gain (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, regularizedPostRate N f (collisionGrouping.symm (p,q)) ∂fiberMeasure N

def loss (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q, regularizedPreRate N f (collisionGrouping.symm (p,q)) ∂fiberMeasure N

def gainBound (N : ℝ) : ℝ := 2*N^3*(fiberMeasure N).real Set.univ

def lossBound (N : ℝ) : ℝ := 2*N^2*(fiberMeasure N).real Set.univ

theorem gain_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gain N f) :=
  ((regularizedPostRate_measurable N hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem loss_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (loss N f) :=
  ((regularizedPreRate_measurable N hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem pre_fiber_integrable {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    Integrable (fun q => regularizedPreRate N f (collisionGrouping.symm (p,q))) (fiberMeasure N) := by
  apply (integrable_const (2*N^3)).mono'
    (((regularizedPreRate_measurable N hfm).comp collisionGrouping.symm.measurable).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [] with q
  change ‖regularizedPreRate N f (collisionGrouping.symm (p,q))‖ ≤ _
  rw [Real.norm_of_nonneg (regularizedPreRate_bounds hN hf _).1]
  exact (regularizedPreRate_bounds hN hf _).2

theorem post_fiber_integrable {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    Integrable (fun q => regularizedPostRate N f (collisionGrouping.symm (p,q))) (fiberMeasure N) := by
  apply (integrable_const (2*N^3)).mono'
    (((regularizedPostRate_measurable N hfm).comp collisionGrouping.symm.measurable).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards [] with q
  change ‖regularizedPreRate N f (scatterTriple (collisionGrouping.symm (p,q)))‖ ≤ _
  rw [Real.norm_of_nonneg (regularizedPreRate_bounds hN hf _).1]
  exact (regularizedPreRate_bounds hN hf _).2

theorem gain_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ gain N f p ∧ gain N f p ≤ gainBound N := by
  constructor
  · exact integral_nonneg (fun _ => (regularizedPreRate_bounds hN hf _).1)
  · calc
      _ ≤ ∫ _q, 2*N^3 ∂fiberMeasure N := integral_mono (post_fiber_integrable hN hfm hf p)
        (integrable_const _) (fun _ => (regularizedPreRate_bounds hN hf _).2)
      _ = _ := by simp only [integral_const,smul_eq_mul,gainBound] <;> ring

theorem loss_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ loss N f p ∧ loss N f p ≤ lossBound N*f p := by
  constructor
  · exact integral_nonneg (fun _ => (regularizedPreRate_bounds hN hf _).1)
  · calc
      _ ≤ ∫ _q, 2*N^2*f p ∂fiberMeasure N := integral_mono (pre_fiber_integrable hN hfm hf p)
        (integrable_const _) (fun q => regularizedPreRate_linear hN hf (collisionGrouping.symm (p,q)))
      _ = _ := by simp only [integral_const,smul_eq_mul,lossBound] <;> ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicFiniteMild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform stability of the actual regularized collision integrands -/
noncomputable section
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem pairRate_uniform_difference {N D a b c d a' b' c' d' : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (hea : |a-a'| ≤ D) (heb : |b-b'| ≤ D) (hec : |c-c'| ≤ D) (hed : |d-d'| ≤ D) :
    |pairRate N a b c d-pairRate N a' b' c' d'| ≤ 12*N*D := by
  have hp := pairRate_difference_le hN ha hb hc hd ha' hb' hc' hd'
  calc
    _ ≤ 3*N*(|a-a'|+|b-b'|+|c-c'|+|d-d'|) := hp
    _ ≤ 3*N*(D+D+D+D) := by gcongr
    _ = _ := by ring

variable {X : Type*}

theorem regularizedPreRate_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (hfg : ∀ p, |f p-g p| ≤ D) (z : (X × (Velocity × Velocity)) × Sphere) :
    |regularizedPreRate N f z-regularizedPreRate N g z| ≤ 24*N^2*D := by
  have hw := windowKernel_bounds hN.le z
  have hp := pairRate_uniform_difference hN
    (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
    (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (hg (z.1.1,z.1.2.1)) (hg (z.1.1,z.1.2.2))
    (hg (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hg (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (hfg _) (hfg _) (hfg _) (hfg _)
  unfold regularizedPreRate
  rw [← mul_sub,abs_mul,abs_of_nonneg hw.1]
  exact (mul_le_mul hw.2 hp (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem regularizedPostRate_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (hfg : ∀ p, |f p-g p| ≤ D) (z : (X × (Velocity × Velocity)) × Sphere) :
    |regularizedPostRate N f z-regularizedPostRate N g z| ≤ 24*N^2*D :=
  regularizedPreRate_difference hN hf hg hfg (scatterTriple z)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global uniform stability of the positive cutoff collision operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def rateLipschitz (N : ℝ) : ℝ := 24*N^2*(fiberMeasure N).real Set.univ

theorem gain_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p) (hfg : ∀ p, |f p-g p| ≤ D)
    (p : X × Velocity) : |gain N f p-gain N g p| ≤ rateLipschitz N*D := by
  unfold gain
  rw [← integral_sub (post_fiber_integrable hN hfm hf p) (post_fiber_integrable hN hgm hg p)]
  have h := norm_integral_le_of_norm_le_const (μ := fiberMeasure N)
    (ae_of_all _ (fun q => show ‖regularizedPostRate N f (collisionGrouping.symm (p,q))-
      regularizedPostRate N g (collisionGrouping.symm (p,q))‖ ≤ 24*N^2*D by
        simpa only [Real.norm_eq_abs] using regularizedPostRate_difference hN hf hg hfg _))
  rw [Real.norm_eq_abs] at h
  exact h.trans_eq (by unfold rateLipschitz; ring)

theorem loss_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p) (hfg : ∀ p, |f p-g p| ≤ D)
    (p : X × Velocity) : |loss N f p-loss N g p| ≤ rateLipschitz N*D := by
  unfold loss
  rw [← integral_sub (pre_fiber_integrable hN hfm hf p) (pre_fiber_integrable hN hgm hg p)]
  have h := norm_integral_le_of_norm_le_const (μ := fiberMeasure N)
    (ae_of_all _ (fun q => show ‖regularizedPreRate N f (collisionGrouping.symm (p,q))-
      regularizedPreRate N g (collisionGrouping.symm (p,q))‖ ≤ 24*N^2*D by
        simpa only [Real.norm_eq_abs] using regularizedPreRate_difference hN hf hg hfg _))
  rw [Real.norm_eq_abs] at h
  exact h.trans_eq (by unfold rateLipschitz; ring)

def positiveSource (N : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain N f p + (lossBound N*f p-loss N f p)

theorem positiveSource_bounds {N R : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hR : ∀ p, f p ≤ R) (p : X × Velocity) :
    0 ≤ positiveSource N f p ∧ positiveSource N f p ≤ gainBound N+lossBound N*R := by
  have hgain := gain_bounds hN hfm hf p
  have hloss := loss_bounds hN hfm hf p
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  unfold positiveSource
  constructor
  · linarith
  · have hr := mul_le_mul_of_nonneg_left (hR p) hL
    linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The positive source used in the global cutoff iteration -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def sourceLipschitz (N : ℝ) : ℝ := 2*rateLipschitz N+lossBound N

theorem positiveSource_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (positiveSource N f) :=
  (gain_measurable N hf).add ((measurable_const.mul hf).sub (loss_measurable N hf))

theorem positiveSource_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p) (hfg : ∀ p, |f p-g p| ≤ D)
    (p : X × Velocity) : |positiveSource N f p-positiveSource N g p| ≤ sourceLipschitz N*D := by
  have hgain := gain_difference hN hfm hgm hf hg hfg p
  have hloss := loss_difference hN hfm hgm hf hg hfg p
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  have he : positiveSource N f p-positiveSource N g p =
      (gain N f p-gain N g p)+(lossBound N*(f p-g p)-(loss N f p-loss N g p)) := by
    unfold positiveSource
    ring
  rw [he]
  calc
    _ ≤ |gain N f p-gain N g p|+|lossBound N*(f p-g p)-(loss N f p-loss N g p)| := abs_add_le _ _
    _ ≤ |gain N f p-gain N g p|+(|lossBound N*(f p-g p)|+|loss N f p-loss N g p|) := by
      gcongr
      exact abs_sub (lossBound N*(f p-g p)) (loss N f p-loss N g p)
    _ = |gain N f p-gain N g p|+(lossBound N*|f p-g p|+|loss N f p-loss N g p|) := by
      rw [abs_mul,abs_of_nonneg hL]
    _ ≤ rateLipschitz N*D+(lossBound N*D+rateLipschitz N*D) := by
      gcongr
      exact hfg p
    _ = _ := by unfold sourceLipschitz; ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Exponential rescaling of the bounded positive collision source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def scaledDensity (T a : ℝ) (f : ℝ × Phase → ℝ) (t : ℝ) (p : Phase) : ℝ :=
  Real.exp (a*PositiveIntegral.time T t)*f (t,p)

def scaledProfile (T a : ℝ) (f : ℝ × Phase → ℝ) (p : (ℝ × Position) × Velocity) : ℝ :=
  scaledDensity T a f p.1.1 (p.1.2,p.2)

def scaledSource (T a N : ℝ) (f : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  Real.exp (-a*PositiveIntegral.time T z.1)*positiveSource N (scaledProfile T a f)
    ((z.1,z.2.1),z.2.2)

theorem scaledSource_eq (T a N : ℝ) (f : ℝ × Phase → ℝ) (z : ℝ × Phase) :
    scaledSource T a N f z = Real.exp (-a*PositiveIntegral.time T z.1)*
      positiveSource N (scaledDensity T a f z.1) z.2 := rfl

theorem scaledDensity_measurable (T a : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f)
    (t : ℝ) : Measurable (scaledDensity T a f t) :=
  measurable_const.mul (hf.comp (measurable_const.prodMk measurable_id))

theorem scaledProfile_measurable (T a : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f) :
    Measurable (scaledProfile T a f) := by
  unfold scaledProfile scaledDensity PositiveIntegral.time
  fun_prop

theorem scaledSource_measurable (T a N : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f) :
    Measurable (scaledSource T a N f) := by
  have hm := (positiveSource_measurable N (scaledProfile_measurable T a hf)).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  apply Measurable.mul _ hm
  unfold PositiveIntegral.time
  fun_prop

theorem exp_discount_cancel (a t : ℝ) : Real.exp (-a*t)*Real.exp (a*t) = 1 := by
  rw [← Real.exp_add]
  rw [show -a*t+a*t = 0 by ring,Real.exp_zero]

theorem scaledSource_bounds {T a N R : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (hN : 0 < N)
    {f : ℝ × Phase → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hR : ∀ z, f z ≤ R) (z : ℝ × Phase) :
    0 ≤ scaledSource T a N f z ∧ scaledSource T a N f z ≤ gainBound N+lossBound N*R := by
  let s := PositiveIntegral.time T z.1
  have hs : 0 ≤ s := (PositiveIntegral.time_bounds hT z.1).1
  have hn (p : Phase) : 0 ≤ scaledDensity T a f z.1 p :=
    mul_nonneg (Real.exp_pos _).le (hf _)
  have hb (p : Phase) : scaledDensity T a f z.1 p ≤ Real.exp (a*s)*R :=
    mul_le_mul_of_nonneg_left (hR _) (Real.exp_pos _).le
  have hsrc := positiveSource_bounds hN (scaledDensity_measurable T a hfm z.1) hn hb z.2
  have hd : Real.exp (-a*s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  rw [scaledSource_eq]
  refine ⟨mul_nonneg (Real.exp_pos _).le hsrc.1,?_⟩
  calc
    _ ≤ Real.exp (-a*s)*(gainBound N+lossBound N*(Real.exp (a*s)*R)) :=
      mul_le_mul_of_nonneg_left hsrc.2 (Real.exp_pos _).le
    _ = Real.exp (-a*s)*gainBound N+(lossBound N*R)*(Real.exp (-a*s)*Real.exp (a*s)) := by ring
    _ = Real.exp (-a*s)*gainBound N+lossBound N*R := by rw [exp_discount_cancel,mul_one]
    _ ≤ gainBound N+lossBound N*R := by
      exact add_le_add ((mul_le_mul_of_nonneg_right hd hC).trans_eq (one_mul _)) le_rfl

theorem scaledSource_difference {T a N D : ℝ} (hN : 0 < N)
    {f g : ℝ × Phase → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z) (hfg : ∀ z, |f z-g z| ≤ D)
    (z : ℝ × Phase) : |scaledSource T a N f z-scaledSource T a N g z| ≤ sourceLipschitz N*D := by
  let s := PositiveIntegral.time T z.1
  have hfn (p : Phase) : 0 ≤ scaledDensity T a f z.1 p := mul_nonneg (Real.exp_pos _).le (hf _)
  have hgn (p : Phase) : 0 ≤ scaledDensity T a g z.1 p := mul_nonneg (Real.exp_pos _).le (hg _)
  have hdiff (p : Phase) : |scaledDensity T a f z.1 p-scaledDensity T a g z.1 p| ≤
      Real.exp (a*s)*D := by
    change |Real.exp (a*s)*f (z.1,p)-Real.exp (a*s)*g (z.1,p)| ≤ _
    rw [← mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hfg _) (Real.exp_pos _).le
  have h := positiveSource_difference hN (scaledDensity_measurable T a hfm z.1)
    (scaledDensity_measurable T a hgm z.1) hfn hgn hdiff z.2
  rw [scaledSource_eq,scaledSource_eq,← mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-a*s)*(sourceLipschitz N*(Real.exp (a*s)*D)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = (sourceLipschitz N*D)*(Real.exp (-a*s)*Real.exp (a*s)) := by ring
    _ = sourceLipschitz N*D := by rw [exp_discount_cancel,mul_one]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual positive cutoff solutions on every finite time interval -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def scalingRate (N : ℝ) : ℝ := sourceLipschitz N+gainBound N+1

def dampingRate (N : ℝ) : ℝ := scalingRate N+lossBound N

theorem sourceLipschitz_nonneg (N : ℝ) : 0 ≤ sourceLipschitz N := by
  unfold sourceLipschitz rateLipschitz lossBound
  positivity

theorem scalingRate_pos {N : ℝ} (hN : 0 < N) : 0 < scalingRate N := by
  have hK := sourceLipschitz_nonneg N
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  unfold scalingRate
  linarith

theorem dampingRate_gt_sourceLipschitz {N : ℝ} (hN : 0 < N) :
    sourceLipschitz N < dampingRate N := by
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  unfold dampingRate scalingRate
  linarith

theorem scaledSource_ball {N R T : ℝ} (hN : 0 < N) (hT : 0 ≤ T) (hR : 1 ≤ R)
    {f : ℝ × Phase → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ R)
    (z : ℝ × Phase) : 0 ≤ scaledSource T (scalingRate N) N f z ∧
      scaledSource T (scalingRate N) N f z ≤ dampingRate N*R := by
  have hb := scaledSource_bounds hT (scalingRate_pos hN).le hN hfm hf hfb z
  have hK := sourceLipschitz_nonneg N
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  have ha := scalingRate_pos hN
  have har := mul_le_mul_of_nonneg_left hR ha.le
  have hCa : gainBound N ≤ scalingRate N := by unfold scalingRate; linarith
  refine ⟨hb.1,hb.2.trans ?_⟩
  unfold dampingRate
  nlinarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Exact velocity support of the regularized collision operator -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem regularizedPreRate_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.1‖) :
    regularizedPreRate N f z = 0 := by
  have hw : z ∉ collisionWindow N := fun h => (not_lt_of_ge (collisionWindow_bounds hN h).1) hz
  simp only [regularizedPreRate,windowKernel,indicator_of_notMem hw,zero_mul]

omit [MeasurableSpace X] in
theorem regularizedPostRate_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.1‖) :
    regularizedPostRate N f z = 0 := by
  have hw : z ∉ collisionWindow N := fun h => (not_lt_of_ge (collisionWindow_bounds hN h).1) hz
  rw [regularizedPostRate_formula]
  simp only [windowKernel,indicator_of_notMem hw,zero_mul]

theorem gain_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : gain N f p = 0 := by
  unfold gain
  have he (q : Velocity × Sphere) : regularizedPostRate N f (collisionGrouping.symm (p,q)) = 0 :=
    regularizedPostRate_zero_of_velocity hN f _ hp
  simp only [he,integral_zero]

theorem loss_zero_of_velocity {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : loss N f p = 0 := by
  unfold loss
  have he (q : Velocity × Sphere) : regularizedPreRate N f (collisionGrouping.symm (p,q)) = 0 :=
    regularizedPreRate_zero_of_velocity hN f _ hp
  simp only [he,integral_zero]

theorem positiveSource_outside {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : positiveSource N f p = lossBound N*f p := by
  simp only [positiveSource,gain_zero_of_velocity hN f p hp,loss_zero_of_velocity hN f p hp,
    sub_zero,zero_add]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The common pre/post multiplier in the conservative approximation -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def attenuation (N S : ℝ) : ℝ := N^2/(N+S)^2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Localization of the positive iteration to its preserved velocity ball -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def velocityRegion (N : ℝ) : Set (ℝ × Phase) := {z | ‖z.2.2‖ ≤ N}

def localize (N : ℝ) (f : ℝ × Phase → ℝ) : ℝ × Phase → ℝ := (velocityRegion N).indicator f

theorem velocityRegion_measurable (N : ℝ) : MeasurableSet (velocityRegion N) :=
  measurableSet_le (by fun_prop) measurable_const

theorem localize_measurable (N : ℝ) {f : ℝ × Phase → ℝ} (hf : Measurable f) :
    Measurable (localize N f) := hf.indicator (velocityRegion_measurable N)

theorem localize_bounds {N C : ℝ} (hC : 0 ≤ C) {f : ℝ × Phase → ℝ}
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ C) (z : ℝ × Phase) :
    0 ≤ localize N f z ∧ localize N f z ≤ C := by
  by_cases hz : z ∈ velocityRegion N
  · simpa only [localize,indicator_of_mem hz] using hf z
  · simpa only [localize,indicator_of_notMem hz] using And.intro le_rfl hC

theorem localize_difference {N D : ℝ} (hD : 0 ≤ D) {f g : ℝ × Phase → ℝ}
    (hfg : ∀ z, |f z-g z| ≤ D) (z : ℝ × Phase) : |localize N f z-localize N g z| ≤ D := by
  by_cases hz : z ∈ velocityRegion N
  · simpa only [localize,indicator_of_mem hz] using hfg z
  · simpa only [localize,indicator_of_notMem hz,sub_self,abs_zero] using hD

theorem localized_fixed_point_zero {N T L : ℝ} (f₀ : Density)
    (h₀ : ∀ p, N < ‖p.2‖ → f₀ p = 0) {f g : ℝ × Phase → ℝ}
    (hf : ∀ z, f z = PositiveIntegral.value T L TorusFlight.flight f₀ (localize N g) z)
    (z : ℝ × Phase) (hz : N < ‖z.2.2‖) : f z = 0 := by
  rw [hf]
  unfold PositiveIntegral.value
  have hinit : f₀ (TorusFlight.flight (-PositiveIntegral.time T z.1) z.2) = 0 := h₀ _ hz
  rw [hinit,mul_zero,zero_add]
  have he (r : ℝ) : localize N g (r,TorusFlight.flight (r-PositiveIntegral.time T z.1) z.2) = 0 := by
    apply indicator_of_notMem
    exact not_le_of_gt hz
  simp only [he,mul_zero,intervalIntegral.integral_zero]

theorem localized_scaledSource_eq {N T a : ℝ} (hN : 0 ≤ N) {f : ℝ × Phase → ℝ}
    (hf : ∀ z, N < ‖z.2.2‖ → f z = 0) :
    localize N (scaledSource T a N f) = scaledSource T a N f := by
  funext z
  by_cases hz : z ∈ velocityRegion N
  · exact indicator_of_mem hz _
  · have ho : N < ‖z.2.2‖ := lt_of_not_ge hz
    rw [localize,indicator_of_notMem hz,scaledSource_eq,positiveSource_outside hN _ z.2 ho]
    simp only [scaledDensity,hf z ho,mul_zero]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicInitialEntropyLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive iteration preserves the actual velocity support -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_supported_weighted_solution {N T A : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f₀ : Density} (hfm : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (h₀ : ∀ p, N < ‖p.2‖ → f₀ p = 0) :
    ∃ f : BoundedMeasurable.PositiveBall (ℝ × Phase) (max A 1),
      (∀ z, f.val z = PositiveIntegral.value T (dampingRate N) TorusFlight.flight f₀
        (scaledSource T (scalingRate N) N (fun z => f.val z)) z) ∧
      (∀ z, N < ‖z.2.2‖ → f.val z = 0) := by
  have hR : 1 ≤ max A 1 := le_max_right _ _
  have hL : 0 < dampingRate N :=
    (sourceLipschitz_nonneg N).trans_lt (dampingRate_gt_sourceLipschitz hN)
  have hex : ∃ f : BoundedMeasurable.PositiveBall (ℝ × Phase) (max A 1),
      ∀ z, f.val z = PositiveIntegral.value T (dampingRate N) TorusFlight.flight f₀
        (localize N (scaledSource T (scalingRate N) N (fun z => f.val z))) z := by
    apply PositiveIntegral.exists_damped_fixed_point hT hL (by linarith)
      (sourceLipschitz_nonneg N) (dampingRate_gt_sourceLipschitz hN) TorusFlight.measurable_flight hfm
      (fun p => ⟨(hf₀ p).1,(hf₀ p).2.trans (le_max_left _ _)⟩)
      (fun f => localize N (scaledSource T (scalingRate N) N (fun z => f.val z)))
    · intro f
      exact localize_measurable N (scaledSource_measurable _ _ _ (BoundedMeasurable.measurable _ f.val))
    · intro f z
      apply localize_bounds (mul_nonneg hL.le (by linarith)) _ z
      intro z
      exact scaledSource_ball hN hT hR (BoundedMeasurable.measurable _ f.val)
        (fun z => (f.property z).1) (fun z => (f.property z).2) z
    · intro f g z
      apply localize_difference (mul_nonneg (sourceLipschitz_nonneg N) dist_nonneg) _ z
      intro z
      exact scaledSource_difference hN (BoundedMeasurable.measurable _ f.val)
        (BoundedMeasurable.measurable _ g.val) (fun z => (f.property z).1) (fun z => (g.property z).1)
        (fun z => BoundedMeasurable.dist_apply_le (ℝ × Phase) f.val g.val z) z
  obtain ⟨f,hf⟩ := hex
  have hsupport : ∀ z, N < ‖z.2.2‖ → f.val z = 0 := localized_fixed_point_zero f₀ h₀ hf
  refine ⟨f,?_,hsupport⟩
  rw [localized_scaledSource_eq hN.le hsupport] at hf
  exact hf

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Supported positive mild approximants and their finite entropy class -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

structure BoundedCutoffSolution (N T : ℝ) (f₀ : Density) where
  density : ℝ × Phase → ℝ
  measurable : Measurable density
  nonnegative : ∀ z, 0 ≤ density z
  bounded : ∃ B : ℝ, ∀ z, density z ≤ B
  support : ∀ z, N < ‖z.2.2‖ → density z = 0
  mild : ∀ z, density z = PositiveIntegral.value T (lossBound N) TorusFlight.flight f₀
    (fun w => positiveSource N (fun p => density (w.1,p)) w.2) z

theorem exists_supported_cutoff_solution {N T A : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f₀ : Density} (hfm : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (h₀ : ∀ p, N < ‖p.2‖ → f₀ p = 0) : Nonempty (BoundedCutoffSolution N T f₀) := by
  obtain ⟨f,hf,hsupport⟩ := exists_supported_weighted_solution hN hT hfm hf₀ h₀
  let F : ℝ × Phase → ℝ := fun z => Real.exp (scalingRate N*PositiveIntegral.time T z.1)*f.val z
  have hFm : Measurable F := by
    apply Measurable.mul _ (BoundedMeasurable.measurable (ℝ × Phase) f.val)
    unfold PositiveIntegral.time
    fun_prop
  refine ⟨⟨F,hFm,?_,⟨Real.exp (scalingRate N*T)*max A 1,?_⟩,?_,?_⟩⟩
  · intro z
    exact mul_nonneg (Real.exp_pos _).le (f.property z).1
  · intro z
    have he : Real.exp (scalingRate N*PositiveIntegral.time T z.1) ≤ Real.exp (scalingRate N*T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (PositiveIntegral.time_bounds hT z.1).2
        (scalingRate_pos hN).le)
    exact mul_le_mul he (f.property z).2 (f.property z).1 (Real.exp_pos _).le
  · intro z hz
    change Real.exp _*f.val z = 0
    rw [hsupport z hz,mul_zero]
  · intro z
    have h := congrArg (fun r => Real.exp (scalingRate N*PositiveIntegral.time T z.1)*r) (hf z)
    change F z = _ at h
    have hs : scaledSource T (scalingRate N) N (fun z => f.val z) =
        (fun w => Real.exp (-scalingRate N*PositiveIntegral.time T w.1)*
          positiveSource N (fun p => F (w.1,p)) w.2) := by
      funext w
      exact scaledSource_eq _ _ _ _ _
    rw [hs] at h
    simpa only [dampingRate,PositiveIntegral.value_rescale hT] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual bounded initial approximations for the global construction -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def initialApproximation (N : ℝ) (f : Density) (p : Phase) : ℝ :=
  if ‖p.2‖ ≤ N then min N (max 0 (f p)) else 0

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The exact characteristic equation of the supported periodic approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.source (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) : ℝ :=
  positiveSource N (fun p => S.density (z.1,p)) z.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildCharacteristics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact dilation of the damped characteristic integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

def scalePhase (r : ℝ) (p : JetPrototype.Phase) : JetPrototype.Phase := (r • p.1,p.2)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalCharacteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical collision source in the localized characteristic equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.PhysicalLocalization

def density (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) : ℝ := H q z.2.2*F z

def source (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) : ℝ :=
  CollisionCompactness.collisionSource b (GaussianLocal.state (density q F)) ((z.1,z.2.1),z.2.2)

end BoltzmannNonuniqueness.PhysicalLocalization

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EuclideanKineticMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Euclidean coordinates for the physical characteristic equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

/-- Euclidean free transport, with the same velocity convention as GLPS. -/
def flight (t : ℝ) (p : Velocity × Velocity) : Velocity × Velocity :=
  (p.1+t • p.2,p.2)

def spaceEquiv : Velocity ≃ᵐ JetPrototype.Space :=
  split.trans MeasurableEquiv.prodComm

def phaseEquiv : (Velocity × Velocity) ≃ᵐ JetPrototype.Phase :=
  MeasurableEquiv.prodCongr spaceEquiv (MeasurableEquiv.refl Velocity)

theorem spaceEquiv_apply (x : Velocity) : spaceEquiv x = JetPeriodicDatum.spatialMap x := by
  change (split x).swap = _
  rw [split_apply]
  rfl

theorem phaseEquiv_apply (p : Velocity × Velocity) : phaseEquiv p = JetPeriodicDatum.phaseMap p := by
  change (spaceEquiv p.1,p.2) = _
  rw [spaceEquiv_apply]
  rfl

theorem phaseEquiv_measurePreserving :
    MeasurePreserving phaseEquiv (volume : Measure (Velocity × Velocity)) FlightMeasure.phaseVolume := by
  convert JetPeriodicDatum.phaseMap_measurePreserving using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact phaseEquiv_apply p

theorem phaseEquiv_flight (t : ℝ) (p : Velocity × Velocity) :
    phaseEquiv (flight t p) = JetBarrier.flight t (phaseEquiv p) := by
  simp only [phaseEquiv_apply,JetPeriodicDatum.phaseMap,JetPeriodicDatum.spatialMap,
    flight,JetBarrier.flight]
  congr 2

/-- The physical density lifted to the Euclidean kinetic domain of GLPS. -/
def density (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : Published.KineticPhase) : ℝ :=
  PhysicalLocalization.density q F (z.1.1,phaseEquiv (z.1.2,z.2))

def source (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : Published.KineticPhase) : ℝ :=
  PhysicalLocalization.source b q F (z.1.1,phaseEquiv (z.1.2,z.2))

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Inverse free flight and Lebesgue preservation in Euclidean coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (flight t) (volume : Measure (Velocity × Velocity)) volume := by
  have h := (MeasurePreserving.symm phaseEquiv phaseEquiv_measurePreserving).comp
    ((FlightMeasure.flight_measurePreserving t).comp phaseEquiv_measurePreserving)
  have he : (fun p => phaseEquiv.symm (JetBarrier.flight t (phaseEquiv p))) = flight t := by
    funext p
    apply phaseEquiv.injective
    simp only [phaseEquiv.apply_symm_apply,phaseEquiv_flight]
  exact he ▸ h

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Localized physical mild equation in the Euclidean GLPS coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

@[simp] theorem phaseEquiv_snd (p : Velocity × Velocity) : (phaseEquiv p).2 = p.2 := rfl

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The measure-preserving map from Euclidean to jet kinetic coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.EuclideanFlight

def kineticMap (z : Published.KineticPhase) : ℝ × JetPrototype.Phase :=
  (z.1.1,phaseEquiv (z.1.2,z.2))

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrating characteristic test identities in physical spacetime -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

def characteristicEquiv : (ℝ × (Velocity × Velocity)) ≃ᵐ Published.KineticPhase where
  toFun z := TransportCutoff.characteristic z.2 z.1
  invFun z := (z.1.1,(z.1.2-z.1.1 • z.2,z.2))
  left_inv z := by
    dsimp only [TransportCutoff.characteristic]
    simp
  right_inv z := by
    dsimp only [TransportCutoff.characteristic]
    simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × (Velocity × Velocity) => TransportCutoff.characteristic z.2 z.1)
    unfold TransportCutoff.characteristic
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : Published.KineticPhase => (z.1.1,(z.1.2-z.1.1 • z.2,z.2)))
    fun_prop

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricColdSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The source created between distinct cold colors -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def coldFamilySource (q b : ℝ) (c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) : ℝ :=
  remainderForcing q b 0 (fun z => ∑' i, c i z) c u

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The complete core loss estimate from the hot cap and proved escaped tails -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def escapedFrequencyConstant (s₀ η α K d₀ q : ℝ) (m : ℕ) : ℝ :=
  JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m:ℝ))*
    weightFrequencyConstant q 2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cold colors lie between their surviving free flight and the Gaussian excess -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def freeColor (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : Label) (t : ℝ)
    (p : JetPrototype.Phase) : ℝ :=
  color s₀ η K α γ d₀ q N i (JetBarrier.flight (-t) p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Constructed zero-hot approximations on a uniform positive time interval -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def continuationAmplitude (s₀ η K α d₀ : ℝ) (N : ℕ) : ℝ :=
  WeightedFiniteSeed.amplitude s₀ η K d₀ N+coldNormBound s₀ η K α d₀ N+1

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CappedDensitySequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common velocity moment for the actual capped torus densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

def momentBase (s₀ η K α d₀ q : ℝ) : ℝ :=
  (2+escapedConstant s₀ η K α d₀)*hotConstant q

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Spacetime velocity moments of the actual capped periodic solutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

def torusPhysical (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : (ℝ × Position) × Velocity) : ℝ :=
  H q z.2*F (z.1.1,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1.2),z.2))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The constructed approximation sequence with uniformly integrable collision pairs -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

structure CapApproximation (s₀ η K α γ d₀ q T : ℝ) (N : ℕ) where
  amplitude : ℝ
  coefficient : ℝ
  amplitude_pos : 0 < amplitude
  coefficient_mem : coefficient ∈ Icc 0 2
  initial_bound : ∀ p, initial s₀ η K α γ d₀ q N
    (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*amplitude
  solution : PeriodicMildState q (N+1) (damping q (N+1) amplitude) T (2*amplitude)
    (initial s₀ η K α γ d₀ q N
      (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p))
  cap : solution.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) = 1

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapDilationCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual cap shots on horizons tending to zero -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

def shrinkingHorizon (τ : ℝ) (n : ℕ) : ℝ := τ/((n:ℝ)+1)

structure ShrinkingCapFamily (s₀ η K α γ d₀ q : ℝ) where
  horizonScale : ℝ
  horizonScale_pos : 0 < horizonScale
  horizonScale_le : horizonScale ≤ 1/32
  indices : ℕ → ℕ
  indices_ge : ∀ n, n ≤ indices n
  indices_tendsto : Tendsto indices atTop atTop
  cold_ratio_tendsto : Tendsto (fun n => DatumBounds.scale s₀ η (indices n+1)/
    shrinkingHorizon horizonScale n) atTop (𝓝 0)
  approximation : ∀ n, CapApproximation s₀ η K α γ d₀ q (shrinkingHorizon horizonScale n) (indices n)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Attained times and dilation radii for the actual shrinking cap shots -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hotSize {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (t : ℝ) : ℝ :=
  PhaseEssSup.size (fun p => F.solution.value (t,p)-
    ∑' i, rebuiltColdFamily q (N+1) (damping q (N+1) F.amplitude) T
      F.solution.value (color s₀ η K α γ d₀ q N) i (t,p))

structure AttainedCapSequence {s₀ η K α γ d₀ q : ℝ}
    (F : ShrinkingCapFamily s₀ η K α γ d₀ q) where
  time : ℕ → ℝ
  time_mem : ∀ n, time n ∈ Icc 0 (shrinkingHorizon F.horizonScale n)
  attained : ∀ n, (F.approximation n).hotSize (time n) =
    time n+DatumBounds.scale s₀ η (F.indices n+1)

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def radius (S : AttainedCapSequence F) (n : ℕ) : ℝ :=
  S.time n+DatumBounds.scale s₀ η (F.indices n+1)

def coldFraction (S : AttainedCapSequence F) (n : ℕ) : ℝ :=
  DatumBounds.scale s₀ η (F.indices n+1)/S.radius n

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A common subsequence for the cold scale, mesh phase and time domain -/

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def normalizedHorizon (S : AttainedCapSequence F) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (shrinkingHorizon F.horizonScale n/S.radius n)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positivity, measurability and cap bounds of the actual hot remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hot {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  F.solution.value u-∑' i, rebuiltColdFamily q (N+1) (damping q (N+1) F.amplitude) T
    F.solution.value (color s₀ η K α γ d₀ q N) i u

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Damping-free source bound for the actual finite cap solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hotNetSource {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  remainderForcing q (N+1) (damping q (N+1) F.amplitude) F.solution.value
    (rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N F.solution.value) u-
      damping q (N+1) F.amplitude*F.hot u

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Physical hot densities under the attained cap dilation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledHot (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  H q u.2.2 * (F.approximation n).hot
    (S.radius n*u.1,(S.radius n • u.2.1,u.2.2)) / S.radius n

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Zero extension of rescaled hot densities beyond their physical horizons -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def hotTimeDomain (S : AttainedCapSequence F) (n : ℕ) : Set (ℝ × JetPrototype.Phase) :=
  {u | S.radius n*u.1 ∈ Icc 0 (shrinkingHorizon F.horizonScale n)}

def extendedHot (S : AttainedCapSequence F) (n : ℕ) : ℝ × JetPrototype.Phase → ℝ :=
  (S.hotTimeDomain n).indicator (S.rescaledHot n)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local uniform integrability of the actual dilated hot sequence -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

abbrev HotKineticPhase := (ℝ × JetPrototype.Space) × Velocity

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def hotDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotKineticPhase) : ℝ :=
  S.extendedHot n (z.1.1,(z.1.2,z.2))

def hotWindowVolume (A R : ℝ) : Measure HotKineticPhase :=
  ((volume.restrict (Icc (0:ℝ) A)).prod
    (volume.restrict (Metric.closedBall (0 : JetPrototype.Space) R))).prod volume

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform integrability and tightness of the actual dilated hot pairs -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

abbrev HotPairPhase := (ℝ × JetPrototype.Space) × (Velocity × Velocity)

def hotBaseWindowVolume (A R : ℝ) : Measure (ℝ × JetPrototype.Space) :=
  (volume.restrict (Icc (0:ℝ) A)).prod
    (volume.restrict (Metric.closedBall (0 : JetPrototype.Space) R))

def hotPairWindowVolume (A R : ℝ) : Measure HotPairPhase :=
  (hotBaseWindowVolume A R).prod volume

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapLabelFreeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # One subsequence for the hot density, mesh phase and limiting horizon -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

structure HotLimitExtraction (S : AttainedCapSequence F) where
  fraction : ℝ
  fraction_mem : fraction ∈ Icc 0 1
  phase : ℝ
  phase_mem : phase ∈ Icc 1 (Real.exp η)
  horizon : ℝ≥0∞
  horizon_ge : 1 ≤ horizon
  indices : ℕ → ℕ
  indices_strict : StrictMono indices
  fraction_limit : Tendsto (fun n => S.coldFraction (indices n)) atTop (𝓝 fraction)
  phase_limit : Tendsto (fun n => GeometricMesh.phase (s₀/S.radius (indices n)) η)
    atTop (𝓝 phase)
  horizon_limit : Tendsto (fun n => S.normalizedHorizon (indices n)) atTop (𝓝 horizon)
  profile : ℕ → HotKineticPhase → ℝ
  weak : ∀ j : ℕ, Published.WeakL1Converges (hotWindowVolume (j+1) (j+1))
    (fun n => S.hotDensity (indices n)) (profile j)
  nonneg : ∀ j : ℕ, ∀ᵐ z ∂hotWindowVolume (j+1) (j+1), 0 ≤ profile j z
  cap : ∀ j : ℕ, ∀ᵐ z ∂hotWindowVolume (j+1) (j+1),
    profile j z ≤ (z.1.1+fraction)*H q z.2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual cold labels approaching each point of the limiting geometric mesh -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabel (E : HotLimitExtraction S) (k : ℤ) (a : Bool) (n : ℕ) :
    JetLattice.Label :=
  ⟨GeometricMesh.jetIndex s₀ η (fun j => S.radius (E.indices j)) k n,a,0⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The quantitative free-flight error of the constructed cap approximations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.cold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (i : Label) : ℝ × JetPrototype.Phase → ℝ :=
  rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N F.solution.value i

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual hot remainder satisfies a bounded linear mild equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hotInitial {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (p : JetPrototype.Phase) : ℝ :=
  initial s₀ η K α γ d₀ q N
    (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p-
      ∑' i, color s₀ η K α γ d₀ q N i p

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The mixed-cold source bound for the actual cap approximations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.coldSource {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : ℝ × JetPrototype.Phase → ℝ :=
  coldFamilySource q (N+1) F.cold

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual free-core average reduces to its limiting shell and fine stripes -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelFreeAverage (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  let r := S.radius (E.indices n)
  let s := JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  ∫ v, r*JetFreeTransport.free η K α γ s (d₀*s^10) (r*t) a (r • x,v)*ψ v

def HotLimitExtraction.coldLabelStripeAverage (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (y : Transverse) : ℝ :=
  let r := S.radius (E.indices n)
  let s := JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  ∫ w, (JetGeometry.stripe s a).indicator (fun _ => (1:ℝ))
    (r • (y-t • ((d₀*s^10) • w.1)))*JetThermalKernel.J (SheetMeasures.join w)
    ∂(volume : Measure Transverse).prod volume

def HotLimitExtraction.coldLabelStripedProfile (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  let μ := E.phase*Real.exp (η*(k:ℝ))
  JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
    ((JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      E.coldLabelStripeAverage k a n t x.1)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotWindowGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and compatibility of the nested hot-density windows -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def hotWindowSet (A R : ℝ) : Set HotKineticPhase :=
  (Icc (0:ℝ) A ×ˢ Metric.closedBall (0 : JetPrototype.Space) R) ×ˢ univ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LinearHotLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized GLPS resolvents for a bounded weighted linear mild equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

def linearSource (q L : ℝ) (F g : ℝ × JetPrototype.Phase → ℝ)
    (z : Published.KineticPhase) : ℝ :=
  H q z.2*(g (z.1.1,phaseEquiv (z.1.2,z.2))-L*F (z.1.1,phaseEquiv (z.1.2,z.2)))

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapHotUndamped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A single measurable hot limit from the compatible local weak limits -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.hotLimit (E : HotLimitExtraction S) (z : HotKineticPhase) : ℝ :=
  max 0 (liminf (fun j => E.profile j z) atTop)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The local weak limit is a limit of the physical, unextended cap shots -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def physicalHotDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotKineticPhase) : ℝ :=
  S.rescaledHot n (z.1.1,(z.1.2,z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform upper source bounds after the actual cap dilation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledHotSource (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  (F.approximation n).hotNetSource (S.radius n*u.1,(S.radius n • u.2.1,u.2.2))

def sourceError (S : AttainedCapSequence F) (C B A : ℝ) (m n : ℕ) : ℝ :=
  C*(S.radius n)^2*(A+1)^2+B*(S.radius n)^m*A^m

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The exact linear mild equation of the rescaled hot component -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def normalizedHot (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  (F.approximation n).hot (S.radius n*u.1,PositiveIntegral.scalePhase (S.radius n) u.2)/S.radius n

def rescaledHotForcing (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  remainderForcing q (F.indices n+1) (damping q (F.indices n+1) (F.approximation n).amplitude)
    (F.approximation n).solution.value (F.approximation n).cold
      (S.radius n*u.1,PositiveIntegral.scalePhase (S.radius n) u.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Further extraction preserves every scale and the same global hot limit -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.subsequence (E : HotLimitExtraction S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : HotLimitExtraction S where
  fraction := E.fraction
  fraction_mem := E.fraction_mem
  phase := E.phase
  phase_mem := E.phase_mem
  horizon := E.horizon
  horizon_ge := E.horizon_ge
  indices := E.indices ∘ φ
  indices_strict := E.indices_strict.comp hφ
  fraction_limit := E.fraction_limit.comp hφ.tendsto_atTop
  phase_limit := E.phase_limit.comp hφ.tendsto_atTop
  horizon_limit := E.horizon_limit.comp hφ.tendsto_atTop
  profile := E.profile
  weak := fun j => (E.weak j).comp hφ.tendsto_atTop
  nonneg := E.nonneg
  cap := E.cap

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual rescaled cold density, before taking its atomic limit -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.coldTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  ∑' i, F.cold i u

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledColdDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotKineticPhase) : ℝ :=
  S.radius n*H q z.2*(F.approximation n).coldTotal
    (S.radius n*z.1.1,(S.radius n • z.1.2,z.2))

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual hot-limit representative and its geometric background bounds -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.cappedHot (E : HotLimitExtraction S) (z : HotKineticPhase) : ℝ :=
  min (E.hotLimit z) (max 0 (z.1.1+E.fraction)*H q z.2)

def HotLimitExtraction.background (E : HotLimitExtraction S) (t : ℝ)
    (x : JetPrototype.Space) : Measure Velocity :=
  GeometricBackground.background E.phase η E.fraction K α γ t x

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual limiting cold--hot product kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.hotKernel (E : HotLimitExtraction S) :
    Kernel (ℝ × JetPrototype.Space) Velocity :=
  (Kernel.const _ (volume : Measure Velocity)).withDensity
    (fun x v => ENNReal.ofReal (E.cappedHot (x,v)))

instance HotLimitExtraction.hotKernel_sFinite (E : HotLimitExtraction S) :
    IsSFiniteKernel E.hotKernel :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

def HotLimitExtraction.mixedKernel (E : HotLimitExtraction S) {a : ℝ} (ha : 0 < a)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    Kernel (ℝ × JetPrototype.Space) (Velocity × Velocity) :=
  GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction ×ₖ
    E.hotKernel

instance HotLimitExtraction.mixedKernel_sFinite (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    IsSFiniteKernel (E.mixedKernel ha hK hα hγ) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  unfold HotLimitExtraction.mixedKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite mixed cold--hot measures on bounded spacetime windows -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.mixedMeasure (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (μ : Measure (ℝ × JetPrototype.Space)) :
    Measure ((ℝ × JetPrototype.Space) × (Velocity × Velocity)) :=
  μ ⊗ₘ E.mixedKernel ha hK hα hγ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The mixed-cold source becomes small under the cap dilation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledColdSource (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  (F.approximation n).coldSource (S.radius n*u.1,(S.radius n • u.2.1,u.2.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual mixed-cold source vanishes in local spacetime L1 -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def coldSourceDensity (S : AttainedCapSequence F) (a A : ℝ) (n : ℕ)
    (z : HotKineticPhase) : ℝ :=
  {z : HotKineticPhase | z.1.1 ∈ Icc a A}.indicator
    (fun z => H q z.2*S.rescaledColdSource n (z.1.1,(z.1.2,z.2))) z

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual rescaled hot solutions have the GLPS resolvent representation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def euclideanHot (S : AttainedCapSequence F) (n : ℕ) : Published.KineticPhase → ℝ :=
  EuclideanFlight.density q (S.normalizedHot n)

def euclideanHotSource (S : AttainedCapSequence F) (n : ℕ) (z : Published.KineticPhase) : ℝ :=
  H q z.2*S.rescaledHotSource n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The same weak hot density in the Euclidean averaging coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotChart : Published.KineticPhase ≃ᵐ JetCopyDatum.AttainedCapSequence.HotKineticPhase :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) spaceEquiv)
    (MeasurableEquiv.refl Velocity)

def hotBaseVolume (A R : ℝ) : Measure Published.SpaceTime :=
  (volume.restrict (Icc (0:ℝ) A)).prod
    (volume.restrict (spaceEquiv ⁻¹' Metric.closedBall (0 : JetPrototype.Space) R))

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AxisInput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Suppression of transverse input away from the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.AxisInput

def away (v : Velocity) (δ : ℝ) : Set Coordinates :=
  {y | δ ≤ ‖transverse (chart v y.1 y.2.1 y.2.2)‖}

def awayBall (v : Velocity) (R δ : ℝ) : Set Coordinates := ballRegion v R ∩ away v δ

def powerConstant (q L R δ : ℝ) : ℝ :=
  tiltConstant * (4 * L) * (1 + δ ^ (-q)) * (8 * R ^ 2) *
    TransverseAverage.expectationConstant q

end BoltzmannNonuniqueness.AxisInput

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MismatchSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Slice bounds with a nonzero axial mismatch -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.MismatchSlices

def slopeCoefficient (q R : ℝ) : ℝ :=
  AxialSlices.lineConstant q * (2 * (2 * R) ^ (2 - q) / (2 - q))

def mismatchCoefficient (q R δ : ℝ) : ℝ :=
  4 * R ^ 2 + slopeCoefficient q R * δ ^ (1 - q)

end BoltzmannNonuniqueness.MismatchSlices

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AxisMismatch
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform suppression of nonzero axial mismatch near the output axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.MismatchSlices

namespace BoltzmannNonuniqueness.AxisMismatch

def incoming (v : Velocity) (δ : ℝ) : Set Velocity :=
  {p | δ ≤ |axial (v - p)|}

def region (v : Velocity) (R δ : ℝ) : Set Coordinates :=
  ballRegion v R ∩ (incoming v δ ×ˢ univ)

def powerValue (q L R δ r : ℝ) : ℝ :=
  (tiltConstant * (4 * L) * (2 * mismatchCoefficient q R δ)) *
    (r ^ q + expectationConstant q * r ^ (q - 1))

end BoltzmannNonuniqueness.AxisMismatch

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AffineSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricted affine slice changes of variables -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.GeometricSlice

namespace BoltzmannNonuniqueness.AffineSlices

def intervalConstant (q D : ℝ) : ℝ := 2 * (2 * D) ^ (2 - q) / (2 - q)

def rectangleConstant (q D S : ℝ) : ℝ :=
  4 * D * S + AxialSlices.lineConstant q * intervalConstant q D

end BoltzmannNonuniqueness.AffineSlices

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_StripeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact period and mean of the cold stripes -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGeometry

def stripeLine (p : ℝ) (a : Bool) : Set ℝ :=
  {x | ∃ k : ℤ, ((k:ℝ)+(if a then 0 else 1/2))*p < x ∧
    x < ((k:ℝ)+(if a then 0 else 1/2)+1/4)*p}

end BoltzmannNonuniqueness.JetGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ShiftedStripe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered stripe estimates uniform in spatial phase -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGeometry

def centeredStripe (p d : ℝ) (a : Bool) (x : ℝ) : ℝ :=
  (stripeLine p a).indicator (fun _ => (1:ℝ)) (x-d)-1/4

end BoltzmannNonuniqueness.JetGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseStripeWeak
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Stripe averaging on the transverse plane and additional fibers -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def transverseCartesian : Transverse ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ThermalStripeIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak averaging after the Gaussian thermal mixture -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def thermalStripeCentered (p d t : ℝ) (a : Bool) (y : Transverse) : ℝ :=
  ∫ w : Transverse × ℝ, centeredStripe p (t*d*w.1 0) a (y 0)*
    JetThermalKernel.J (SheetMeasures.join w) ∂(volume : Measure Transverse).prod volume

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapFiniteBackgroundLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded testing of the actual cold/free error -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelError (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  S.radius (E.indices n)*(H q p.2*(F.approximation (E.indices n)).cold (E.coldLabel k a n)
    (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2))-
    JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
      (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
      (S.radius (E.indices n)*t) a
      (shift (displacement (E.coldLabel k a n).lattice) (S.radius (E.indices n) • p.1,p.2)))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The velocity averages of the actual retained cold colors -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelDensity (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (p : JetPrototype.Phase) : ℝ :=
  S.radius (E.indices n)*(H q p.2*(F.approximation (E.indices n)).cold (E.coldLabel k a n)
    (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2)))

def HotLimitExtraction.coldLabelAverage (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∫ v, ψ v*E.coldLabelDensity k a n t (x,v)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The limiting average of an individual cold label -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelLimitProfile (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  let μ := E.phase*Real.exp (η*(k:ℝ))
  JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
    ((JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*(1/4))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Simultaneous striped approximation on a finite retained mesh -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.finiteColdAverage (E : HotLimitExtraction S) (L U : ℤ)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∑ a : Bool, ∑ k ∈ Finset.Icc L U, if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
    E.coldLabelAverage k a n t ψ x else 0

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The weak limit of the finite retained cold mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.finiteColdLimitProfile (E : HotLimitExtraction S) (L U : ℤ)
    (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∑ a : Bool, ∑ k ∈ Finset.Icc L U, if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
    E.coldLabelLimitProfile k a t ψ x else 0

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapHotSourceIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform lower hot-source bounds on positive rescaled time slabs -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def lossEnvelope (s₀ η K α γ d₀ q a A : ℝ) : ℝ :=
  ((A+1+escapedConstant s₀ η K α d₀)*hotConstant q)*(A+1)+
    JetEnvelopeGain.momentConstant K α γ*(1+1/a)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A uniform absolute bound for the actual rescaled transport source -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def sourceEnvelope (s₀ η K α γ d₀ q a A : ℝ) (v : Velocity) : ℝ :=
  2*JetMainGain.coefficient K α γ q+1+
    2*Real.pi*(‖v‖+1)*lossEnvelope s₀ η K α γ d₀ q a A

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform integrability of the actual hot sources on positive-time windows -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def hotSourceDensity (S : AttainedCapSequence F) (a A : ℝ) (n : ℕ)
    (z : HotKineticPhase) : ℝ :=
  {z : HotKineticPhase | z.1.1 ∈ Icc a A}.indicator
    (fun z => H q z.2*S.rescaledHotSource n (z.1.1,(z.1.2,z.2))) z

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapColdBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual escaped cold density in Euclidean coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.escapedTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ :=
  ∑' i, escaped s₀ η z.1.1 N z.1.2
    (fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) i

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact removal of the escaped colors from an actual cap approximation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.centralTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ := by
  classical
  exact ∑' i, if i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Only finitely many central colors remain in the centered cell -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def centralLabels (N : ℕ) : Finset JetLattice.Label :=
  ((Finset.range N).product (Finset.univ : Finset Bool)).image
    (fun p => ⟨p.1,p.2,0⟩)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Escaped cold mass vanishes on bounded positive-time dilation windows -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledEscapedDensity (S : AttainedCapSequence F) (n : ℕ)
    (z : Published.KineticPhase) : ℝ :=
  S.radius n*H q z.2*(F.approximation n).escapedTotal
    ((S.radius n*z.1.1,S.radius n • z.1.2),z.2)

def coldSlabSet (a A R : ℝ) : Set Published.KineticPhase :=
  (Icc a A ×ˢ Metric.closedBall (0 : Velocity) R) ×ˢ univ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Joint regularity and uniform bounds for the full cold velocity averages -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def coldAverage (S : AttainedCapSequence F) (n : ℕ) (ψ : Velocity → ℝ)
    (x : ℝ × JetPrototype.Space) : ℝ :=
  ∫ v, ψ v*S.rescaledColdDensity n (x,v)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A finite window of actual cold labels -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.meshLabels (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ) : Finset JetLattice.Label :=
  ((Finset.Icc L U).product (Finset.univ : Finset Bool)).image (fun p => E.coldLabel p.1 p.2 n)

def HotLimitExtraction.meshCold (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (u : ℝ × JetPrototype.Phase) : ℝ :=
  ∑ i ∈ E.meshLabels n L U, if i.annulus < F.indices (E.indices n) then
    (F.approximation (E.indices n)).cold i u else 0

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapColdAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual dilated cold density on a finite mesh window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.meshColdDensity (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (z : Published.KineticPhase) : ℝ :=
  S.radius (E.indices n)*H q z.2*E.meshCold n L U
    (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2,z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite mesh truncation of the actual cold density in local L1 -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def meshWindowSet (a A δ R : ℝ) : Set Published.KineticPhase :=
  coldSlabSet a A R ∩ {z | δ ≤ ‖transverse z.1.2‖}

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual finite-mesh velocity averages converge to the background -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.meshColdChartAverage (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  ∫ v, ψ v*E.meshColdDensity n L U ((t,SheetMeasures.join x),v)

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_SubcapColdControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive approximations below the cap

The cap upper bound suffices for compactness, without requiring the cap to be
attained. Zero-hot approximations therefore satisfy the same bounds. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

structure Approximation (s₀ η K α γ d₀ q T : ℝ) (N : ℕ) where
  amplitude : ℝ
  coefficient : ℝ
  amplitude_pos : 0 < amplitude
  coefficient_mem : coefficient ∈ Icc 0 2
  initial_bound : ∀ p, initial s₀ η K α γ d₀ q N
    (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*amplitude
  solution : PeriodicMildState q (N+1) (damping q (N+1) amplitude) T (2*amplitude)
    (initial s₀ η K α γ d₀ q N
      (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p))
  cap_bound : solution.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) ≤ 1


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Actual cold components of approximations below the cap -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.Published
namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

def Approximation.cold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (i : Label) : ℝ × JetPrototype.Phase → ℝ :=
  rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N F.solution.value i



def Approximation.coldTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  ∑' i, F.cold i u



def Approximation.escapedTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ :=
  ∑' i, escaped s₀ η z.1.1 N z.1.2
    (fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) i



def Approximation.centralTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ := by
  classical
  exact ∑' i, if i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdCentralVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact cold cylinders and their exhaustion away from the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def coldCylinderVolume (a A R : ℝ) : Measure (ℝ × JetPrototype.Space) :=
  (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict
    (Metric.closedBall (0 : VelocityWeight.Transverse) R ×ˢ Icc (-R) R))

instance coldCylinderVolume_finite (a A R : ℝ) : IsFiniteMeasure (coldCylinderVolume a A R) := by
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict
      (Metric.closedBall (0 : VelocityWeight.Transverse) R ×ˢ Icc (-R) R)) :=
    isFiniteMeasure_restrict.mpr ((isCompact_closedBall (0 : VelocityWeight.Transverse) R).prod
      isCompact_Icc).measure_lt_top.ne
  exact inferInstanceAs (IsFiniteMeasure ((volume.restrict (Icc a A)).prod _))

def coldAxisCutoff (m : ℕ) : Set (ℝ × JetPrototype.Space) :=
  {z | 1/((m:ℝ)+1) ≤ ‖z.2.1‖}

def coldTransverseAnnulus (R : ℝ) (m : ℕ) : Set VelocityWeight.Transverse :=
  Metric.closedBall 0 R ∩ {y | 1/((m:ℝ)+1) ≤ ‖y‖}

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The cold cylinders are measurable restrictions of the hot windows -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def coldCylinderSet (a A R : ℝ) : Set HotKineticPhase :=
  (Icc a A ×ˢ Metric.closedBall (0 : JetPrototype.Space) R) ×ˢ univ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotChartHomeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A bounded Borel hot ratio preserving the actual finite-time traces -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def boundedHotRatio (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase) : ℝ :=
  max 0 (min 2 (S.euclideanHot n z/H q z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Topological transport of compact kinetic tests through the hot chart -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem spaceEquiv_continuous : Continuous spaceEquiv := by
  change Continuous (fun x => spaceEquiv x)
  simp only [spaceEquiv_apply,JetPeriodicDatum.spatialMap]
  unfold transverse axial
  fun_prop

theorem spaceEquiv_symm_components (x : JetPrototype.Space) :
    transverse (spaceEquiv.symm x) = x.1 ∧ axial (spaceEquiv.symm x) = x.2 := by
  have h := spaceEquiv.apply_symm_apply x
  rw [spaceEquiv_apply] at h
  change (transverse (spaceEquiv.symm x), axial (spaceEquiv.symm x)) = x at h
  constructor
  · exact @congrArg JetPrototype.Space _
      (transverse (spaceEquiv.symm x), axial (spaceEquiv.symm x)) x (fun p => p.1) h
  · exact @congrArg JetPrototype.Space ℝ
      (transverse (spaceEquiv.symm x), axial (spaceEquiv.symm x)) x (fun p => p.2) h

theorem spaceEquiv_symm_lipschitz : LipschitzWith 2 spaceEquiv.symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  change ‖spaceEquiv.symm x-spaceEquiv.symm y‖ ≤ 2*‖x-y‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hn := norm_sq_split (spaceEquiv.symm x-spaceEquiv.symm y)
  rw [PlaneChart.transverse_sub,PlaneChart.axial_sub,
    (spaceEquiv_symm_components x).1,(spaceEquiv_symm_components y).1,
    (spaceEquiv_symm_components x).2,(spaceEquiv_symm_components y).2] at hn
  have hx : ‖x.1-y.1‖ ≤ ‖x-y‖ := norm_fst_le (x-y)
  have hy : ‖x.2-y.2‖ ≤ ‖x-y‖ := norm_snd_le (x-y)
  have hx2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
  have hy2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy
  rw [Real.norm_eq_abs,sq_abs] at hy2
  nlinarith [sq_nonneg ‖x-y‖]

def hotHomeomorph : Published.KineticPhase ≃ₜ JetCopyDatum.AttainedCapSequence.HotKineticPhase where
  toEquiv := hotChart.toEquiv
  continuous_toFun := by
    change Continuous (fun z : Published.KineticPhase => ((z.1.1,spaceEquiv z.1.2),z.2))
    exact (continuous_fst.fst.prodMk (spaceEquiv_continuous.comp continuous_fst.snd)).prodMk
      continuous_snd
  continuous_invFun := by
    change Continuous (fun z : JetCopyDatum.AttainedCapSequence.HotKineticPhase =>
      ((z.1.1,spaceEquiv.symm z.1.2),z.2))
    exact (continuous_fst.fst.prodMk
      (spaceEquiv_symm_lipschitz.continuous.comp continuous_fst.snd)).prodMk continuous_snd

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicProductTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Smooth compact tests in free-characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

abbrev CharacteristicPhase := ℝ × (Velocity × Velocity)

theorem characteristicEquiv_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (characteristicEquiv : CharacteristicPhase → Published.KineticPhase) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : CharacteristicPhase => ((z.1,z.2.1+z.1 • z.2.2),z.2.2))
  fun_prop

theorem characteristicEquiv_symm_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (characteristicEquiv.symm : Published.KineticPhase → CharacteristicPhase) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : Published.KineticPhase =>
    (z.1.1,(z.1.2-z.1.1 • z.2,z.2)))
  fun_prop

def characteristicHomeomorph : CharacteristicPhase ≃ₜ Published.KineticPhase where
  toEquiv := characteristicEquiv.toEquiv
  continuous_toFun := characteristicEquiv_contDiff.continuous
  continuous_invFun := characteristicEquiv_symm_contDiff.continuous

def testPullback (ψ : CharacteristicPhase → ℝ) : Published.KineticPhase → ℝ :=
  ψ ∘ characteristicEquiv.symm

def timeDerivative (ψ : CharacteristicPhase → ℝ) (z : CharacteristicPhase) : ℝ :=
  fderiv ℝ ψ z (1,0)

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Time and phase test products in characteristic coordinates -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.EuclideanFlight

def timePhaseTest (θ : ℝ → ℝ) (φ : Velocity × Velocity → ℝ) : CharacteristicPhase → ℝ :=
  fun z => θ z.1*φ z.2

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedAverageProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A bounded representative of a density divided by its positive mass -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def boundedQuotient (C : ℝ≥0) (A R : X → ℝ) (x : X) : ℝ :=
  max (-(C:ℝ)) (min (C:ℝ) (A x/R x))

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TimeSourceCumulative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite time measures obtained by testing characteristic phase -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeakTime

abbrev Phase := Velocity × Velocity

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Measure-preserving time translations of kinetic half-lines and intervals -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def timeTranslation (τ : ℝ) : (ℝ × Phase) ≃ᵐ (ℝ × Phase) :=
  (MeasurableEquiv.addRight τ).prodCongr (MeasurableEquiv.refl Phase)

@[simp] theorem timeTranslation_apply (τ : ℝ) (z : ℝ × Phase) :
    timeTranslation τ z = (z.1+τ,z.2) := rfl

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildCurveContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A strongly continuous Eulerian representative of an integrable mild curve -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.TorusFlight

def characteristicProfile (μ : Measure ℝ) (a : Density) (R : ℝ × Phase → ℝ)
    (t : ℝ) (p : Phase) : ℝ := a p+Published.timePrimitive μ R (t,p)

def eulerianProfile (μ : Measure ℝ) (a : Density) (R : ℝ × Phase → ℝ)
    (t : ℝ) (p : Phase) : ℝ := characteristicProfile μ a R t (flight (-t) p)

end BoltzmannNonuniqueness.TorusFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMomentEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable undamped sources of the actual periodic cutoff solutions -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.collision (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) : ℝ :=
  S.source z-lossBound N*S.density z

def BoundedCutoffSolution.characteristicSource (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) : ℝ :=
  S.collision (z.1,TorusFlight.flight z.1 z.2)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Retained dissipation of the actual finite periodic solutions -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.kineticProfile (S : BoundedCutoffSolution N T f₀) :
    (ℝ × Position) × Velocity → ℝ := fun p => S.density (p.1.1,(p.1.2,p.2))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable renormalized fields of the actual periodic solution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.renormalizedDensity (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : ℝ × Phase) : ℝ :=
  maxwellian z.2.2*β.toFun (S.density z/maxwellian z.2.2)

def BoundedCutoffSolution.renormalizedSource (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : ℝ × Phase) : ℝ :=
  derivWithin β.toFun (Ici 0) (S.density z/maxwellian z.2.2)*S.collision z

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveVolterra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive backward gain iteration on free kinetic characteristics -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

def flight (z : Published.KineticPhase) (s : ℝ) : Published.KineticPhase :=
  ((s,z.1.2-(z.1.1-s) • z.2),z.2)

def step (a : ℝ) (K : Kernel Published.KineticPhase Velocity)
    (f : Published.KineticPhase → ℝ≥0∞) (z : Published.KineticPhase) : ℝ≥0∞ :=
  ∫⁻ s in Ioc a z.1.1, ∫⁻ v, f ((flight z s).1,v) ∂K (flight z s)

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EuclideanBackwardMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The spatial windows transported to Euclidean coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotBaseSet (A R : ℝ) : Set Published.SpaceTime :=
  Icc 0 A ×ˢ (spaceEquiv ⁻¹' Metric.closedBall (0 : JetPrototype.Space) R)

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPositiveRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cylinder densities and source measures in characteristic coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotCharacteristicEquiv : CharacteristicPhase ≃ᵐ
    JetCopyDatum.AttainedCapSequence.HotKineticPhase := characteristicEquiv.trans hotChart

def cylinderPullback (a A R : ℝ)
    (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ) : CharacteristicPhase → ℝ :=
  (JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R).indicator f ∘ hotCharacteristicEquiv

def sourcePullback (μ : Measure JetCopyDatum.AttainedCapSequence.HotKineticPhase) :
    Measure CharacteristicPhase := μ.map hotCharacteristicEquiv.symm

instance sourcePullback_finite (μ : Measure JetCopyDatum.AttainedCapSequence.HotKineticPhase)
    [IsFiniteMeasure μ] : IsFiniteMeasure (sourcePullback μ) := by
  unfold sourcePullback
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The positive-time region below the limiting hot horizon -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotRegion (U : ℝ≥0∞) : Set Published.SpaceTime :=
  {z | 0 < z.1 ∧ ENNReal.ofReal z.1 < U}

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicCutoffGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Transport of collision kernels into characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def transportedKernel (e : X ≃ᵐ Y) (K : Kernel Y Y) : Kernel X X :=
  (K.comap e e.measurable).map e.symm

instance transportedKernel_sFinite (e : X ≃ᵐ Y) (K : Kernel Y Y) [IsSFiniteKernel K] :
    IsSFiniteKernel (transportedKernel e K) := by
  unfold transportedKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness

end

end

section

/-! # Smooth phase cutoffs around a bounded physical flight cylinder -/

noncomputable section

open Set MeasureTheory Metric

namespace BoltzmannNonuniqueness.EuclideanFlight

def centeredFlightChart (t : ℝ) (x : Velocity) : (Velocity × Velocity) ≃ₜ (Velocity × Velocity) where
  toFun p := (p.1+t • p.2-x,p.2)
  invFun p := (p.1+x-t • p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LargeOutput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Decay of truncated chart measures at large axial output -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.LargeOutputSlices

def boundedIncoming (U : ℝ) : Set Velocity := {p | ‖p‖ ≤ U}

def boundedBall (v : Velocity) (R U : ℝ) : Set Coordinates :=
  ballRegion v R ∩ (boundedIncoming U ×ˢ univ)

end BoltzmannNonuniqueness.LargeOutputSlices

end

end

section

/-! # Uniform decay of the normalized kernel at large output velocity -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.LargeOutputSlices

namespace BoltzmannNonuniqueness.LargeOutput

def axialConstant (q L R : ℝ) : ℝ :=
  tiltConstant * (4 * L) * (2 * AffineSlices.rectangleConstant q R R)

def transverseConstant (q L R : ℝ) : ℝ :=
  tiltConstant * (4 * L) * 2 * (8 * R ^ 2) * TransverseAverage.expectationConstant q

end BoltzmannNonuniqueness.LargeOutput

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LateBoxAccessMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The expanding boxes used in the finite-horizon growth contradiction -/

noncomputable section

open Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

def lateBox (κ d t : ℝ) : Set (V × V) :=
  {p | ‖p.1-(κ*t) • firstAxis‖ < d*κ*t ∧ ‖p.2‖ < 5}

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CompactCapFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The constructed cap sequence and its compactness bounds

The actual positive cutoff solutions satisfy bounds sufficient for the
compactness and limit constructions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

structure CompactCapFamily (s₀ η K α γ d₀ q : ℝ) where
  time : ℝ
  time_pos : 0 < time
  time_le : time ≤ 1/32
  approximation : ∀ N, CapApproximation s₀ η K α γ d₀ q time N
  density_ui : UniformIntegrable (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_ui : UniformIntegrable (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_ui : UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_ui : UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  initial_l1 : Tendsto (fun N => ∫ p,
    ‖periodicInitial s₀ η K α γ d₀ q N (approximation N).coefficient p-
      JetPeriodicDatum.datum s₀ η K α γ d₀ p‖) atTop (𝓝 0)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapHotTransportBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common weak subsequence for every hot pair window -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

structure HotPairExtraction (S : AttainedCapSequence F) extends HotLimitExtraction S where
  pairProfile : ℕ → HotPairPhase → ℝ
  pairWeak : ∀ j : ℕ, Published.WeakL1Converges (hotPairWindowVolume (j+1) (j+1))
    (fun n => CollisionCompactness.pairProduct (S.hotDensity (indices n))) (pairProfile j)
  pairNonneg : ∀ j : ℕ, ∀ᵐ z ∂hotPairWindowVolume (j+1) (j+1), 0 ≤ pairProfile j z

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPairWindowGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nested spatial windows for the actual hot pair sequence -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def hotPairWindowSet (A R : ℝ) : Set HotPairPhase :=
  (Icc (0:ℝ) A ×ˢ Metric.closedBall (0 : JetPrototype.Space) R) ×ˢ univ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TightCapFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed cap families with uniform tightness in velocity -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

structure TightCapFamily (s₀ η K α γ d₀ q : ℝ) extends CompactCapFamily s₀ η K α γ d₀ q where
  density_tight : UnifTight (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_tight : UnifTight (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_tight : UnifTight (fun N => CollisionCompactness.gainDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_tight : UnifTight (fun N => CollisionCompactness.lossDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A compatible global weak limit for the actual hot pair products -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotPairExtraction.pairLimit (E : HotPairExtraction S) (z : HotPairPhase) : ℝ :=
  max 0 (liminf (fun j => E.pairProfile j z) atTop)

def HotPairExtraction.subsequence (E : HotPairExtraction S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : HotPairExtraction S where
  toHotLimitExtraction := E.toHotLimitExtraction.subsequence φ hφ
  pairProfile := E.pairProfile
  pairWeak := fun j => (E.pairWeak j).comp hφ.tendsto_atTop
  pairNonneg := E.pairNonneg

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The hot pair limit in the physical Euclidean averaging coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotPairChart : (Published.SpaceTime × (Velocity × Velocity)) ≃ᵐ
    JetCopyDatum.AttainedCapSequence.HotPairPhase :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) spaceEquiv)
    (MeasurableEquiv.refl (Velocity × Velocity))

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Factorized velocity-pair moments of actual cap-family weak limits -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum

def averageWeight (χ : Published.KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (z : Published.KineticPhase) : ℝ := ψ z.2*χ z

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ProductKineticCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Kinetic cutoffs preserving velocity tests on a spacetime patch -/

noncomputable section

open Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.Compactness

def productCutoff (χ : Published.SpaceTime → ℝ) (β : Velocity → ℝ)
    (z : Published.KineticPhase) : ℝ := χ z.1*β z.2

end BoltzmannNonuniqueness.Compactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightLocalL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive lower bound for the hot weight on bounded velocity sets -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityWeight

def compactLower (R : ℝ) : ℝ :=
  Real.exp (-R^2)*(1+R^2)^(-50 : ℝ)

end BoltzmannNonuniqueness.VelocityWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityAverageDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint integrability for damped velocity-dependent characteristic lines -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def velocityLineResolvent (r : Velocity × FourierSpace → ℂ) (p : Velocity × FourierSpace) : ℂ :=
  dampedLineResolvent (fun x => r (p.1,x)) (characteristicDirection p.1) p.2

def velocityLineAverage (r : Velocity × FourierSpace → ℂ) (x : FourierSpace) : ℂ :=
  ∫ v, velocityLineResolvent r (v,x)

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticWindowL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Regrouping time and phase space in the weak limit -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

def regroup (f : (ℝ × Position) × Velocity → ℝ) (z : ℝ × Phase) : ℝ :=
  f ((z.1,z.2.1),z.2.2)

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapMildLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A genuine local mild solution obtained from the actual positive cap family -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

/-- The characteristic identity uses the full physical collision terms and the
prescribed initial density. The spacetime identity determines a continuous-time
representative through the Bochner integral of the collision source. -/
structure MildCollisionSolution (T : ℝ) (f₀ : Density)
    (g : (ℝ × Position) × Velocity → ℝ) : Prop where
  measurable : Measurable g
  nonnegative : ∀ z, 0 ≤ g z
  integrable : Integrable g ((AnnularEnvelope.timePositionVolume T).prod volume)
  pair_integrable : Integrable (CollisionCompactness.pairDensity g)
    ((AnnularEnvelope.timePositionVolume T).prod volume)
  characteristic : TorusFlight.along (TorusFlight.regroup g) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => f₀ z.2+Published.timePrimitive (volume.restrict (Icc 0 T))
      (TorusFlight.along (TorusFlight.regroup
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p))) z)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildRenormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A strongly continuous representative of the constructed local mild solution -/

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

namespace MildCollisionSolution

def source (g : (ℝ × Position) × Velocity → ℝ) (p : (ℝ × Position) × Velocity) : ℝ :=
  CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p

def characteristicSource (g : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (source g))

def evolution (T : ℝ) (f₀ : Density) (g : (ℝ × Position) × Velocity → ℝ) : Evolution :=
  TorusFlight.eulerianProfile (volume.restrict (Icc 0 T)) f₀ (characteristicSource g)

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveMildRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonnegative strongly continuous representative with the exact initial trace -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.MildCollisionSolution

def positiveEvolution (T : ℝ) (f₀ : Density) (g : (ℝ × Position) × Velocity → ℝ) : Evolution :=
  fun t p => max (evolution T f₀ g t p) 0

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ExponentialPairIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable exponential collision pairs from the common squared moment envelope -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def exponentialPair (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  (VelocityMoment.weight z.2.1*f (z.1,z.2.1))*(VelocityMoment.weight z.2.2*f (z.1,z.2.2))

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalFrequencyWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical loss frequency in kinetic spacetime coordinates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def kineticFrequency (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  2*Real.pi*∫ w, ‖p.2-w‖*f (p.1,w)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Physical spacetime frequencies in the velocity spectral estimate -/
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def physicalFourierFrequency (k : FourierSpace) : SpaceTime :=
  (2*Real.pi) • WithLp.ofLp k

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual cold datum has a nonnegative strong local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

/-- The local solution properties established before the entropy and continuation steps. -/
structure LocalMildSolution (T : ℝ) (f₀ : Density) (F : Evolution) : Prop where
  strong : StrongEarly T F
  measurable : Measurable (fun z : ℝ × Phase => F z.1 z.2)
  nonnegative : ∀ t p, 0 ≤ F t p
  initial : F 0 = f₀
  integrable_each_time : ∀ t, Integrable (F t)
  pair_integrable : Integrable (CollisionCompactness.pairDensity (kineticDensity F))
    ((AnnularEnvelope.timePositionVolume T).prod volume)
  characteristic : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => f₀ z.2 + Published.timePrimitive (volume.restrict (Icc 0 T))
      (fun w => collision (F w.1) (TorusFlight.flight w.1 w.2).1
        (TorusFlight.flight w.1 w.2).2) z)

end BoltzmannNonuniqueness

end

end

section

/-! # Local admissibility and terminal traces for global continuation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

/-- Local admissibility retains endpoint terms for arbitrary tests. This permits pasting at
`T` without assuming that a test vanishes at the joining time. -/
structure AdmissibleLocal (T : ℝ) (f₀ : Density) (F : Evolution) : Prop
    extends LocalMildSolution T f₀ F where
  datum : FiniteEntropyDatum f₀
  finite_each_time : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (F t)
  uniform_moment : ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ z, entropyMoment (F t) z) ≤ C
  collision_fibers : ∀ᵐ p ∂volume.restrict (boundedTimes T),
    Integrable (fun q : Velocity × Sphere => collisionKernel p.2.2 q.1 q.2 *
      F p.1 (p.2.1,scatterLeft p.2.2 q.1 q.2)*F p.1 (p.2.1,scatterRight p.2.2 q.1 q.2))
      ((volume : Measure Velocity).prod sphereArea) ∧
    Integrable (fun q : Velocity × Sphere => collisionKernel p.2.2 q.1 q.2 *
      F p.1 p.2*F p.1 (p.2.1,q.1)) ((volume : Measure Velocity).prod sphereArea)
  renormalized_integrable : ∀ β φ, IntegrableOn (renormalizedIntegrand F β φ) (boundedTimes T)
  renormalized_balance : ∀ (β : Renormalization) (φ : KineticTest),
    (∫ z in boundedTimes T, renormalizedIntegrand F β φ z)+
      (∫ p, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) =
      ∫ p, maxwellian p.2*β.toFun (F T p/maxwellian p.2)*φ.toFun T p.1 p.2
  local_mass_integrable : ∀ φ : MassTest, IntegrableOn
    (fun z : ℝ × Phase => F z.1 z.2*φ.transportDerivative z.1 z.2) (boundedTimes T)
  local_mass_balance : ∀ φ : MassTest,
    (∫ z in boundedTimes T, F z.1 z.2*φ.transportDerivative z.1 z.2)+
      (∫ p, f₀ p*φ.toFun 0 p.1) = ∫ p, F T p*φ.toFun T p.1
  momentum_conservation : ∀ t ∈ Icc 0 T, momentum (F t) = momentum f₀
  energy_conservation : ∀ t ∈ Icc 0 T, energy (F t) = energy f₀
  entropy_inequality : ∀ t ∈ Icc 0 T,
    ENNReal.ofReal (relativeEntropy (F t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (F s)) ≤ ENNReal.ofReal (relativeEntropy f₀)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The moving cutoff preserves entropy dissipation at the actual weak collision limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def rateDissipation (μ : Measure X) (f : X × Velocity → ℝ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹*∫⁻ z, extendedEntropyProduction (postRate f z) (preRate f z)
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision-rate dissipation is the physical entropy dissipation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r5fcdae_2 : SFinite ((volume : Measure BoltzmannNonuniqueness.Velocity).prod
    BoltzmannNonuniqueness.sphereArea) := Measure.prod.instSFinite
def kernelEntropyProduction (f : X × Velocity → ℝ)
    (p : X × (Velocity × (Velocity × Sphere))) : ℝ≥0∞ :=
  ENNReal.ofReal (collisionKernel p.2.1 p.2.2.1 p.2.2.2) *
    extendedEntropyProduction
      (f (p.1,scatterLeft p.2.1 p.2.2.1 p.2.2.2) *
        f (p.1,scatterRight p.2.1 p.2.2.1 p.2.2.2))
      (f (p.1,p.2.1)*f (p.1,p.2.2.1))

def collisionEntropyGrouping : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    X × (Velocity × (Velocity × Sphere)) :=
  collisionGrouping.trans MeasurableEquiv.prodAssoc

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_SubcapMildLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compactness bounds for positive cutoff approximations below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

structure CompactFamily (s₀ η K α γ d₀ q : ℝ) where
  time : ℝ
  time_pos : 0 < time
  time_le : time ≤ 1/32
  approximation : ∀ N, Approximation s₀ η K α γ d₀ q time N
  density_ui : UniformIntegrable (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_ui : UniformIntegrable (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_ui : UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_ui : UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  initial_l1 : Tendsto (fun N => ∫ p,
    ‖periodicInitial s₀ η K α γ d₀ q N (approximation N).coefficient p-
      JetPeriodicDatum.datum s₀ η K α γ d₀ p‖) atTop (𝓝 0)


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Approximation families below the cap with uniform velocity tightness -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

structure TightFamily (s₀ η K α γ d₀ q : ℝ) extends CompactFamily s₀ η K α γ d₀ q where
  density_tight : UnifTight (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_tight : UnifTight (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_tight : UnifTight (fun N => CollisionCompactness.gainDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_tight : UnifTight (fun N => CollisionCompactness.lossDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Factorized velocity-pair moments of weak limits below the cap -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

def averageWeight (χ : Published.KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (z : Published.KineticPhase) : ℝ := ψ z.2*χ z


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_DormantConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact, tight zero-hot approximation families -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

structure DormantFamily (s₀ η K α γ d₀ q : ℝ) extends BelowCap.TightFamily s₀ η K α γ d₀ q where
  coefficient_zero : ∀ N, (approximation N).coefficient = 0
  hot_quadratic : ∀ N t, t ∈ Icc 0 time →
    PhaseEssSup.size (fun p => (approximation N).solution.value (t,p)-
      ∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) (approximation N).amplitude)
        time N (approximation N).solution.value i (t,p)) ≤ t^2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # An admissible comparison solution from the actual zero-hot sequence -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

structure DormantLimit {s₀ η K α γ d₀ q : ℝ} (A : DormantFamily s₀ η K α γ d₀ q) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  density : (ℝ × Position) × Velocity → ℝ
  weak_limit : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume A.time).prod volume)
    (fun n => torusPhysical q (A.approximation (subsequence n)).solution.value) density
  mild : MildCollisionSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density
  admissible : AdmissibleLocal A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
    (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A uniform physical majorant for the actual zero-hot family -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

def dormantMajorant (s₀ η K α d₀ q ε : ℝ) (z : Published.KineticPhase) : ℝ :=
  JetSupersolution.transverseDecayConstant K d₀ ε*‖transverse z.1.2‖^9+
    (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))*z.1.1^2*H q z.2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact small-time scaling of the dormant majorant -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

def kineticDilation (r : ℝ) (z : Published.KineticPhase) : Published.KineticPhase :=
  ((r*z.1.1,r • z.1.2),z.2)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_DormantBoxLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform small-time bounds on bounded kinetic boxes away from the axis -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

def awayKineticBox (B R ε : ℝ) : Set Published.KineticPhase :=
  ((Icc (0:ℝ) B ×ˢ Metric.closedBall (0:Velocity) R) ×ˢ Metric.closedBall (0:Velocity) R) ∩
    {z | ε ≤ ‖transverse z.2‖}

def dormantBoxBound (s₀ η K α d₀ q ε B R r : ℝ) : ℝ :=
  JetSupersolution.transverseDecayConstant K d₀ ε*r^8*R^9+
    (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))*r*B^2*(1+ε^(-q))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SeparationBoxContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably many bounded boxes for the final separation argument -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.JetCopyDatum

def separationBox (j : ℕ) : Set Published.KineticPhase :=
  awayKineticBox 1 (j+1) (1/((j:ℝ)+1))

def scaledBoxMass (r : ℝ) (f : Published.KineticPhase → ℝ) (j : ℕ) : ℝ :=
  ∫ z in separationBox j, r⁻¹*f (kineticDilation r z)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDilationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The four-dimensional Jacobian of kinetic time-space dilation -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace BoltzmannNonuniqueness.JetCopyDatum

def kineticDilationEquiv (r : ℝ) (hr : r ≠ 0) :
    Published.KineticPhase ≃ᵐ Published.KineticPhase :=
  (Homeomorph.smul (Units.mk0 r hr) : (ℝ × Velocity) ≃ₜ (ℝ × Velocity)).toMeasurableEquiv.prodCongr
    (MeasurableEquiv.refl Velocity)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_OffAxisBoxExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Choosing a bounded representative of a collision kernel on the null axis -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_offAxis :
    MeasurableSet {z : X × Velocity | transverse z.2 ≠ 0} := by
  exact ((measurableSet_singleton 0).preimage
    (measurable_transverse.comp measurable_snd)).compl

def offAxis (K : Kernel (X × Velocity) Velocity) : Kernel (X × Velocity) Velocity := by
  classical
  exact Kernel.piecewise measurableSet_offAxis K 0

instance offAxis_sFinite (K : Kernel (X × Velocity) Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (offAxis K) := by
  classical
  unfold offAxis
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_FreeCoreMismatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The free-core gain kernel has the positive-slab mass bound -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def growthConstant (K α γ q : ℝ) : ℝ :=
  (K * max 1 (α*γ)⁻¹) * JetGaussianProduct.coefficient *
    (SheetTotal.bound q (2*Real.exp (16*(1+α)^2))).toReal

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The actual free-core kernel in the coordinates of positive iteration -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def kineticColdKernel (η K α γ s d : ℝ) (a : Bool) : Kernel SpaceTime Velocity :=
  (coreKernel η K α γ s d a).comap
    (fun z => (z.1,JetPeriodicDatum.spatialMap z.2))
    (measurable_fst.prodMk (JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp measurable_snd))

instance kineticColdKernel_sFinite (η K α γ s d : ℝ) (a : Bool) :
    IsSFiniteKernel (kineticColdKernel η K α γ s d a) := by
  unfold kineticColdKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def kineticFreeKernel (η K α γ s d q : ℝ) (a : Bool) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (kineticColdKernel η K α γ s d a) q)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Endpoint representative invariance for the actual free-core iterates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def kineticCoreDensity (η K α γ s d : ℝ) (sign : Bool) (z : KineticPhase) : ℝ≥0∞ :=
  ENNReal.ofReal (JetFreeTransport.free η K α γ s d z.1.1 sign
    (JetPeriodicDatum.spatialMap z.1.2,z.2))

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DilatedCoreDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive gain kernels under the actual cap dilation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def dilatedColdKernel (r η K α γ s d : ℝ) (sign : Bool) : Kernel SpaceTime Velocity :=
  ((kineticColdKernel η K α γ s d sign).comap
    (fun z : SpaceTime => (r*z.1,r • z.2)) (by fun_prop)).withDensity
      (fun _ _ => ENNReal.ofReal r)

instance dilatedColdKernel_sFinite (r η K α γ s d : ℝ) (sign : Bool) :
    IsSFiniteKernel (dilatedColdKernel r η K α γ s d sign) := by
  unfold dilatedColdKernel
  exact Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

def dilatedFreeKernel (r η K α γ s d q : ℝ) (sign : Bool) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (dilatedColdKernel r η K α γ s d sign) q)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Density representatives for the dilated free-core measures -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

def dilatedCoreDensity (r η K α γ s d : ℝ) (sign : Bool) (z : KineticPhase) : ℝ≥0∞ :=
  ENNReal.ofReal r*kineticCoreDensity η K α γ s d sign ((r*z.1.1,r • z.1.2),z.2)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TranslatedCoreKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dilated free kernels for the actual periodic labels -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

def latticeVector (n : Lattice) : Velocity := WithLp.toLp 2 (fun k => (n k : ℝ))

def copyColdKernel (r s₀ η K α γ d₀ : ℝ) (i : Label) : Kernel SpaceTime Velocity :=
  (JetCoreSheet.dilatedColdKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
    (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive).comap
      (fun z => (z.1,z.2-r⁻¹ • latticeVector i.lattice)) (by fun_prop)

instance copyColdKernel_sFinite (r s₀ η K α γ d₀ : ℝ) (i : Label) :
    IsSFiniteKernel (copyColdKernel r s₀ η K α γ d₀ i) := by
  unfold copyColdKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def copyFreeKernel (r s₀ η K α γ d₀ q : ℝ) (i : Label) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (copyColdKernel r s₀ η K α γ d₀ i) q)

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialBandMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite exceptional axial intervals for the two-gain argument -/

noncomputable section

open Set MeasureTheory

namespace BoltzmannNonuniqueness.AxialFlow

def collapsedCenters (α t z : ℝ) : Finset ℝ :=
  {z/t,1-α,1+α,-1-α,-1+α}

def profileCenters (α γ t z : ℝ) (S : Finset ℝ) : Finset ℝ :=
  S.biUnion fun s => {velocity 1 α γ s t z,velocity (-1) α γ s t z}

def bands (S : Finset ℝ) (b : ℝ) : Set ℝ :=
  ⋃ c ∈ S, {w | |w-c| < b}

end BoltzmannNonuniqueness.AxialFlow

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MainCoreScaleWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable regions selecting the unique main periodic core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def mainCoreRegion (s₀ η r : ℝ) (N : ℕ) (i : Label) : Set SpaceTime :=
  {z | i.annulus < N ∧ r*z.1 ≤ 1/32 ∧
    r • z.2 ∈ spatialEnlargement s₀ η (r*z.1) i}

theorem measurableSet_mainCoreRegion (s₀ η r : ℝ) (N : ℕ) (i : Label) :
    MeasurableSet (mainCoreRegion s₀ η r N i) := by
  by_cases hi : i.annulus < N
  · have hE : MeasurableSet (JetGeometry.enlargement η (JetGeometry.jetScale s₀ η i.annulus)
        i.positive) := Metric.isClosed_cthickening.measurableSet
    have hy : MeasurableSet {z : SpaceTime |
        VelocityWeight.transverse (r • z.2)-transverseShift i.lattice ∈
          JetGeometry.enlargement η (JetGeometry.jetScale s₀ η i.annulus) i.positive} :=
      hE.preimage (by fun_prop)
    have hz : MeasurableSet {z : SpaceTime |
        |VelocityWeight.axial (r • z.2)-axialShift i.lattice| ≤ 1/8+2*(r*z.1)+1/16} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have ht : MeasurableSet {z : SpaceTime | r*z.1 ≤ 1/32} :=
      measurableSet_le (by fun_prop) measurable_const
    simp only [mainCoreRegion,hi,true_and]
    exact ht.inter (hy.inter hz)
  · simp [mainCoreRegion,hi]

def mainCoreKernel (s₀ η r : ℝ) (N : ℕ) (K : Label → Kernel SpaceTime Velocity) :
    Kernel SpaceTime Velocity := by
  classical
  exact Kernel.sum (fun i => Kernel.piecewise (measurableSet_mainCoreRegion s₀ η r N i) (K i) 0)

instance mainCoreKernel_sFinite (s₀ η r : ℝ) (N : ℕ) (K : Label → Kernel SpaceTime Velocity)
    [∀ i, IsSFiniteKernel (K i)] : IsSFiniteKernel (mainCoreKernel s₀ η r N K) := by
  classical
  unfold mainCoreKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedCoreSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The selected main free core and its uniform positive gain bound -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

def selectedColdKernel (r s₀ η K α γ d₀ : ℝ) (N : ℕ) : Kernel SpaceTime Velocity :=
  mainCoreKernel s₀ η r N (copyColdKernel r s₀ η K α γ d₀)

instance selectedColdKernel_sFinite (r s₀ η K α γ d₀ : ℝ) (N : ℕ) :
    IsSFiniteKernel (selectedColdKernel r s₀ η K α γ d₀ N) := by
  unfold selectedColdKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def selectedFreeKernel (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Kernel KineticPhase Velocity :=
  ChartKernel.offAxis (ChartKernel.inputKernel (selectedColdKernel r s₀ η K α γ d₀ N) q)

def positiveMainKernel (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Kernel KineticPhase Velocity :=
  selectedFreeKernel r s₀ η K α γ d₀ q N + selectedFreeKernel r s₀ η K α γ d₀ q N

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A jointly measurable density of the selected main free core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

def copyCoreDensity (r s₀ η K α γ d₀ : ℝ) (i : Label) (z : KineticPhase) : ℝ≥0∞ :=
  JetCoreSheet.dilatedCoreDensity r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
    (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive
    ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2)

def selectedCoreDensity (r s₀ η K α γ d₀ : ℝ) (N : ℕ) (z : KineticPhase) : ℝ≥0∞ := by
  classical
  exact ∑' i : Label, if z.1 ∈ mainCoreRegion s₀ η r N i
    then copyCoreDensity r s₀ η K α γ d₀ i z else 0

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_CoreDensityTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The exact free-core integral over three Euclidean thermal parameters -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def thermalCoordinates (w : FiveGainMap.V) : Transverse × ℝ :=
  SheetMeasures.join.symm (WithLp.toLp 2 w)

def thermalWeight (η K α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (w : FiveGainMap.V) : ℝ := weight η K α γ s d t a x (thermalCoordinates w)

def thermalPoint (α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (w : FiveGainMap.V) : Velocity :=
  JetCoreMeasure.velocityMap (JetPrototype.sign a) α γ s d t x.2 (thermalCoordinates w)

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Joint measurable thermal parameters on nonnegative time

Clamping time at zero provides a globally measurable representative, equal to
the physical parametrization at every nonnegative collision time.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

abbrev ThermalArguments := ℝ × (Space × FiveGainMap.V)

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # A fixed-cardinality exceptional list has uniformly small first-core mass -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

def slabAmplitude (K α γ a : ℝ) : ℝ :=
  (K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient/a

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DilatedTwoCoreLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact measure representation of the dilated cold core

The masks stay at their original physical scale. Dilation is carried by the
measure factor and the time/position arguments, without identifying masks.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def rescaledCoreMeasure (r η K α γ μ d q : ℝ) (sign : Bool)
    (t : ℝ) (x : JetPrototype.Space) (v : Velocity) : Measure Velocity :=
  ENNReal.ofReal r • ChartKernel.offAxis
    (normalizedCoreKernel η K α γ (r*μ) d q sign) ((r*t,r • x),v)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RedundantParameterSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The redundant coordinates recover the actual graph-chart velocity -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.RedundantPlane

def normalVector (v p : Velocity) : V := WithLp.ofLp (v-p)

def crossVelocity (v p : Velocity) (L : V) : Velocity :=
  WithLp.toLp 2 (normalVector v p ⨯₃ L)

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Redundant parameters for the normalized positive collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.RedundantPlane

def normalCoefficient (v p : Velocity) (L : V) : ℝ :=
  (normalVector v p ⬝ᵥ L)/normSq (normalVector v p)

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_CoreParameterStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual free-core normalized gain as a six-parameter integral -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

def parameterPoint (α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (v : Velocity) (w L : FiveGainMap.V) : Velocity :=
  v+crossVelocity v (thermalPoint α γ s d t a x w) L

def parameterDensity (η K α γ s d t q : ℝ) (a : Bool) (x : JetPrototype.Space)
    (v : Velocity) (w L : FiveGainMap.V) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (thermalWeight η K α γ s d t a x w) *
    normalDensity (normalCoefficient v (thermalPoint α γ s d t a x w) L) *
    ENNReal.ofReal (H q (parameterPoint α γ s d t a x v w L)/H q v)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The parameterized gain and its thermal collision map -/

noncomputable section

open scoped Matrix
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

def jetPosition (x : FiveGainMap.V) : JetPrototype.Space :=
  (transverse (WithLp.toLp 2 x),x 2)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RescaledParameterSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The physical dilated gain in bounded thermal and plane parameters -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

def rescaledParameterDensity (r η K α γ μ d t q : ℝ) (a : Bool) (x : JetPrototype.Space)
    (v : Velocity) (w L : FiveGainMap.V) : ℝ≥0∞ :=
  ENNReal.ofReal r*parameterDensity η K α γ (r*μ) d (r*t) q a (r • x) v w L

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform compact parameter support for retained physical collisions -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity
open BoltzmannNonuniqueness.RedundantPlane

namespace BoltzmannNonuniqueness.JetCoreSheet

def retainedPlaneBound (α b Vmax : ℝ) : ℝ :=
  (2*Vmax)^2/(b/2)^2+(Vmax+(α+3))^2+1

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # A common bound for retained physical gain densities on a positive slab -/

noncomputable section

open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def parameterSlabBound (K α γ q a b V : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/a)*JetThermalKernel.bound) *
    ENNReal.ofReal ((1+b^(-q))/compactLower V)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_CoreJointParameterDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint measurability of the physical six-parameter collision density -/

noncomputable section

open MeasureTheory
open scoped Matrix ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

abbrev ParameterArguments := (ℝ × JetPrototype.Space) × (Velocity × (FiveGainMap.V × FiveGainMap.V))

attribute [local irreducible] thermalPoint parameterPoint parameterDensity
  thermalWeight RedundantPlane.normalCoefficient RedundantPlane.normalDensity

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FiveGainPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact pullback convergence for the actual five thermal gains -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Function
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

def controlDomain : Set ThermalControls := {q | q.1 ∈ positiveDomain}

/-- Seven output coordinates and twenty-eight complementary parameters. -/
def controlCoordinates : ThermalControls ≃L[ℝ] State × (Fin 28 → ℝ) :=
  (LinearEquiv.ofFinrankEq _ _ (by
    simp [ThermalControls,Parameters,State,V,Module.finrank_prod,
      Module.finrank_pi_fintype])).toContinuousLinearEquiv

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The five-gain output coordinates preserve physical kinetic volume -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.FiveGainMap

def toKinetic : State ≃ᵐ Published.KineticPhase :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 V) (MeasurableEquiv.toLp 2 V))).trans
      MeasurableEquiv.prodAssoc.symm

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Bounded actual five-gain parameter densities

Each factor is the six-parameter density of the physical rescaled core.
Arbitrary retained-path masks are allowed, with their velocity and time
restrictions stated explicitly. The final lemma applies the proved thermal
map pullback theorem to these actual factors.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def stagePrevious (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : State :=
  thermalPath (fun i => JetPrototype.sign (colors i)) α γ env q i.val

def stagePosition (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : V :=
  let z := stagePrevious colors α γ env q i
  z.2.1-(z.1-q.1.1 i) • z.2.2

def stagePoint (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : Velocity :=
  parameterPoint α γ (env.1 i) (env.2.1 i) (q.1.1 i) (colors i)
    (jetPosition (stagePosition colors α γ env q i))
    (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2) (q.2 i) (q.1.2 i)

def stageDensity (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) (i : Fin 5) : ℝ≥0∞ :=
  rescaledParameterDensity r η K α γ (env.1 i) (env.2.1 i) (q.1.1 i) qexp (colors i)
    (jetPosition (stagePosition colors α γ env q i))
    (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2) (q.2 i) (q.1.2 i)

def pathDensity (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) : ℝ≥0∞ :=
  ∏ i : Fin 5, stageDensity colors r η K α γ qexp env q i

def stageGood (colors : Fin 5 → Bool) (α γ a b Vmax : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) (i : Fin 5) : Prop :=
  a ≤ q.1.1 i ∧ ‖WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2‖ ≤ Vmax ∧
    b ≤ ‖transverse (stagePoint colors α γ env q i)‖

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Product volume for the five physical collision parameter blocks -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

abbrev StageControls := (ℝ × V) × V

def packControls : (Fin 5 → StageControls) ≃ᵐ ThermalControls :=
  (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × V) V (Fin 5)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.arrowProdEquivProdArrow ℝ V (Fin 5))
      (MeasurableEquiv.refl (Fin 5 → V)))

def integrateControls : (n : ℕ) → ((Fin n → StageControls) → ℝ≥0∞) → ℝ≥0∞
  | 0, F => F Fin.elim0
  | n+1, F => ∫⁻ p : StageControls, integrateControls n (fun q => F (Fin.cons p q))

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # A compact parameter box for all five retained collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def velocityParameterBall (R : ℝ) : Set V :=
  (WithLp.ofLp : Velocity → V) '' closedBall 0 R

def parameterBox (a T R : ℝ) : Set ThermalControls :=
  ((pi univ (fun _ : Fin 5 => Icc a T)) ×ˢ
    (pi univ (fun _ : Fin 5 => velocityParameterBall R))) ×ˢ
      (pi univ (fun _ : Fin 5 => velocityParameterBall 1))

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteParameterChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite parameterized gain chain as one product integral

This is the Fubini assembly used after replacing each physical collision by its
thermal and redundant-plane parameters. The transition maps and densities are
explicit functions, and the conclusion is an exact integral identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def parameterChain (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞) (g : State → ℝ≥0∞)
    (i : ℕ) : ℕ → State → ℝ≥0∞
  | 0, z => g z
  | n+1, z => ∫⁻ p : StageControls, density i z p*
      parameterChain next density g (i+1) n (next i z p)

def chainIntegrand (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞) (g : State → ℝ≥0∞)
    (i : ℕ) : (n : ℕ) → State → (Fin n → StageControls) → ℝ≥0∞
  | 0, z, _ => g z
  | n+1, z, q => density i z (q 0)*
      chainIntegrand next density g (i+1) n (next i z (q 0)) (Fin.tail q)

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ControlledParameterPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact density product along a finite controlled collision path -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def controlledPath (next : ℕ → State → StageControls → State) (controls : ℕ → StageControls)
    (i : ℕ) (z : State) : ℕ → State
  | 0 => z
  | n+1 => next (i+n) (controlledPath next controls i z n) (controls (i+n))

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_StageParameterIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a collision parameter block in physical time, thermal, plane order -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def splitStage : StageControls ≃ᵐ ℝ × (V × V) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ThermalParameterChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable time and collision parameters for one actual positive core gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def stageArguments (z : State) (p : StageControls) : ParameterArguments :=
  ((p.1.1,jetPosition (z.2.1-(z.1-max 0 p.1.1) • z.2.2)),
    (WithLp.toLp 2 z.2.2,(p.2,p.1.2)))

def coreNext (α γ μ d : ℝ) (color : Bool) (z : State) (p : StageControls) : State :=
  (max 0 p.1.1,z.2.1-(z.1-max 0 p.1.1) • z.2.2,
    WithLp.ofLp (parameterPoint α γ μ d (max 0 p.1.1) color
      (stageArguments z p).1.2 (stageArguments z p).2.1 p.2 p.1.2))

def validStage (a : ℝ) : Set (State × StageControls) :=
  {p | a < p.2.1.1 ∧ p.2.1.1 ≤ p.1.1 ∧ transverse (WithLp.toLp 2 p.1.2.2) ≠ 0}

def coreDensity (r η K α γ μ d q a : ℝ) (color : Bool)
    (z : State) (p : StageControls) : ℝ≥0∞ :=
  (validStage a).indicator (fun u : State × StageControls =>
    rescaledParameterDensity r η K α γ μ d (max 0 u.2.1.1) q color
      (stageArguments u.1 u.2).1.2 (stageArguments u.1 u.2).2.1 u.2.2 u.2.1.2) (z,p)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedThermalChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Multiplicative state restrictions along a finite collision path -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

def statePathWeight (next : ℕ → State → StageControls → State)
    (weight : ℕ → State → ℝ≥0∞) (controls : ℕ → StageControls)
    (i n : ℕ) (z : State) : ℝ≥0∞ :=
  ∏ j : Fin n, weight (i+j.val) (controlledPath next controls i z (j.val+1))

attribute [local irreducible] controlledPath

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Actual physical core chains with spatial and velocity restrictions -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap

namespace BoltzmannNonuniqueness.JetCoreSheet

def weightedCoreChain (r η K α γ q a : ℝ) (μ d : ℕ → ℝ) (colors : ℕ → Bool)
    (weight : ℕ → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (i : ℕ) : ℕ → Published.KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ i) (d i) q (colors i))
      (fun z => weight i z * weightedCoreChain r η K α γ q a μ d colors weight f (i+1) n z)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FiveGainConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Identification of the five actual thermal transitions with the analytic path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def cycleFive {A : Type*} (f : Fin 5 → A) (k : ℕ) : A := f ⟨k%5,Nat.mod_lt _ (by decide)⟩

def controlBlocks (q : ThermalControls) : Fin 5 → StageControls :=
  fun i => ((q.1.1 i,q.1.2 i),q.2 i)

def actualNext (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment) :
    ℕ → State → StageControls → State :=
  fun k => coreNext α γ (cycleFive env.1 k) (cycleFive env.2.1 k) (cycleFive colors k)

attribute [local irreducible] thermalPath actualNext

def stageValidity (colors : Fin 5 → Bool) (α γ a : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) : ℝ≥0∞ :=
  (validStage a).indicator (fun _ => 1)
    (stagePrevious colors α γ env q i,controlBlocks q i)

def pathValidity (colors : Fin 5 → Bool) (α γ a : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) : ℝ≥0∞ := ∏ i : Fin 5, stageValidity colors α γ a env q i

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The actual five-collision integrand is the bounded thermal path density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def actualDensity (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ) (env : ThermalEnvironment) :
    ℕ → State → StageControls → ℝ≥0∞ :=
  fun k => coreDensity r η K α γ (cycleFive env.1 k) (cycleFive env.2.1 k) qexp a
    (cycleFive colors k)

def actualFiveIntegrand (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ)
    (env : ThermalEnvironment) (f : Published.KineticPhase → ℝ≥0∞) (q : ThermalControls) : ℝ≥0∞ :=
  chainIntegrand (actualNext colors α γ env) (actualDensity colors r η K α γ qexp a env)
    (fun z => f (toKinetic z)) 0 5 env.2.2 (controlBlocks q)

attribute [local irreducible] thermalPath actualNext actualDensity coreDensity stageDensity

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact physical five-core integrals with all state restrictions retained -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

def actualPathWeight (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞) (q : ThermalControls) : ℝ≥0∞ :=
  statePathWeight (actualNext colors α γ env)
    (fun i z => cycleFive weight i (toKinetic z)) (cycleFive (controlBlocks q)) 0 5 env.2.2

attribute [local irreducible] actualNext actualDensity actualFiveIntegrand controlledPath

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Uniform compact support of a retained physical five-collision path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

def retainedPath (colors : Fin 5 → Bool) (α γ a T b Vmax : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) : Prop := ∀ i : Fin 5,
  q.1.1 i ∈ Icc a T ∧
    ‖WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2‖ ≤ Vmax ∧
    b ≤ ‖transverse (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2)‖ ∧
    ‖stagePoint colors α γ env q i‖ ≤ Vmax ∧ b ≤ ‖transverse (stagePoint colors α γ env q i)‖

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteThermalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite physical thermal families expand into the actual weighted chains -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCoreSheet

def thermalKernelFamily {I : Type*} (r η K α γ q : ℝ)
    (μ d : ℕ → I → ℝ) (colors : ℕ → I → Bool) : ℕ → I → Kernel Published.KineticPhase Velocity :=
  fun i j => dilatedFreeKernel r η K α γ (r*μ i j) (d i j) q (colors i j)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricTwoCoreUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite retained geometric mesh has vanishing fifth gain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GeometricMesh

namespace BoltzmannNonuniqueness.JetCoreSheet

abbrev MeshLabel (J : Finset ℤ) := {k : ℤ // k ∈ J} × Bool

def meshScale (s₀ η : ℝ) (r : ℕ → ℝ) {J : Finset ℤ} (n : ℕ) (j : MeshLabel J) : ℝ :=
  JetGeometry.jetScale s₀ η (jetIndex s₀ η r j.1.val n)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedLargeOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual selected-kernel velocity tails and large-scale truncation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def retainedScaleRegion (s₀ η r M : ℝ) (N : ℕ) : Set Published.SpaceTime :=
  ⋃ (i : Label) (_h : JetGeometry.jetScale s₀ η i.annulus/r ≤ M), mainCoreRegion s₀ η r N i

theorem measurableSet_retainedScaleRegion (s₀ η r M : ℝ) (N : ℕ) :
    MeasurableSet (retainedScaleRegion s₀ η r M N) := by
  apply MeasurableSet.iUnion
  intro i
  exact MeasurableSet.iUnion (fun _ => measurableSet_mainCoreRegion s₀ η r N i)

def retainedFreeKernel (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    Kernel Published.KineticPhase Velocity := by
  classical
  exact Kernel.piecewise ((measurableSet_retainedScaleRegion s₀ η r M N).preimage measurable_fst)
    (selectedFreeKernel r s₀ η K α γ d₀ q N) 0

def discardedFreeKernel (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    Kernel Published.KineticPhase Velocity := by
  classical
  exact Kernel.piecewise ((measurableSet_retainedScaleRegion s₀ η r M N).preimage measurable_fst)
    0 (selectedFreeKernel r s₀ η K α γ d₀ q N)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedTwoGainLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform selected-pair convergence and the two collision times -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel retainedFreeKernel

def selectedPairMass (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) (t₁ t₂ : ℝ) (x v : Velocity) : ℝ≥0∞ :=
  ∫⁻ w, selectedFreeKernel r s₀ η K α γ d₀ q N ((t₂,x-(t₁-t₂) • w),w) univ
    ∂selectedFreeKernel r s₀ η K α γ d₀ q N ((t₁,x),v)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_OriginMeshStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual selected kernel restricted to one origin and a compact scale window -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def originScaleRegion (s₀ η r δ M : ℝ) (N : ℕ) (k : Lattice) : Set Published.SpaceTime :=
  ⋃ (i : Label) (_h : i.lattice = k ∧ δ ≤ JetGeometry.jetScale s₀ η i.annulus/r ∧
    JetGeometry.jetScale s₀ η i.annulus/r ≤ M), mainCoreRegion s₀ η r N i

theorem originScaleRegion_measurable (s₀ η r δ M : ℝ) (N : ℕ) (k : Lattice) :
    MeasurableSet (originScaleRegion s₀ η r δ M N k) := by
  apply MeasurableSet.iUnion
  intro i
  exact MeasurableSet.iUnion (fun _ => measurableSet_mainCoreRegion s₀ η r N i)

def originScaleKernel (r s₀ η K α γ d₀ q δ M : ℝ) (N : ℕ) (k : Lattice) :
    Kernel Published.KineticPhase Velocity := by
  classical
  exact Kernel.piecewise ((originScaleRegion_measurable s₀ η r δ M N k).preimage measurable_fst)
    (selectedFreeKernel r s₀ η K α γ d₀ q N) 0

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact finite mesh labels for the selected origin and scale window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.JetCopyDatum

def windowMesh (η δ M : ℝ) : Finset ℤ :=
  Finset.Icc (index (δ/Real.exp η) η) (index M η)

def meshLabel (s₀ η : ℝ) (r : ℕ → ℝ) {J : Finset ℤ} (n : ℕ) (j : MeshLabel J) : Label :=
  ⟨jetIndex s₀ η r j.1.val n,j.2,0⟩

def meshLabelRegion (s₀ η δ M : ℝ) (r : ℕ → ℝ) (N : ℕ) {J : Finset ℤ}
    (n : ℕ) (j : MeshLabel J) : Set Published.KineticPhase :=
  {z | jetMeshIndex s₀ η (r n) (meshLabel s₀ η r n j).annulus = j.1.val ∧
    δ ≤ meshScale s₀ η r n j/r n ∧ meshScale s₀ η r n j/r n ≤ M ∧
    z.1 ∈ mainCoreRegion s₀ η (r n) N (meshLabel s₀ η r n j)}

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMeshStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual spatial and velocity masks for the finite mesh representation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

def boundedMeshWeight (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} (S : Set Velocity) (j : MeshLabel J) : Published.KineticPhase → ℝ≥0∞ :=
  (meshLabelRegion s₀ η δ M r N n j ∩ {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S}).indicator (fun _ => 1)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicWeakCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Localized renormalized characteristics in Euclidean coordinates -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def projectedPhase (p : Velocity × Velocity) : Phase := (torusProjection p.1,p.2)

def BoundedCutoffSolution.euclideanRenormalizedDensity (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : Published.KineticPhase) : ℝ :=
  S.renormalizedDensity β (z.1.1,projectedPhase (z.1.2,z.2))

def BoundedCutoffSolution.euclideanRenormalizedSource (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : Published.KineticPhase) : ℝ :=
  S.renormalizedSource β (z.1.1,projectedPhase (z.1.2,z.2))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicStrongAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The supported approximants dominate their physical positive characteristic source -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.characteristicGain (S : BoundedCutoffSolution N T f₀) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (gain N S.kineticProfile))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The physical loss defect along each actual bounded characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.characteristicLossDefect (S : BoundedCutoffSolution N T f₀) :
    ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup
    (fun p => lossDensity S.kineticProfile p-loss N S.kineticProfile p))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual damped path with its physical frequency and nonnegative loss defect -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.dampedPath (S : BoundedCutoffSolution N T f₀) (p : Phase) : ℝ → ℝ :=
  TransportPrimitive.damped (lossBound N) (f₀ p)
    (fun r => S.source (r,TorusFlight.flight r p))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_SurvivalProfile
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive-measure region reached from the fixed initial hot core -/

noncomputable section

open MeasureTheory Set Metric

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def survivalCore (ell : ℝ) : Set HotKineticPhase :=
  {z | z.1.1 ∈ Ioo (0:ℝ) (1/2) ∧
    ‖(JetBarrier.flight (-z.1.1) (z.1.2,z.2)).1‖ < ell/16 ∧
      z.2 ∈ HotSeedProfile.velocityCore}

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A measurable fixed positive profile on the transported seed core -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

def survivalProfile (q ell c C : ℝ) (z : HotKineticPhase) : ℝ :=
  (survivalCore ell).indicator (fun z => VelocityWeight.H q z.2 *
    (Real.exp (-(C*(‖z.2‖+1))*z.1.1) * (c*(ell/2)*(HotSeedProfile.normLower q/HotSeedProfile.bound)))) z

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapMixedCollisionLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual collision error vanishes on the physical cold cylinders -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def physicalCollisionError (S : AttainedCapSequence F) (a A : ℝ) (n : ℕ)
    (z : HotKineticPhase) : ℝ :=
  (S.radius n)^2*CollisionCompactness.collisionSource (F.indices n+1) (S.physicalHotDensity n) z+
    S.coldSourceDensity a A n z

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual cold-hot pair density on finite positive-time cylinders -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def mixedDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotPairPhase) : ℝ :=
  S.rescaledColdDensity n (z.1,z.2.1)*S.hotDensity n (z.1,z.2.2)

def mixedPrelimitMeasure (S : AttainedCapSequence F) (n : ℕ)
    (ρ : Measure (ℝ × JetPrototype.Space)) : Measure HotPairPhase :=
  (ρ.prod volume).withDensity (fun z => ENNReal.ofReal (S.mixedDensity n z))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Removal of the actual finite-cap relative-velocity cutoff -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def collisionCutoff (_S : AttainedCapSequence F) (n : ℕ) : ℝ := F.indices n+1

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The physical hot collision equation for the actual finite cap solution -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.physicalCold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : (ℝ × JetPrototype.Space) × Velocity → ℝ :=
  HotRepresentative.density q (GaussianLocal.state F.coldTotal)

def CapApproximation.physicalHot {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : (ℝ × JetPrototype.Space) × Velocity → ℝ :=
  HotRepresentative.density q (GaussianLocal.state F.hot)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Positive finite measures for the physical cap approximants' collision terms -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def physicalGainMeasure (S : AttainedCapSequence F) (a A R : ℝ) (n : ℕ) :
    Measure HotKineticPhase :=
  mixedGainMeasure (coldCylinderVolume a A R) (S.collisionCutoff n)
    (S.rescaledColdDensity n) (S.hotDensity n)

def physicalLossMeasure (S : AttainedCapSequence F) (a A R : ℝ) (n : ℕ) :
    Measure HotKineticPhase :=
  mixedLossMeasure (coldCylinderVolume a A R) (S.collisionCutoff n)
    (S.rescaledColdDensity n) (S.hotDensity n)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Exact mixed collision equation under the attained cap dilation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def collisionDilation (S : AttainedCapSequence F) (n : ℕ)
    (x : ℝ × JetPrototype.Space) : ℝ × JetPrototype.Space :=
  (S.radius n*x.1,S.radius n • x.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_OriginMeshLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cost of removing collisions close to a transverse origin -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PositiveIteration

def nearOriginRegion (c : Transverse) (ρ : ℝ) : Set KineticPhase :=
  {z | ‖transverse z.1.2-c‖ < ρ}

theorem nearOriginRegion_measurable (c : Transverse) (ρ : ℝ) :
    MeasurableSet (nearOriginRegion c ρ) := by
  apply measurableSet_lt _ measurable_const
  unfold transverse
  fun_prop

def awayOriginKernel (c : Transverse) (ρ : ℝ) (K : Kernel KineticPhase Velocity) :
    Kernel KineticPhase Velocity := by
  classical
  exact Kernel.piecewise (nearOriginRegion_measurable c ρ) 0 K

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Exact finite mesh representation of the restricted fixed-origin gain chain -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

def meshFamily (s₀ η K α γ d₀ q : ℝ) (r : ℕ → ℝ) {J : Finset ℤ} (n : ℕ) :
    ℕ → MeshLabel J → Kernel Published.KineticPhase Velocity :=
  thermalKernelFamily (r n) η K α γ q (fun _ j => meshScale s₀ η r n j/r n)
    (fun _ j => d₀*meshScale s₀ η r n j^10) (fun _ j => j.2)

def meshWeights (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    (S : ℕ → Set Velocity) : ℕ → MeshLabel (windowMesh η δ M) → Published.KineticPhase → ℝ≥0∞ :=
  fun i j => boundedMeshWeight s₀ η δ M a T r N n (S (i+1)) j

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapLimitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cumulative collision balance for the actual weak hot limit

Every smooth nonnegative compact phase test has an almost-everywhere time trace
given by a constant and the cumulative incoming gain minus incoming loss.
Both source measures are built from the actual mixed atomic-cold/hot measure.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicGainMeasure (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (A R : ℝ) :
    Measure CharacteristicPhase :=
  (2 : ℝ≥0) • sourcePullback
    (incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))

def HotLimitExtraction.characteristicLossMeasure (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (A R : ℝ) :
    Measure CharacteristicPhase :=
  sourcePullback
    (incomingLossMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ThreeCollisionTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive time window for three ordered collision waits -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev ThreeWaits := ℝ × (ℝ × ℝ)

def threeWaitBox (h : ℝ) : Set ThreeWaits :=
  Ioo 0 (h/4) ×ˢ (Ioo 0 (h/4) ×ˢ Ioo 0 (h/4))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EntrySites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The three physical collision sites in the entry path -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

def entrySite₀ (t : ℝ) (x v : V) (s : ThreeWaits) : ℝ × V :=
  (t+s.1,x+s.1 • v)

def entrySite₁ (t : ℝ) (x v : V) (s : ThreeWaits) (u : V) : ℝ × V :=
  (t+s.1+s.2.1,x+s.1 • v+s.2.1 • u)

def entrySite₂ (t : ℝ) (x v : V) (s : ThreeWaits) (u z : V) : ℝ × V :=
  (t+s.1+s.2.1+s.2.2,x+s.1 • v+s.2.1 • u+s.2.2 • z)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionParameterShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regrouping collision times and outgoing angles preserves their product law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev ThreeAngles := Sphere × (Sphere × Sphere)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedOriginDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Successively chosen nonaxial thresholds for the actual selected kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

attribute [local irreducible] selectedFreeKernel

def transverseRetained (b : ℝ) : Set Velocity := {v | b ≤ ‖transverse v‖}

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Successive bounded nonaxial velocity windows for the actual selected kernel -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def velocityWindow (R b : ℝ) : Set Velocity := {v | ‖v‖ ≤ R ∧ b ≤ ‖transverse v‖}

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual cold partners and densities at the three entry collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryPartner₀ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) : V :=
  beamVelocity θ η α γ σ (entrySite₀ t x v s)

def entryDensity₀ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) : ℝ :=
  beamDensity θ η α γ 1 σ (entrySite₀ t x v s)

def entryPartner₁ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V) : V :=
  beamVelocity θ η α γ (-σ) (entrySite₁ t x v s u)

def entryDensity₁ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V) : ℝ :=
  beamDensity θ η α γ 1 (-σ) (entrySite₁ t x v s u)

def entryPartner₂ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V)
    (a : Sphere × Sphere) : V :=
  beamVelocity θ η α γ 1 (entrySite₂ t x v s u
    (child u (entryPartner₁ θ η α γ σ t x v s u) a.1.1))

def entryDensity₂ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (u : V)
    (a : Sphere × Sphere) : ℝ :=
  beamDensity θ η α γ 1 1 (entrySite₂ t x v s u
    (child u (entryPartner₁ θ η α γ σ t x v s u) a.1.1))

def entryAngularMass (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (κ ρ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
    ‖v-entryPartner₀ θ η α γ σ t x v s‖)*
    ∫⁻ u, (∫⁻ a, accessWeight u (fun _ => entryPartner₁ θ η α γ σ t x v s u)
      (entryPartner₂ θ η α γ σ t x v s u)
      (fun _ => entryDensity₁ θ η α γ σ t x v s u)
      (entryDensity₂ θ η α γ σ t x v s u) κ ρ a
      ∂sphereProbability.prod sphereProbability)
      ∂outgoing (v,entryPartner₀ θ η α γ σ t x v s)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The entry signs are the two physical beam marks -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryMark (σ : ℝ) : HistoryMark := if σ = 1 then 1 else 2

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three physical state transitions follow the geometric entry path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryVelocity₀ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) : V :=
  child v (entryPartner₀ θ η α γ σ t x v s) a.1.1

def entryVelocity₁ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) : V :=
  child (entryVelocity₀ θ η α γ σ t x v s a)
    (entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)) a.2.1.1

def entryVelocity₂ (θ η α γ σ t : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) : V :=
  child (entryVelocity₁ θ η α γ σ t x v s a)
    (entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a) a.2) a.2.2.1

def entryState₁ (θ η α γ σ t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    PhysicalFlightState :=
  (h-s.1,((entrySite₀ t x v s).2,entryVelocity₀ θ η α γ σ t x v s a))

def entryState₂ (θ η α γ σ t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    PhysicalFlightState :=
  (h-s.1-s.2.1,((entrySite₁ t x v s (entryVelocity₀ θ η α γ σ t x v s a)).2,
    entryVelocity₁ θ η α γ σ t x v s a))

def entryState₃ (θ η α γ σ t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    PhysicalFlightState :=
  (h-s.1-s.2.1-s.2.2,((entrySite₂ t x v s (entryVelocity₀ θ η α γ σ t x v s a)
    (entryVelocity₁ θ η α γ σ t x v s a)).2,entryVelocity₂ θ η α γ σ t x v s a))

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Exact retained weight of the three physical entry collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryTerminal (C : ℝ≥0) (κ ρ : ℝ) (p : PhysicalFlightState) : ℝ≥0∞ :=
  clockSurvival C p.1 * (ball (κ • firstAxis) ρ).indicator 1 p.2.2

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive collision-time mass for entry in the actual cold field -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

def entryTimeMass (θ η α γ σ t : ℝ) (x v : V) (κ ρ h : ℝ) (C : ℝ≥0) : ℝ≥0∞ :=
  clockSurvival C h * ∫⁻ s in threeWaitBox h, entryAngularMass θ η α γ σ t x v s κ ρ

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedDampedBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local measure balances with one fixed phase cutoff -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def phaseWeight (β : Phase → ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ := β z.2*F z

def weightedPhaseSource (μ : Measure (ℝ × Phase)) (β : Phase → ℝ) : Measure (ℝ × Phase) :=
  positiveDensityMeasure μ (fun z => β z.2)

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedNonaxialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The Gaussian remainder selected by the actual main-core regions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def copyRemainderDensity (r s₀ η K α γ d₀ : ℝ) (i : Label) (z : KineticPhase) : ℝ≥0∞ :=
  ENNReal.ofReal r*ENNReal.ofReal
    (JetRemainderSheet.remainder η K α γ (JetGeometry.jetScale s₀ η i.annulus)
      (d₀*JetGeometry.jetScale s₀ η i.annulus^10) (r*z.1.1) i.positive
      (JetPeriodicDatum.spatialMap (r • z.1.2)-displacement i.lattice) z.2)

def selectedRemainderDensity (r s₀ η K α γ d₀ : ℝ) (N : ℕ) (z : KineticPhase) : ℝ≥0∞ := by
  classical
  exact ∑' i : Label, if z.1 ∈ mainCoreRegion s₀ η r N i
    then copyRemainderDensity r s₀ η K α γ d₀ i z else 0

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RescaledBoundedGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A principal positive action plus a vanishing error for the actual cold gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def coldGainErrorConstant (s₀ η K α d₀ q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (JetRemainderSheet.uniformConstant K)*
    SheetTotal.bound q (2*Real.exp (16*(1+α)^2))+
  ENNReal.ofReal (JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0))*
    ENNReal.ofReal (HotApplication.realBound q)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapMixedPositiveBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual cold density in the Euclidean dilation coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.dilatedCold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (r : ℝ) (z : KineticPhase) : ℝ :=
  r*(H q z.2*F.coldTotal (r*z.1.1,(JetPeriodicDatum.spatialMap (r • z.1.2),z.2)))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseSliceLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing phase and spatial cutoffs from the masses in a covered box -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotPhaseSlice (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ) (t : ℝ) :
    Measure WeakTime.Phase :=
  positiveDensityMeasure volume (fun p => f (hotCharacteristicEquiv (t,p)))

def hotLateBoxMass (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ)
    (κ d t : ℝ) : ℝ≥0∞ :=
  hotPhaseSlice f t (flight t ⁻¹' ReferenceGeometry.lateBox κ d t)

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapCoefficientExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual normalized source is bounded by the positive main action -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def euclideanColdSource (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase) : ℝ :=
  S.rescaledColdSource n (EuclideanFlight.kineticMap z)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A vanishing uniform error in the actual positive source inequality -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def positiveSourceError (S : AttainedCapSequence F) (B A : ℝ) (n : ℕ) : ℝ≥0∞ :=
  4*(ENNReal.ofReal (S.radius n)*coldGainErrorConstant s₀ η K α d₀ q)+
    ENNReal.ofReal ((S.radius n)^2*(4*HotApplication.realBound q))+
    ENNReal.ofReal (B*S.radius n*A)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # An admissible cap limit retaining its actual approximation sequence -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

structure CapLocalLimit {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  density : (ℝ × Position) × Velocity → ℝ
  weak_limit : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume A.time).prod volume)
    (fun n => torusPhysical q (A.approximation (subsequence n)).solution.value) density
  mild : MildCollisionSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density
  admissible : AdmissibleLocal A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
    (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MovingBoxMass
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving-box mass cap in characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

def flightMeasurableEquiv (t : ℝ) : (Velocity × Velocity) ≃ᵐ (Velocity × Velocity) where
  toFun := flight t
  invFun := flight (-t)
  left_inv p := by
    apply Prod.ext
    · dsimp [flight]; module
    · rfl
  right_inv p := by
    apply Prod.ext
    · dsimp [flight]; module
    · rfl
  measurable_toFun := by
    change Measurable (flight t)
    exact (flight_measurePreserving t).measurable
  measurable_invFun := by
    change Measurable (flight (-t))
    exact (flight_measurePreserving (-t)).measurable

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapCoveredDamping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform proportional loss for the actual hot solutions at positive cold fraction -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def positiveFractionLoss (s₀ η K α γ d₀ q ell : ℝ) : ℝ :=
  (2+escapedConstant s₀ η K α d₀)*hotConstant q+
    2*JetEnvelopeGain.momentConstant K α γ/ell

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic collision source acts on the actual hot density -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicGainKernel (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  transportedKernel hotCharacteristicEquiv (normalPhaseGainKernel
    (GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
      hK hα hγ η E.fraction))

instance HotLimitExtraction.characteristicGainKernel_sFinite (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    IsSFiniteKernel (E.characteristicGainKernel ha hK hα hγ) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  unfold HotLimitExtraction.characteristicGainKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The characteristic loss source has an integrable time density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicLossDensity (E : HotLimitExtraction S) (a A R : ℝ) :
    CharacteristicPhase → ℝ := cylinderPullback a A R (fun z => E.hotLimit z*
      GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positive retained-source balance for the actual hot limit -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicFrequency (E : HotLimitExtraction S)
    (u : CharacteristicPhase) : ℝ :=
  GeometricBackground.frequency E.phase η E.fraction K α γ
    (hotCharacteristicEquiv u).1.1 (hotCharacteristicEquiv u).1.2 (hotCharacteristicEquiv u).2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapEscapingSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A globally measurable extension of the actual slab collision frequency -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicSlabFrequency (E : HotLimitExtraction S)
    (a : ℝ) (u : CharacteristicPhase) : ℝ :=
  GeometricBackground.frequency E.phase η E.fraction K α γ
    (max a (hotCharacteristicEquiv u).1.1)
    (hotCharacteristicEquiv u).1.2 (hotCharacteristicEquiv u).2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot trace has one positive gain-and-retention source -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.retainedSource (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (A R C : ℝ) (β : WeakTime.Phase → ℝ) : Measure CharacteristicPhase :=
  WeakTime.weightedPhaseSource
    (E.characteristicGainKernel ha hK hα hγ ∘ₘ
      positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit)) β+
  positiveDensityMeasure volume (fun z => C*WeakTime.phaseWeight β
    (cylinderPullback a A R E.hotLimit) z-
      WeakTime.phaseWeight β (E.characteristicLossDensity a A R) z)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual gain and self-retention source is a positive collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.retainedKernel (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (C : ℝ) (β : WeakTime.Phase → ℝ) : Kernel CharacteristicPhase CharacteristicPhase :=
  positiveSourceKernel (E.characteristicGainKernel ha hK hα hγ)
    (fun z => β z.2) (fun z => C-E.characteristicSlabFrequency a z)

instance HotLimitExtraction.retainedKernel_sFinite (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (C : ℝ) (β : WeakTime.Phase → ℝ) :
    IsSFiniteKernel (E.retainedKernel ha hK hα hγ C β) := by
  unfold HotLimitExtraction.retainedKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DiagonalVanishingCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual cap shots selected from prescribed-horizon limits -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.retime {s₀ η K α γ d₀ q T U : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (h : T = U) :
    CapApproximation s₀ η K α γ d₀ q U N := h ▸ F

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MainParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete compatible parameters for the nonuniqueness construction -/
noncomputable section
open scoped ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum

structure ConstructionParameters where
  s₀ : ℝ
  η : ℝ
  K : ℝ
  α : ℝ
  γ : ℝ
  d₀ : ℝ
  q : ℝ
  scale_pos : 0 < s₀
  scale_le : s₀ ≤ 1/8
  eta_pos : 0 < η
  eta_le : η ≤ Real.log 2
  density_pos : 0 < K
  alpha_pos : 0 < α
  alpha_le : α ≤ 1/4
  gamma_pos : 0 < γ
  width_pos : 0 < d₀
  width_le : d₀ ≤ 1
  width_small : d₀*(1/8:ℝ)^10 ≤ 1/64
  comparison_small : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1
  q_lower : 1 < q
  q_upper : q < 2
  finite_horizon : ∀ (F : ShrinkingCapFamily s₀ η K α γ d₀ q) (S : AttainedCapSequence F)
    (E : AttainedCapSequence.HotPairExtraction S), E.horizon < ⊤

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The normal-and-plane Jacobian in physical velocity coordinates -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

def physicalFrame (n : Velocity) : V → Velocity :=
  (MeasurableEquiv.toLp 2 V) ∘ frame (WithLp.ofLp n) ‖transverse n‖

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Matching the tangent columns with the manuscript's collision-plane chart -/
noncomputable section
open MeasureTheory Matrix
open scoped Matrix RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine BoltzmannNonuniqueness.TransverseAverage
namespace BoltzmannNonuniqueness.CarlemanCoordinates

def planeFrame (n : Velocity) (z s : ℝ) : Velocity := physicalFrame n ![0,z,s]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Measurable collision-plane averages and their orientation invariance -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] physicalFrame frame

def planeAverage (g : Velocity → ℝ≥0∞) (v n : Velocity) : ℝ≥0∞ :=
  ∫⁻ z : ℝ, ∫⁻ s : ℝ, g (v+planeFrame n z s)

attribute [local irreducible] planeFrame

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # A measurable radial integrand, even after integration over the sphere -/
noncomputable section
open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeAverage planeFrame physicalFrame

def radialIntegrand (f g : Velocity → ℝ≥0∞) (v : Velocity) (a : ℝ) (n : Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (‖transverse n.1‖⁻¹) *
    (ENNReal.ofReal |a| * f (v-a • n.1) * planeAverage g v n.1)

attribute [local irreducible] radialIntegrand

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The measurable Carleman profile and its radial weight -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] chart physicalFrame planeFrame

def chartProfile (g : Velocity → ℝ≥0∞) (v p : Velocity) : ℝ≥0∞ :=
  ENNReal.ofReal (‖normal v p‖⁻¹) * ∫⁻ z : ℝ, ∫⁻ s : ℝ, g (chart v p z s)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

end OAI
end


