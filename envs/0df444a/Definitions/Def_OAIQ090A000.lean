-- Prove2me | Definitions.Def_OAIQ090A000
-- name    : OAIQ090A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T19:33:08.746029+00:00
-- url     : https://prove2.me/theorems/f98704b4-ff19-464d-bbd4-005861998a19
-- title:
--   Definitions bundle OAIQ090A000 of the split of OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 780 declarations of OpenAI's Lean: 456 definitions, 19 inductive types or structures, 8 instances and 297 theorems. The definitions and types are `OAI.LipschitzHilbert.AngularBins.Bin`, `OAI.LipschitzHilbert.AngularBins.baseBin`, `OAI.LipschitzHilbert.AngularBins.binFunction`, `OAI.LipschitzHilbert.AngularBins.enlargedBin`, `OAI.LipschitzHilbert.AngularBins.radialCoordinate`, `OAI.LipschitzHilbert.AngularBins.radialMidpoint`, `OAI.LipschitzHilbert.AngularBins.radialStart`, `OAI.LipschitzHilbert.AngularBins.width`, `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.AngularGrid.analyticTransition`, `OAI.LipschitzHilbert.AngularGrid.boundaryDistance`, `OAI.LipschitzHilbert.AngularGrid.boundaryMass`, `OAI.LipschitzHilbert.AngularGrid.boundaryTops`, `OAI.LipschitzHilbert.AngularGrid.cellTops`, `OAI.LipschitzHilbert.AngularGrid.center`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.firstIneligibleShiftedBlock`, `OAI.LipschitzHilbert.AngularGrid.fixedPathResidualPackets`, `OAI.LipschitzHilbert.AngularGrid.index`, `OAI.LipschitzHilbert.AngularGrid.lastEligible`, `OAI.LipschitzHilbert.AngularGrid.left`, `OAI.LipschitzHilbert.AngularGrid.mass`, `OAI.LipschitzHilbert.AngularGrid.nearbyEligibleMass`, `OAI.LipschitzHilbert.AngularGrid.nearbyEligibleTops`, `OAI.LipschitzHilbert.AngularGrid.neighbors`, `OAI.LipschitzHilbert.AngularGrid.outsideNearTops`, `OAI.LipschitzHilbert.AngularGrid.packetAmplitude`, `OAI.LipschitzHilbert.AngularGrid.packetPathProduct`, `OAI.LipschitzHilbert.AngularGrid.packetResidual`, `OAI.LipschitzHilbert.AngularGrid.packetSet`, `OAI.LipschitzHilbert.AngularGrid.pathLogCombination`, `OAI.LipschitzHilbert.AngularGrid.pathLogSize`, `OAI.LipschitzHilbert.AngularGrid.radialBoundaryLoss`, `OAI.LipschitzHilbert.AngularGrid.radialPathLogMass`, `OAI.LipschitzHilbert.AngularGrid.shiftedPathLossTops`, `OAI.LipschitzHilbert.AngularGrid.shiftedPathMass`, `OAI.LipschitzHilbert.AngularGrid.sourceActivePathValue`, `OAI.LipschitzHilbert.AngularGrid.sourceAmplitudeRadius`, `OAI.LipschitzHilbert.AngularGrid.sourceBlockCells`, `OAI.LipschitzHilbert.AngularGrid.sourceBlockNodeRatio` and 435 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LipschitzHilbert_Estimates_ActualErrorSource`, `LipschitzHilbert_Estimates_ContinuousBMOTail`, `LipschitzHilbert_Estimates_CountableCarleson`, `LipschitzHilbert_Estimates_DyadicErrorProfile`, `LipschitzHilbert_Estimates_DyadicErrorSource`, `LipschitzHilbert_Estimates_DyadicLongScales`, `LipschitzHilbert_Estimates_DyadicSquareWeakL1`, `LipschitzHilbert_Estimates_EnvelopeDerivative`, `LipschitzHilbert_Estimates_EnvelopeSynthesis`, `LipschitzHilbert_Estimates_ErrorSourceBridge`, `LipschitzHilbert_Estimates_FiniteVariation`, `LipschitzHilbert_Estimates_IntervalOscillation`, `LipschitzHilbert_Estimates_LogEnergy`, `LipschitzHilbert_Estimates_MartingaleMaximalL2`, `LipschitzHilbert_Estimates_MultiplierError`, `LipschitzHilbert_Estimates_OrdinaryModelConstruction`, `LipschitzHilbert_Estimates_OrdinaryModelConstructionCost`, `LipschitzHilbert_Estimates_OrdinaryModelNumerics`, `LipschitzHilbert_Estimates_PlanarCoefficientNorm`, `LipschitzHilbert_Estimates_PlanarFixedScaleEnergy`, `LipschitzHilbert_Estimates_PlanarHorizontalRescale`, `LipschitzHilbert_Estimates_PlanarProfileBounds`, `LipschitzHilbert_Estimates_PlanarProfilePolarization`, `LipschitzHilbert_Estimates_PolynomialEnvelope`, `LipschitzHilbert_Estimates_PositiveErrorMajorant`, `LipschitzHilbert_Estimates_PublishedHilbertInput`, `LipschitzHilbert_Estimates_PublishedInputs`, `LipschitzHilbert_Estimates_RankedMaximal`, `LipschitzHilbert_Estimates_RestrictedStrongOperator`, `LipschitzHilbert_Estimates_ScalarRestrictedStrong`, `LipschitzHilbert_Estimates_ShearedEnvelope`, `LipschitzHilbert_Estimates_ShiftedBlocks`, `LipschitzHilbert_Estimates_SlopeBoxMask`, `LipschitzHilbert_Estimates_SnappedLattice`, `LipschitzHilbert_Estimates_SquareMaximalWeakL1`, `LipschitzHilbert_Estimates_StoppingScaleIntervals`, `LipschitzHilbert_Estimates_TopAreaAverage`, `LipschitzHilbert_Estimates_TopMaskApproximation`, `LipschitzHilbert_Estimates_TopWeight`, `LipschitzHilbert_Estimates_TopWeightIntegral`, `LipschitzHilbert_Estimates_UniformPlanarRawBounds`, `LipschitzHilbert_Estimates_VariationSum`, `LipschitzHilbert_Fourier_BandAverageComparison`, `LipschitzHilbert_Fourier_ComplexBandAverage`, `LipschitzHilbert_Fourier_ComplexLineAverage`, `LipschitzHilbert_Fourier_DyadicLineBad`, `LipschitzHilbert_Fourier_DyadicLineCount`, `LipschitzHilbert_Fourier_DyadicLineMaximal`, `LipschitzHilbert_Fourier_DyadicLineNesting`, `LipschitzHilbert_Fourier_DyadicLineRootCount`, `LipschitzHilbert_Fourier_DyadicLineRoots`, `LipschitzHilbert_Fourier_FiniteBandDerivative`, `LipschitzHilbert_Fourier_FiniteLineCells`, `LipschitzHilbert_Fourier_HilbertAnnularVariation`, `LipschitzHilbert_Fourier_PlanarCovariantJet`, `LipschitzHilbert_Fourier_PlanarModulatedJet`, `LipschitzHilbert_Fourier_PlanarSchwartzDecay`, `LipschitzHilbert_Fourier_PlanarSchwartzSlice`, `LipschitzHilbert_Fourier_PlanarSliceFourierBasic`, `LipschitzHilbert_Fourier_PlanarSliceFourierDerivative`, `LipschitzHilbert_Fourier_PositiveConvolution`, `LipschitzHilbert_Fourier_PositiveLineKernel`, `LipschitzHilbert_Fourier_PositiveLineMaximal`, `LipschitzHilbert_Fourier_SchwartzDilation`, `LipschitzHilbert_Fourier_SharpKernelComparison`, `LipschitzHilbert_Fourier_ShiftedLineAverage`, `LipschitzHilbert_Fourier_SincMask`, `LipschitzHilbert_Fourier_SincMaskMotion`, `LipschitzHilbert_Fourier_SincMaskSchwartz`, `LipschitzHilbert_Fourier_SincMaskedLine`, `LipschitzHilbert_Fourier_SkippedLineAverage`, `LipschitzHilbert_Fourier_SquareLineConcentration`, `LipschitzHilbert_Fourier_TileEnvelopeKernel`, `LipschitzHilbert_Fourier_VerticalErrorSources`, `LipschitzHilbert_Geometry_LocalMinimaSelection`, `LipschitzHilbert_Geometry_PacketDataFarGram`, `LipschitzHilbert_Geometry_PacketDataSignedInteractionPacking`, `LipschitzHilbert_Geometry_PacketDataSizeSelectionEnergy`, `LipschitzHilbert_Geometry_SourceTransverseTail`, `LipschitzHilbert_Packets_AnalyzedLineFamily`, `LipschitzHilbert_Packets_AnalyzingCoefficientNorm`, `LipschitzHilbert_Packets_AnalyzingCoefficients`, `LipschitzHilbert_Packets_LinePacketFamily`, `LipschitzHilbert_Packets_LinePacketReplacement`, `LipschitzHilbert_Packets_PacketBoxes`, `LipschitzHilbert_Packets_PacketConvolution`, `LipschitzHilbert_Packets_PacketDataActualReferenceEvents`, `LipschitzHilbert_Packets_PacketDataAdjoint`, `LipschitzHilbert_Packets_PacketDataAssignedParentMarkedBound`, `LipschitzHilbert_Packets_PacketDataAssignedPathIntegral`, `LipschitzHilbert_Packets_PacketDataAssignedPhysical`, `LipschitzHilbert_Packets_PacketDataAssignedReference`, `LipschitzHilbert_Packets_PacketDataAssignedTopAlternate`, `LipschitzHilbert_Packets_PacketDataAssignedTopFamily`, `LipschitzHilbert_Packets_PacketDataAssignedTopSelector`, `LipschitzHilbert_Packets_PacketDataCoefficient`, `LipschitzHilbert_Packets_PacketDataCrossValue`, `LipschitzHilbert_Packets_PacketDataDensity`, `LipschitzHilbert_Packets_PacketDataDensityForest`, `LipschitzHilbert_Packets_PacketDataDropPackets`, `LipschitzHilbert_Packets_PacketDataDropTreeTransport`, `LipschitzHilbert_Packets_PacketDataInteractionGeometry`, `LipschitzHilbert_Packets_PacketDataJetControl`, `LipschitzHilbert_Packets_PacketDataMaskedValue`, `LipschitzHilbert_Packets_PacketDataModelConfig`, `LipschitzHilbert_Packets_PacketDataModelCostPolynomial`, `LipschitzHilbert_Packets_PacketDataModelRestriction`, `LipschitzHilbert_Packets_PacketDataOrdinaryDensityForest`, `LipschitzHilbert_Packets_PacketDataOriginalParentMarkedPath`, `LipschitzHilbert_Packets_PacketDataParentReference`, `LipschitzHilbert_Packets_PacketDataPartial`, `LipschitzHilbert_Packets_PacketDataPolarization`, `LipschitzHilbert_Packets_PacketDataReferenceConditions`, `LipschitzHilbert_Packets_PacketDataReverseCost`, `LipschitzHilbert_Packets_PacketDataScaleRestriction`, `LipschitzHilbert_Packets_PacketDataSelectedBoxSeparation`, `LipschitzHilbert_Packets_PacketDataSelectedConstants`, `LipschitzHilbert_Packets_PacketDataSelectedDuality`, `LipschitzHilbert_Packets_PacketDataSelectedGram`, `LipschitzHilbert_Packets_PacketDataSelectedPrefix`, `LipschitzHilbert_Packets_PacketDataSelectedReference`, `LipschitzHilbert_Packets_PacketDataSelectedSum`, `LipschitzHilbert_Packets_PacketDataSignedSizeTest`, `LipschitzHilbert_Packets_PacketDataSizeStopping`, `LipschitzHilbert_Packets_PacketDataUniformCappedStep`, `LipschitzHilbert_Packets_PacketDataUniformReverseModel`, `LipschitzHilbert_Packets_PacketDataUniversalEstimate`, `LipschitzHilbert_Packets_PacketDataVectorEnvelope`, `LipschitzHilbert_Packets_PacketLatticeData`, `LipschitzHilbert_Packets_PacketLatticeRestriction`, `LipschitzHilbert_Packets_PacketReferenceSpectrum`, `LipschitzHilbert_Packets_PacketVectorDerivative`, `LipschitzHilbert_Packets_PhysicalPlanarPacket`, `LipschitzHilbert_Packets_PlanarPacketDerivative`, `LipschitzHilbert_Packets_PlanarPacketDifferentiation`, `LipschitzHilbert_Packets_PlanarPacketEnvelope`, `LipschitzHilbert_Packets_PlanarPacketFamily`, `LipschitzHilbert_Packets_PositivePacketSquare`, `LipschitzHilbert_Packets_ScaledPlanarPacket`, `LipschitzHilbert_Packets_ShortPacketBoxes`, `LipschitzHilbert_Packets_SourceFrozenProfile`, `LipschitzHilbert_Packets_SourceFrozenWhitneyLocal`, `LipschitzHilbert_Packets_SourceLabeledPacketRestriction`, `LipschitzHilbert_Packets_SourceLatticePacket`, `LipschitzHilbert_Packets_SourcePacketRegroup`, `LipschitzHilbert_Packets_VariationPacketL1`, `LipschitzHilbert_Phase_AngularAmplitudeIdentity`, `LipschitzHilbert_Phase_AngularAnalyticWeight`, `LipschitzHilbert_Phase_AngularBinOverlap`, `LipschitzHilbert_Phase_AngularBins`, `LipschitzHilbert_Phase_AngularBoundary`, `LipschitzHilbert_Phase_AngularCommonTranslation`, `LipschitzHilbert_Phase_AngularErrorConvolution`, `LipschitzHilbert_Phase_AngularGeometry`, `LipschitzHilbert_Phase_AngularGrid`, `LipschitzHilbert_Phase_AngularPacketAmplitude`, `LipschitzHilbert_Phase_AngularSourceAmplitude`, `LipschitzHilbert_Phase_AngularSourceWeight`, `LipschitzHilbert_Phase_AngularStopping`, `LipschitzHilbert_Phase_AngularTranslationMeasurable`, `LipschitzHilbert_Phase_PacketAngularModel`, `LipschitzHilbert_Phase_PlanarSliceFourierAngular`, `LipschitzHilbert_Phase_SourceAmplitudeInterpolation`, `LipschitzHilbert_Phase_SourceAngularGridRebase`, `LipschitzHilbert_Phase_SourceAngularScales`, `LipschitzHilbert_Phase_SourceLabeledAngularErrorData`, `LipschitzHilbert_Phase_SourceMarkedPrediction`, `LipschitzHilbert_Phase_SourcePathPrediction`, `LipschitzHilbert_Phase_SourcePredictionValues`, `LipschitzHilbert_Trees_DyadicLineGrid`, `LipschitzHilbert_Trees_FiniteLineGrid`, `LipschitzHilbert_Trees_LineGridBMO`, `LipschitzHilbert_Trees_LineGridLimit`, `LipschitzHilbert_Trees_LineGridMartingale`, `LipschitzHilbert_Trees_ResidualOscillation`, `LipschitzHilbert_Trees_SourceAllDyadicMaximal`, `LipschitzHilbert_Trees_SourceAllStrongMaximal`, `LipschitzHilbert_Trees_SourceAmplitudeExhaustion`, `LipschitzHilbert_Trees_SourceAmplitudeExponential`, `LipschitzHilbert_Trees_SourceAmplitudeIntegral`, `LipschitzHilbert_Trees_SourceAssignedMaskSums`, `LipschitzHilbert_Trees_SourceAssignedTopFamily`, `LipschitzHilbert_Trees_SourceAxisMaximal`, `LipschitzHilbert_Trees_SourceBlockChildren`, `LipschitzHilbert_Trees_SourceBlockLineGrid`, `LipschitzHilbert_Trees_SourceBoundaryDeficit`, `LipschitzHilbert_Trees_SourceBoundaryGeometry`, `LipschitzHilbert_Trees_SourceBoundaryScales`, `LipschitzHilbert_Trees_SourceCellMarking`, `LipschitzHilbert_Trees_SourceDensityKeepers`, `LipschitzHilbert_Trees_SourceDensityModel`, `LipschitzHilbert_Trees_SourceDensityRadius`, `LipschitzHilbert_Trees_SourceDensityRebase`, `LipschitzHilbert_Trees_SourceDensityScaledForest`, `LipschitzHilbert_Trees_SourceDensityTail`, `LipschitzHilbert_Trees_SourceErrorSupported`, `LipschitzHilbert_Trees_SourceErrorTail`, `LipschitzHilbert_Trees_SourceGlobalDyadicMaximal`, `LipschitzHilbert_Trees_SourceInhabitedLabels`, `LipschitzHilbert_Trees_SourceLabeledActiveReference`, `LipschitzHilbert_Trees_SourceLabeledCoefficientSplit`, `LipschitzHilbert_Trees_SourceLabeledErrorFamily`, `LipschitzHilbert_Trees_SourceLabeledGoodEvents`, `LipschitzHilbert_Trees_SourceLabeledGoodQuantities`, `LipschitzHilbert_Trees_SourceLabeledMainTail`, `LipschitzHilbert_Trees_SourceLabeledPositiveSplit`, `LipschitzHilbert_Trees_SourceLabeledRawEnvelope`, `LipschitzHilbert_Trees_SourceLabeledSynthesisEnvelope`, `LipschitzHilbert_Trees_SourceLabeledVariationSplit`, `LipschitzHilbert_Trees_SourceLatticePolarization`, `LipschitzHilbert_Trees_SourceLatticePolarizationSpectrum`, `LipschitzHilbert_Trees_SourceLineGrid`, `LipschitzHilbert_Trees_SourceLineMaximal`, `LipschitzHilbert_Trees_SourceLineWindow`, `LipschitzHilbert_Trees_SourceLongCellMask`, `LipschitzHilbert_Trees_SourceMarkedIntegral`, `LipschitzHilbert_Trees_SourceMassStopping`, `LipschitzHilbert_Trees_SourceMixedReference`, `LipschitzHilbert_Trees_SourceMonotoneMaximal`, `LipschitzHilbert_Trees_SourceNodeMeasurable`, `LipschitzHilbert_Trees_SourceNodeRatio`, `LipschitzHilbert_Trees_SourceParameters`, `LipschitzHilbert_Trees_SourcePathIntegrand`, `LipschitzHilbert_Trees_SourcePhysicalGoodPath`, `LipschitzHilbert_Trees_SourcePlanarSynthesis`, `LipschitzHilbert_Trees_SourceRadialLoss`, `LipschitzHilbert_Trees_SourceRadialMassBounds`, `LipschitzHilbert_Trees_SourceReferenceMoments`, `LipschitzHilbert_Trees_SourceReferenceRestriction`, `LipschitzHilbert_Trees_SourceReferenceUnion`, `LipschitzHilbert_Trees_SourceResidualEnvelopes`, `LipschitzHilbert_Trees_SourceResidualPropagation`, `LipschitzHilbert_Trees_SourceReverseBlocks`, `LipschitzHilbert_Trees_SourceReverseWeights`, `LipschitzHilbert_Trees_SourceRootCells`, `LipschitzHilbert_Trees_SourceSelectedReferenceData`, `LipschitzHilbert_Trees_SourceSharedGoodPath`, `LipschitzHilbert_Trees_SourceShiftedCellMotion`, `LipschitzHilbert_Trees_SourceShiftedDrop`, `LipschitzHilbert_Trees_SourceSlopeLabels`, `LipschitzHilbert_Trees_SourceSlottedCoefficient`, `LipschitzHilbert_Trees_SourceSlottedLattice`, `LipschitzHilbert_Trees_SourceSnapshotWindow`, `LipschitzHilbert_Trees_SourceStoppedAmplitude`, `LipschitzHilbert_Trees_SourceTerminalScale`, `LipschitzHilbert_Trees_SourceThreeGridMaximal`, `LipschitzHilbert_Trees_SourceThreeGridPlane`, `LipschitzHilbert_Trees_SourceThresholdSum`, `LipschitzHilbert_Trees_SourceTreeConservation`, `LipschitzHilbert_Trees_SourceTreeExpansion`, `LipschitzHilbert_Trees_SourceTreeSpectrum`, `LipschitzHilbert_Trees_SourceVectorSchwartz`, `LipschitzHilbert_Trees_SourceWeightedTreeMaximal`, `LipschitzHilbert_Trees_SourceWhitneyGluing`, `LipschitzHilbert_Trees_SourceWhitneyIntervals`, `LipschitzHilbert_Trees_VertexIntegration`.
--
--   **Imports.** It imports the published bundle `Def_LipschitzHilbert`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ090A002`; the statements `OAI.LipschitzHilbert.AngularGrid.eventually_source_block_path_motion`, `OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_marked_path_bound`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_vertex_integral`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_original_parent_marked_path_bound`, `OAI.LipschitzHilbert.PacketLatticeData.eventually_physical_parent_full_residual_square`, `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_high_pairing`, `OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing`, `OAI.LipschitzHilbert.PacketLatticeData.exists_tree_far_gram_bound`, `OAI.LipschitzHilbert.PacketLatticeData.exists_universal_ordinary_model_estimate`, `OAI.LipschitzHilbert.PacketLatticeData.source_assigned_selector_mask_good_set`, `OAI.LipschitzHilbert.PacketLatticeData.source_density_popular_recovery`, `OAI.LipschitzHilbert.PacketRepresentation.comparableCommutatorSum_energy`, `OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding`, `OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported`, `OAI.LipschitzHilbert.SourceLabeledLattice.eventually_physical_reference_good_spectral_tail`, `OAI.LipschitzHilbert.eventually_source_grid_parameters`, `OAI.LipschitzHilbert.eventually_source_simultaneous_count_universal`, `OAI.LipschitzHilbert.laceyLiInput_proved`, `OAI.LipschitzHilbert.main_of_three_published_inputs` and `OAI.LipschitzHilbert.uniform_truncation_of_two_published_inputs`; the proof of `OAI.LipschitzHilbert.PacketRepresentation.dyadic_smooth_product_embedding`.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_LipschitzHilbert

section
-- module Solutions.OAIQ090_LH.Compat
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
/-- Mathlib d13f23b's `Complex.hasTemperateGrowth_exp_mul_I`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem hasTemperateGrowth_exp_mul_I : (fun x : ℝ => Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
      = fun x : ℝ => Complex.I ^ n * Complex.exp (Complex.I * (x:ℂ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)))
          (Complex.exp (Complex.I * (x:ℂ)) * Complex.I) x := by
        have := ((hasDerivAt_id x).ofReal_comp.const_mul Complex.I).cexp
        simpa using this
      have h2 := h1.const_mul (Complex.I ^ n)
      rw [h2.deriv]
      ring
  refine ⟨?_, fun n => ⟨0, 1, fun x => ?_⟩⟩
  · exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  · have h : (fun x : ℝ => Complex.exp (x * Complex.I)) = fun x : ℝ => Complex.exp (Complex.I * (x:ℂ)) := by
      funext x; rw [mul_comm]
    rw [h, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit]
    simp [norm_pow, Complex.norm_exp]
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
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicLongScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal lengths of the scales longer than an interval form a
geometric sum controlled by that interval's reciprocal length. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem sum_two_powers (N : ℕ) :
    (∑ j ∈ Finset.range N, (2 : ℝ) ^ j) = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem sum_long_dyadic_reciprocals (N : ℕ) (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    (∑ j : Fin N, if r < L / (2 : ℝ) ^ j.val then
      (L / (2 : ℝ) ^ j.val)⁻¹ else 0) ≤ 2 / r := by
  classical
  change (∑ j : Fin N, (fun n : ℕ => if r < L / (2 : ℝ) ^ n then
    (L / (2 : ℝ) ^ n)⁻¹ else 0) j.val) ≤ 2 / r
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => if r < L / (2 : ℝ) ^ n then
    (L / (2 : ℝ) ^ n)⁻¹ else 0) N, ← Finset.sum_filter]
  let s := (Finset.range N).filter (fun j => r < L / (2 : ℝ) ^ j)
  change (∑ j ∈ s, (L / (2 : ℝ) ^ j)⁻¹) ≤ 2 / r
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := s.max'_mem hs
    have hsub : s ⊆ Finset.range (m + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (s.le_max' j hj))
    have hbound : r * (2 : ℝ) ^ m < L :=
      (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) m)).mp (Finset.mem_filter.mp hm).2
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), (L / (2 : ℝ) ^ j)⁻¹ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
      _ = ((2 : ℝ) ^ (m + 1) - 1) / L := by
        simp only [inv_div, ← Finset.sum_div, sum_two_powers]
      _ ≤ 2 / r := by
        apply (div_le_div_iff₀ hL hr).mpr
        rw [pow_succ]
        nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty, Finset.sum_empty]
    positivity

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicErrorProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded overlap of the dyadic annulus part of the error source. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem dyadic_band_card (N K : ℕ) (a v : ℝ) (ha : 0 < a) :
    (Finset.univ.filter (fun j : Fin N => a * (2 : ℝ)^j.val ≤ v ∧
      v ≤ (2 : ℝ)^K * (a * (2 : ℝ)^j.val))).card ≤ K+1 := by
  let s := Finset.univ.filter (fun j : Fin N => a * (2 : ℝ)^j.val ≤ v ∧
    v ≤ (2 : ℝ)^K * (a * (2 : ℝ)^j.val))
  change s.card ≤ K+1
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := s.min'_mem hs
    have hmin (j : Fin N) (hj : j ∈ s) : m.val ≤ j.val := s.min'_le j hj
    have hmax (j : Fin N) (hj : j ∈ s) : j.val ≤ m.val+K := by
      have hm' := (Finset.mem_filter.mp hm).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hmul : a*(2 : ℝ)^j.val ≤ a*(2 : ℝ)^(m.val+K) := by
        calc
          _ ≤ v := hj'.1
          _ ≤ (2 : ℝ)^K * (a*(2 : ℝ)^m.val) := hm'.2
          _ = _ := by rw [pow_add]; ring
      have hp : (2 : ℝ)^j.val ≤ (2 : ℝ)^(m.val+K) :=
        (mul_le_mul_iff_right₀ ha).mp (by nlinarith [hmul])
      exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hp
    have hcard := Finset.card_le_card_of_injOn (s := s) (t := Finset.range (K+1))
      (fun j : Fin N => j.val-m.val)
      (fun j hj => Finset.mem_range.mpr (by
        change j.val-m.val < K+1
        have := hmin j hj
        have := hmax j hj
        omega))
      (by
        intro j hj k hk heq
        change j.val-m.val = k.val-m.val at heq
        apply Fin.ext
        have := hmin j hj
        have := hmin k hk
        omega)
    simpa only [Finset.card_range] using hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    omega

theorem increasing_dyadic_reverse (N : ℕ) (a : ℝ) (j : Fin N) :
    a * (2 : ℝ)^j.val = (a*(2 : ℝ)^(N-1)) / (2 : ℝ)^(j.rev.val) := by
  have he : N-1 = j.val+j.rev.val := by simp only [Fin.val_rev]; omega
  rw [he, pow_add]
  field_simp

theorem sum_large_increasing_dyadic_reciprocals (N : ℕ) (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∑ j : Fin N, if r < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0) ≤ 2/r := by
  have h := sum_long_dyadic_reciprocals N (a*(2 : ℝ)^(N-1)) r (by positivity) hr
  have hs := Equiv.sum_comp (Fin.revPerm (n := N)) (fun j : Fin N =>
    if r < (a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.val then
      ((a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.val)⁻¹ else 0)
  change (∑ j : Fin N, if r < (a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.rev.val then
    ((a*(2 : ℝ)^(N-1))/(2 : ℝ)^j.rev.val)⁻¹ else 0) = _ at hs
  simp_rw [← increasing_dyadic_reverse N a] at hs
  rw [hs]
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicErrorSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise source and source-sum estimates for the manuscript's
annular indicator plus small-angle error profile. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem sum_dyadic_small_ratio (N : ℕ) (a c v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) :
    (∑ j : Fin N, if v ≤ c*(a*(2 : ℝ)^j.val) then v/(a*(2 : ℝ)^j.val) else 0) ≤ 4*c := by
  by_cases hv0 : v = 0
  · simp only [hv0, zero_div, ite_self, Finset.sum_const_zero]
    positivity
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hr : 0 < v/(2*c) := div_pos hvp (by positivity)
  have hpoint (j : Fin N) :
      (if v ≤ c*(a*(2 : ℝ)^j.val) then v/(a*(2 : ℝ)^j.val) else 0) ≤
        v * (if v/(2*c) < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0) := by
    have hd : 0 < a*(2 : ℝ)^j.val := by positivity
    by_cases hj : v ≤ c*(a*(2 : ℝ)^j.val)
    · have hlt : v/(2*c) < a*(2 : ℝ)^j.val := by
        apply (div_lt_iff₀ (by positivity : 0 < 2*c)).mpr
        nlinarith
      rw [ite_eq_left hj, ite_eq_left hlt, div_eq_mul_inv]
    · simp only [ite_eq_right hj]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ j : Fin N, v * (if v/(2*c) < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = v * ∑ j : Fin N, if v/(2*c) < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ v * (2/(v/(2*c))) :=
      mul_le_mul_of_nonneg_left (sum_large_increasing_dyadic_reciprocals N a (v/(2*c)) ha hr) hv
    _ = 4*c := by field_simp; norm_num

def dyadicErrorSource (c : ℝ) (K : ℕ) (d v : ℝ) : ℝ :=
  (if c*d ≤ v ∧ v ≤ (2 : ℝ)^K * (c*d) then 1 else 0) +
    (if v ≤ c*d then v/d else 0)

theorem sum_dyadicErrorSource (N K : ℕ) (a c v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) :
    (∑ j : Fin N, dyadicErrorSource c K (a*(2 : ℝ)^j.val) v) ≤ (K+1 : ℕ) + 4*c := by
  have heq (j : Fin N) : c*(a*(2 : ℝ)^j.val) = (c*a)*(2 : ℝ)^j.val := by ring
  have hcount : (∑ j : Fin N, if c*(a*(2 : ℝ)^j.val) ≤ v ∧
      v ≤ (2 : ℝ)^K * (c*(a*(2 : ℝ)^j.val)) then (1 : ℝ) else 0) ≤ (K+1 : ℕ) := by
    simp_rw [heq]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast dyadic_band_card N K (c*a) v (mul_pos hc ha)
  have htail := sum_dyadic_small_ratio N a c v ha hc hv
  simp only [dyadicErrorSource, Finset.sum_add_distrib]
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ActualErrorSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's annular error indicator and small-angle ratio,
including its logarithmic dyadic-branching source-sum bound. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def errorSourceProfile (c R d v : ℝ) : ℝ :=
  (if c*d ≤ v ∧ v ≤ R*d then 1 else 0) + (if v ≤ c*d then v/d else 0)

theorem errorSourceProfile_measurable {X : Type*} [MeasurableSpace X]
    {v : X → ℝ} (hv : Measurable v) (c R d : ℝ) :
    Measurable (fun x => errorSourceProfile c R d (v x)) := by
  have hA : MeasurableSet {x | c*d ≤ v x ∧ v x ≤ R*d} :=
    (measurableSet_le measurable_const hv).inter (measurableSet_le hv measurable_const)
  have hB : MeasurableSet {x | v x ≤ c*d} := measurableSet_le hv measurable_const
  exact (Measurable.ite hA measurable_const measurable_const).add
    (Measurable.ite hB (hv.div_const d) measurable_const)

theorem errorSourceProfile_le_dyadic (c R d v : ℝ) (K : ℕ)
    (hd : 0 ≤ d) (hR : R ≤ c*(2 : ℝ)^K) :
    errorSourceProfile c R d v ≤ dyadicErrorSource c K d v := by
  apply add_le_add _ le_rfl
  by_cases h : c*d ≤ v ∧ v ≤ R*d
  · have h' : c*d ≤ v ∧ v ≤ (2 : ℝ)^K*(c*d) := by
      refine ⟨h.1, h.2.trans ?_⟩
      have he := mul_le_mul_of_nonneg_right hR hd
      nlinarith [he]
    simp only [ite_eq_left h, ite_eq_left h', le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

theorem errorSourceProfile_nonneg (c R d v : ℝ) (hd : 0 < d) (hv : 0 ≤ v) :
    0 ≤ errorSourceProfile c R d v := by
  unfold errorSourceProfile
  split_ifs <;> positivity

theorem errorSourceProfile_bound (c R d v : ℝ) (hc : 0 < c) (hd : 0 < d) (_hv : 0 ≤ v) :
    errorSourceProfile c R d v ≤ 1+c := by
  have hfirst : (if c*d ≤ v ∧ v ≤ R*d then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have htail : (if v ≤ c*d then v/d else 0) ≤ c := by
    split_ifs with h
    · exact (div_le_iff₀ hd).mpr h
    · exact hc.le
  exact add_le_add hfirst htail

theorem sum_errorSourceProfile (N K : ℕ) (a c R v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) (hR : R ≤ c*(2 : ℝ)^K) :
    (∑ j : Fin N, errorSourceProfile c R (a*(2 : ℝ)^j.val) v) ≤ (K+1 : ℕ)+4*c := by
  exact (Finset.sum_le_sum (fun j _ => errorSourceProfile_le_dyadic c R _ v K (by positivity) hR)).trans
    (sum_dyadicErrorSource N K a c v ha hc hv)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FiniteLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite line partitions, nested at an integer branching ratio. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

structure FiniteLineGrid where
  branching : ℕ
  branching_pos : 0 < branching
  origin : ℝ
  width : ℝ
  width_pos : 0 < width
  depth : ℕ

namespace FiniteLineGrid

attribute [local instance] Classical.propDecidable

def root (g : FiniteLineGrid) : Set ℝ := Ico g.origin (g.origin + g.width)

def rawIndex (g : FiniteLineGrid) (level : ℕ) (x : ℝ) : ℕ :=
  if x ∈ g.root then ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ else 0

theorem rawIndex_lt (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth) (x : ℝ) :
    g.rawIndex level x < g.branching ^ g.depth := by
  classical
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  by_cases hx : x ∈ g.root
  · have hzero : 0 ≤ (x - g.origin) / g.width :=
      div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le
    have hone : (x - g.origin) / g.width < 1 := by
      rw [div_lt_one g.width_pos]
      exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using hx.2)
    have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
    have hlt : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ <
        g.branching ^ level := by
      rw [Nat.floor_lt (mul_nonneg hzero hp.le), Nat.cast_pow]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hone hp
    rw [rawIndex, ite_eq_left hx]
    exact hlt.trans_le (Nat.pow_le_pow_right g.branching_pos hlevel)
  · simpa only [rawIndex, ite_eq_right hx] using pow_pos g.branching_pos g.depth

def index (g : FiniteLineGrid) (level : ℕ) (x : ℝ) : Fin (g.branching ^ g.depth) :=
  ⟨g.rawIndex (min level g.depth) x, g.rawIndex_lt (Nat.min_le_right _ _) x⟩

def parent (g : FiniteLineGrid) (i : Fin (g.branching ^ g.depth)) :
    Fin (g.branching ^ g.depth) :=
  ⟨i.val / g.branching, (Nat.div_le_self _ _).trans_lt i.isLt⟩

theorem rawIndex_parent (g : FiniteLineGrid) (level : ℕ) (x : ℝ) :
    g.rawIndex (level + 1) x / g.branching = g.rawIndex level x := by
  classical
  by_cases hx : x ∈ g.root
  · simp only [rawIndex, ite_eq_left hx]
    rw [← Nat.floor_div_natCast]
    congr 1
    rw [pow_succ]
    have hG : (g.branching : ℝ) ≠ 0 := by exact_mod_cast g.branching_pos.ne'
    field_simp
  · simp [rawIndex, hx]

/-- The partitions refine on the entire line, including outside the root. -/
theorem index_parent (g : FiniteLineGrid) {level : ℕ} (hlevel : level < g.depth) (x : ℝ) :
    g.index level x = g.parent (g.index (level + 1) x) := by
  apply Fin.ext
  change g.rawIndex (min level g.depth) x =
    g.rawIndex (min (level + 1) g.depth) x / g.branching
  rw [Nat.min_eq_left hlevel.le, Nat.min_eq_left (Nat.succ_le_of_lt hlevel)]
  exact (g.rawIndex_parent level x).symm

theorem measurable_rawIndex (g : FiniteLineGrid) (level : ℕ) : Measurable (g.rawIndex level) := by
  have h : Measurable (fun x : ℝ =>
      ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊) := by fun_prop
  exact Measurable.ite (show MeasurableSet g.root from measurableSet_Ico) h measurable_const

theorem measurable_index_fiber (g : FiniteLineGrid) (level : ℕ)
    (i : Fin (g.branching ^ g.depth)) : MeasurableSet {x | g.index level x = i} := by
  have heq : {x | g.index level x = i} =
      {x | g.rawIndex (min level g.depth) x = i.val} := by
    ext x
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  rw [heq]
  exact (g.measurable_rawIndex _) (measurableSet_singleton _)

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteLineCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact intervals underlying the finite line-mesh index maps. -/

noncomputable section

open Set

namespace LipschitzHilbert.FiniteLineGrid

def meshWidth (g : FiniteLineGrid) (level : ℕ) : ℝ :=
  g.width / (g.branching : ℝ) ^ level

def cell (g : FiniteLineGrid) (level i : ℕ) : Set ℝ :=
  Ico (g.origin + g.meshWidth level * i) (g.origin + g.meshWidth level * (i + 1))

theorem meshWidth_pos (g : FiniteLineGrid) (level : ℕ) : 0 < g.meshWidth level :=
  div_pos g.width_pos (pow_pos (by exact_mod_cast g.branching_pos) _)

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The martingale of actual nested line-cell averages. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem measurable_index (g : FiniteLineGrid) (n : ℕ) : Measurable (g.index n) :=
  measurable_to_countable' (g.measurable_index_fiber n)

def nextParent (g : FiniteLineGrid) (n : ℕ)
    (i : Fin (g.branching ^ g.depth)) : Fin (g.branching ^ g.depth) :=
  if n < g.depth then g.parent i else i

theorem index_nextParent (g : FiniteLineGrid) (n : ℕ) :
    g.index n = g.nextParent n ∘ g.index (n + 1) := by
  funext x
  by_cases hn : n < g.depth
  · simpa only [nextParent, ite_eq_left hn, Function.comp_apply] using g.index_parent hn x
  · have hdn : g.depth ≤ n := le_of_not_gt hn
    simp only [nextParent, ite_eq_right hn, Function.comp_apply, index,
      Nat.min_eq_right hdn, Nat.min_eq_right (hdn.trans (Nat.le_succ n))]

/-- At level `n`, the sigma algebra consists precisely of unions of
the concrete mesh-index fibers. The grid is frozen after its final depth. -/
def filtration (g : FiniteLineGrid) : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq n := MeasurableSpace.comap (g.index n) inferInstance
  mono' := monotone_nat_of_le_succ fun n => by
    rw [g.index_nextParent n, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_countable (g.nextParent n)).comap_le
  le' n := (g.measurable_index n).comap_le

def average (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  μ[f | g.filtration n]

def lineMeasure (g : FiniteLineGrid) : Measure ℝ := volume.restrict g.root

instance lineMeasure_finite (g : FiniteLineGrid) : IsFiniteMeasure g.lineMeasure := ⟨by
  change (volume.restrict g.root) Set.univ < ∞
  rw [Measure.restrict_apply_univ, root, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top⟩

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean oscillation on the actual line cells controls every martingale
jump by the branching factor. This supplies the overshoot bound in the
dyadic stopping proof of John--Nirenberg. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

def cellMean (g : FiniteLineGrid) (f : ℝ → ℝ) (level i : ℕ) : ℝ :=
  (g.meshWidth level)⁻¹ * ∫ x in g.cell level i, f x

def HasMeanOscillationBound (g : FiniteLineGrid) (f : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ level i, level ≤ g.depth → i < g.branching ^ level →
    (∫ x in g.cell level i, |f x - g.cellMean f level i|) ≤ A * g.meshWidth level

instance cellMeasure_finite (g : FiniteLineGrid) (level i : ℕ) :
    IsFiniteMeasure (volume.restrict (g.cell level i)) := ⟨by
  rw [Measure.restrict_apply_univ, cell, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top⟩

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cell averages converge at every continuity point in the root.
Only this continuous-function specialization of differentiation is needed
for the finite smooth packet and variation functions. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

def withDepth (g : FiniteLineGrid) (N : ℕ) : FiniteLineGrid := {g with depth := N}

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! John--Nirenberg's geometric distribution bound for a continuous
function on an actual finite interval. The proof passes the uniform finite
grid estimate to the function, using pointwise convergence of cell means. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

def HasFullMeanOscillationBound (g : FiniteLineGrid) (f : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ n i, i < g.branching ^ n →
    (∫ x in g.cell n i, |f x - g.cellMean f n i|) ≤ A * g.meshWidth n

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountableCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable exhaustion of the Carleson tail

The count is an actual ENNReal sum over occurrences. Every finite subset
has the same exponential tail bound, so continuity from below gives that
bound for the full count without requiring a choice of enumeration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

attribute [local instance] Classical.propDecidable

def occurrenceCount (Q : ι → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i, (Q i).indicator (1 : X → ℝ≥0∞) x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- A top box in the manuscript's slope coordinates. -/
structure SlopeBox where
  x : ℝ
  y : ℝ
  slope : ℝ
  length : ℝ
  width : ℝ
  length_pos : 0 < length
  width_pos : 0 < width

namespace SlopeBox

def horizontal (T : SlopeBox) (z : ℝ × ℝ) : ℝ := (z.1 - T.x) / T.length

def transverse (T : SlopeBox) (z : ℝ × ℝ) : ℝ :=
  ((z.2 - T.y) - T.slope * (z.1 - T.x)) / T.width

def radius (T : SlopeBox) (z : ℝ × ℝ) : ℝ := |T.horizontal z| + |T.transverse z|

def weight (T : SlopeBox) (K D : ℝ) (z : ℝ × ℝ) : ℝ :=
  (2 : ℝ) ^ D * (1 + T.radius z / K) ^ (-D)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- A single common translation is used at every angular level. -/
structure AngularGrid where
  branching : ℕ
  branching_ge_two : 2 ≤ branching
  origin : ℝ
  rootWidth : ℝ
  rootWidth_pos : 0 < rootWidth

namespace AngularGrid

def index (g : AngularGrid) (level : ℕ) (slope : ℝ) : ℤ :=
  ⌊((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level⌋

def eligible (g : AngularGrid) (cutoff precision : ℝ) (level : ℕ) : Prop :=
  precision * (g.branching : ℝ) ^ level ≤ cutoff

theorem eligible_parent (g : AngularGrid) {cutoff precision : ℝ} (hp : 0 ≤ precision)
    (level : ℕ) (h : g.eligible cutoff precision (level + 1)) :
    g.eligible cutoff precision level := by
  have hG : (1 : ℝ) ≤ g.branching := by
    exact_mod_cast (show 1 ≤ g.branching by have h := g.branching_ge_two; omega)
  unfold eligible at h ⊢
  calc
    precision * (g.branching : ℝ) ^ level ≤
        (precision * (g.branching : ℝ) ^ level) * g.branching :=
      le_mul_of_one_le_right (by positivity) hG
    _ = precision * (g.branching : ℝ) ^ (level + 1) := by rw [pow_succ]; ring
    _ ≤ cutoff := h

variable {ι X : Type*}

/-- The tops in an actual translated angular cell, with the scale cutoff
included in membership rather than imposed after assigning the cell. -/
def cellTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (level : ℕ) (cell : ℤ) : Finset ι := by
  classical
  exact tops.filter fun i => g.index level (slope i) = cell ∧ g.eligible cutoff (precision i) level

@[simp] theorem mem_cellTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (level : ℕ) (cell : ℤ) (i : ι) :
    i ∈ g.cellTops tops slope precision cutoff level cell ↔
      i ∈ tops ∧ g.index level (slope i) = cell ∧ g.eligible cutoff (precision i) level := by
  classical
  simp [cellTops]

def mass (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (level : ℕ) (cell : ℤ) (x : X) : ℝ :=
  ∑ i ∈ g.cellTops tops slope precision cutoff level cell, weight i x

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric separation in the actual translated angular grid. -/

noncomputable section

namespace LipschitzHilbert.AngularGrid

def width (g : AngularGrid) (level : ℕ) : ℝ := g.rootWidth / (g.branching : ℝ) ^ level

def left (g : AngularGrid) (level : ℕ) (cell : ℤ) : ℝ :=
  g.origin + g.width level * cell

def center (g : AngularGrid) (level : ℕ) (cell : ℤ) : ℝ :=
  g.left level cell + g.width level / 2

theorem width_pos (g : AngularGrid) (level : ℕ) : 0 < g.width level := by
  have hG : (0 : ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have h := g.branching_ge_two; omega)
  exact div_pos g.rootWidth_pos (pow_pos hG level)

def neighbors (g : AngularGrid) (level : ℕ) (gap : ℝ) (i j : ℤ) : Prop :=
  |g.center level i - g.center level j| < gap + g.width level

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

def scale (k : ℤ) : ℝ := (2 : ℝ) ^ k

def shift (q k : ℤ) : ℝ := ((k.negOnePow : ℤ) * q : ℤ) / (3 : ℝ)

def left (q k j : ℤ) : ℝ := scale k * (j + shift q k)

def cell (q k j : ℤ) : Set ℝ := Ico (left q k j) (left q k (j + 1))

def parent (q k j : ℤ) : ℤ := (j + (k.negOnePow : ℤ) * q) / 2

def index (q k : ℤ) (x : ℝ) : ℤ := ⌊x / scale k - shift q k⌋

theorem scale_pos (k : ℤ) : 0 < scale k := zpow_pos (by norm_num) k

theorem scale_succ (k : ℤ) : scale (k + 1) = 2 * scale k := by
  simp only [scale, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

theorem shift_succ (q k : ℤ) : shift q (k + 1) = -shift q k := by
  simp only [shift, Int.negOnePow_succ, Units.val_neg, Int.cast_neg, Int.cast_mul]
  ring

/-- Every point has the usual unique half-open floor cell. -/
theorem mem_index_cell (q k : ℤ) (x : ℝ) : x ∈ cell q k (index q k x) := by
  have hl := Int.floor_le (x / scale k - shift q k)
  have hr := Int.lt_floor_add_one (x / scale k - shift q k)
  have hs := scale_pos k
  have hmul := mul_le_mul_of_nonneg_left hl hs.le
  have hmul' := mul_lt_mul_of_pos_left hr hs
  have heq : scale k * (x / scale k - shift q k) = x - scale k * shift q k := by
    field_simp [hs.ne']
  rw [heq] at hmul hmul'
  change scale k * (index q k x + shift q k) ≤ x ∧
    x < scale k * ((index q k x + 1 : ℤ) + shift q k)
  push_cast
  dsimp only [index]
  constructor <;> nlinarith

/-- The alternating shift gives actual nesting at successive dyadic scales. -/
theorem cell_subset_parent (q k j : ℤ) : cell q k j ⊆ cell q (k + 1) (parent q k j) := by
  have hmod0 := Int.emod_nonneg (j + (k.negOnePow : ℤ) * q) (by norm_num : (2 : ℤ) ≠ 0)
  have hmod2 := Int.emod_lt_of_pos (j + (k.negOnePow : ℤ) * q) (by norm_num : (0 : ℤ) < 2)
  have hdiv := Int.emod_add_ediv_mul (j + (k.negOnePow : ℤ) * q) 2
  have hlo : 2 * parent q k j ≤ j + (k.negOnePow : ℤ) * q := by
    unfold parent
    omega
  have hhi : j + (k.negOnePow : ℤ) * q + 1 ≤ 2 * parent q k j + 2 := by
    unfold parent
    omega
  have hlo' : (2 : ℝ) * parent q k j ≤ (j : ℝ) + ((k.negOnePow : ℤ) * q : ℤ) := by
    exact_mod_cast hlo
  have hhi' : (j : ℝ) + ((k.negOnePow : ℤ) * q : ℤ) + 1 ≤ 2 * parent q k j + 2 := by
    exact_mod_cast hhi
  push_cast at hlo' hhi'
  have hs := scale_pos k
  have hmlo := mul_le_mul_of_nonneg_left hlo' hs.le
  have hmhi := mul_le_mul_of_nonneg_left hhi' hs.le
  have hleft : left q (k + 1) (parent q k j) ≤ left q k j := by
    unfold left
    rw [scale_succ, shift_succ]
    unfold shift
    push_cast
    nlinarith
  have hright : left q k (j + 1) ≤ left q (k + 1) (parent q k j + 1) := by
    unfold left
    rw [scale_succ, shift_succ]
    unfold shift
    push_cast
    nlinarith
  intro x hx
  exact ⟨hleft.trans hx.1, hx.2.trans_le hright⟩

theorem cells_disjoint (q k : ℤ) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (cell q k i) (cell q k j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hs := scale_pos k
  change scale k * ((i : ℝ) + shift q k) ≤ x ∧
    x < scale k * (((i + 1 : ℤ) : ℝ) + shift q k) at hi
  change scale k * ((j : ℝ) + shift q k) ≤ x ∧
    x < scale k * (((j + 1 : ℤ) : ℝ) + shift q k) at hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    nlinarith
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    nlinarith

theorem cell_measurable (q k j : ℤ) : MeasurableSet (cell q k j) := measurableSet_Ico

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineNesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary-depth nesting and uniqueness in the alternating line grids. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

def ancestor (q k j : ℤ) : ℕ → ℤ
  | 0 => j
  | n + 1 => parent q (k + n) (ancestor q k j n)

theorem cell_subset_ancestor (q k j : ℤ) (n : ℕ) :
    cell q k j ⊆ cell q (k + n) (ancestor q k j n) := by
  induction n with
  | zero => simp [ancestor]
  | succ n ih =>
    have h := ih.trans (cell_subset_parent q (k + n) (ancestor q k j n))
    simpa only [ancestor, Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem index_eq_of_mem {q k j : ℤ} {x : ℝ} (hx : x ∈ cell q k j) :
    index q k x = j := by
  by_contra hne
  exact Set.disjoint_left.mp (cells_disjoint q k hne) (mem_index_cell q k x) hx

theorem cell_nonempty (q k j : ℤ) : (cell q k j).Nonempty := by
  refine ⟨left q k j, le_rfl, ?_⟩
  unfold left
  have hs := scale_pos k
  push_cast
  nlinarith

/-- Intersecting cells at ordered scales are nested, including across
arbitrarily many generations. -/
theorem cell_subset_of_intersect {q k l i j : ℤ} (hkl : k ≤ l)
    (hij : (cell q k i ∩ cell q l j).Nonempty) :
    cell q k i ⊆ cell q l j := by
  obtain ⟨n, rfl⟩ := Int.le.dest hkl
  have hsub := cell_subset_ancestor q k i n
  obtain ⟨x, hxi, hxj⟩ := hij
  have heq : ancestor q k i n = j := by
    by_contra hne
    exact Set.disjoint_left.mp (cells_disjoint q (k + n) hne) (hsub hxi) hxj
  simpa only [heq] using hsub

theorem cell_subset_index {q k l j : ℤ} {x : ℝ} (hkl : k ≤ l)
    (hx : x ∈ cell q k j) : cell q k j ⊆ cell q l (index q l x) :=
  cell_subset_of_intersect hkl ⟨x, hx, mem_index_cell q l x⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleMaximalL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Doob's scalar finite-horizon L2 estimate, with its exact factor four,
for the dyadic averages used in the axis-parallel rectangle count. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

def finiteMaxSignal {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) : ℝ :=
  (Finset.range (N+1)).sup' Finset.nonempty_range_add_one (fun i => |F i x|)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual integer-indexed dyadic line averages. The alternating grids are
handled directly, with no alignment premise between a packet and a root. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

theorem index_fiber (q k i : ℤ) : {x : ℝ | index q k x=i}=cell q k i := by
  ext x
  constructor
  · intro hx
    change index q k x=i at hx
    rw [←hx]
    exact mem_index_cell q k x
  · exact index_eq_of_mem

theorem index_measurable (q k : ℤ) : Measurable (index q k) := by
  apply measurable_to_countable'
  intro i
  change MeasurableSet {x : ℝ | index q k x=i}
  rw [index_fiber]
  exact cell_measurable q k i

theorem parent_index_eq (q k : ℤ) (x : ℝ) :
    parent q k (index q k x)=index q (k+1) x :=
  (index_eq_of_mem (cell_subset_parent q k (index q k x) (mem_index_cell q k x))).symm

def lineFiltration (q top : ℤ) : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq n := MeasurableSpace.comap (index q (top-(n:ℤ))) inferInstance
  le' n := (index_measurable q (top-n)).comap_le
  mono' := monotone_nat_of_le_succ fun n => by
    have heq : index q (top-(n:ℤ)) =
        parent q (top-((n+1:ℕ):ℤ)) ∘ index q (top-((n+1:ℕ):ℤ)) := by
      funext x
      have h := parent_index_eq q (top-((n+1:ℕ):ℤ)) x
      have he : top-((n+1:ℕ):ℤ)+1=top-(n:ℤ) := by omega
      simpa only [Function.comp_apply,he] using h.symm
    rw [heq,←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_countable _).comap_le

def rootMeasure (q top j : ℤ) : Measure ℝ := volume.restrict (cell q top j)

instance rootMeasure_finite (q top j : ℤ) : IsFiniteMeasure (rootMeasure q top j) := ⟨by
  change (volume.restrict (cell q top j)) univ < ∞
  rw [Measure.restrict_apply_univ]
  exact measure_Ico_lt_top⟩

def lineAverage (q top j : ℤ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (rootMeasure q top j)[f | lineFiltration q top n]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGlobalDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform L² bound for actual dyadic cell averages on the whole line.
The root intervals are glued using their true measurable partition. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def cellMean (q k : ℤ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in cell q k (index q k x), f y)/scale k

def dyadicMaximal (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  finiteMaxSignal (fun n => cellMean q (top-(n:ℤ)) f) N

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMonotoneMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from finite scale cutoffs to a genuine countable maximal
function. The real-valued representative is defined even on the null set
where the extended supremum is infinite. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

def maximalSquare {X : Type*} (F : ℕ → X → ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal ((F n x)^2)

def monotoneMaximal {X : Type*} (F : ℕ → X → ℝ) (x : X) : ℝ :=
  Real.sqrt (maximalSquare F x).toReal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAxisMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual one-coordinate dyadic maximal operator on the plane.
Fubini transfers the uniform line estimate without a dimension or scale
count factor. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def horizontalCellMean (q k : ℤ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  cellMean q k (fun x => f (x,z.2)) z.1

def horizontalMaximal (q top : ℤ) (N : ℕ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  dyadicMaximal q top N (fun x => f (x,z.2)) z.1

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAllDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic maximal averages over all integer scales. Uniform finite
estimates give the countable-scale estimate without any scale loss. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def allDyadicMaximal (q : ℤ) (f : ℝ → ℝ) : ℝ → ℝ :=
  monotoneMaximal (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

abbrev GridChoice := {q : ℤ // q∈Finset.Icc (-1) 1}

def threeGridMaximal (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ q : GridChoice, allDyadicMaximal q.val f x

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicSquareWeakL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-scale square averages in a fixed pair of dyadic grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

abbrev SquareIndex := ℤ × ℤ × ℤ

def squareCell (qx qy : ℤ) (p : SquareIndex) : Set (ℝ × ℝ) :=
  cell qx p.1 p.2.1 ×ˢ cell qy p.1 p.2.2

def gridSquareSup (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ⨆ p : SquareIndex, (squareCell qx qy p).indicator
    (fun _ => (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
      (volume.prod volume) (squareCell qx qy p)) z

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

def lineEnvelope (a l : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((1 + ((x - a) / l) ^ 2) ^ n)⁻¹

theorem lineEnvelope_nonneg (a l : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ lineEnvelope a l n x := by
  unfold lineEnvelope
  positivity

theorem integral_lineEnvelope_one (a l : ℝ) (hl : 0 < l) :
    (∫ x, lineEnvelope a l 1 x) = Real.pi * l := by
  simp only [lineEnvelope, pow_one]
  rw [integral_sub_right_eq_self (fun x : ℝ => (1 + (x / l) ^ 2)⁻¹),
    Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) l,
    integral_univ_inv_one_add_sq, abs_of_pos hl]
  ring

theorem integrable_lineEnvelope_one (a l : ℝ) (hl : 0 < l) :
    Integrable (lineEnvelope a l 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_lineEnvelope_one a l hl]
  exact mul_ne_zero Real.pi_ne_zero hl.ne'

theorem lineEnvelope_antitone (a l x : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    lineEnvelope a l n x ≤ lineEnvelope a l m x := by
  have hb : 1 ≤ 1 + ((x - a) / l) ^ 2 := by nlinarith [sq_nonneg ((x - a) / l)]
  unfold lineEnvelope
  exact inv_anti₀ (pow_pos (by positivity) m) (pow_le_pow_right₀ hb hmn)

theorem integrable_lineEnvelope (a l : ℝ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (lineEnvelope a l n) := by
  have hm : Measurable (lineEnvelope a l n) := by unfold lineEnvelope; fun_prop
  apply (integrable_lineEnvelope_one a l hl).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (lineEnvelope_nonneg a l n x)]
  exact lineEnvelope_antitone a l x hn

theorem integral_lineEnvelope_le (a l : ℝ) (hl : 0 < l) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x, lineEnvelope a l n x) ≤ Real.pi * l := by
  rw [← integral_lineEnvelope_one a l hl]
  exact integral_mono (integrable_lineEnvelope a l hl hn)
    (integrable_lineEnvelope_one a l hl) (fun x => lineEnvelope_antitone a l x hn)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal derivatives of the fixed rational packet envelope. -/

noncomputable section

namespace LipschitzHilbert

theorem lineEnvelope_three_hasDerivAt (a l x : ℝ) :
    HasDerivAt (lineEnvelope a l 3)
      ((-6 / l) * ((x-a)/l) * ((1+((x-a)/l)^2)^4)⁻¹) x := by
  have ht := ((hasDerivAt_id x).sub_const a).div_const l
  have hb := (ht.pow 2).const_add 1
  have hbase : 1 + ((x-a)/l)^2 ≠ 0 := by positivity
  have hd := (hb.pow 3).inv (pow_ne_zero 3 hbase)
  refine hd.congr_deriv ?_
  · simp only [Pi.pow_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one]
    set t := (x-a)/l
    field_simp
    ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

def packetSynthesis {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ i, c i • f i

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PublishedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published inputs for the Lipschitz-direction Hilbert transform

The two classical estimates used by the manuscript are stated as propositions.
Their deterministic consequences make the quantifiers needed for the
finite rectangle and martingale applications explicit.

* Lacey--Li, *On a conjecture of E. M. Stein on the Hilbert transform on
  vector fields*, Memoirs AMS 205 (2010), no. 965, result 1.10 and equation
  (1.11); DOI 10.1090/S0065-9266-10-00572-7. In the author version
  arXiv:0704.0808 these occur on printed p. 3, with the finite-family proof
  in Chapter 3. This is the published form of arXiv:math/0601213v2,
  Theorem 1.4. We use the finite admissible-rectangle weak `(2,2)` estimate.
* Zorin-Kranich, *Weighted Lépingle inequality*, Bernoulli 26 (2020),
  2311--2318, Theorem 1.1, with `p = 2`, `r = 3`, and weight one.
  We use only real-valued finite martingales on probability spaces.

The deterministic consequences below make the quantifiers relevant to the
application explicit: a union of high-average rectangles, and a variation
sum whose increasing indices may be chosen separately at each point.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

/-- A closed orthogonal rectangle; `long` and `short` are full side lengths. -/
structure Rectangle where
  center : Plane
  axes : OrthonormalBasis (Fin 2) ℝ Plane
  long : ℝ
  short : ℝ
  short_pos : 0 < short
  short_le_long : short ≤ long

namespace Rectangle

def carrier (R : Rectangle) : Set Plane :=
  {x | |R.axes.repr (x - R.center) 0| ≤ R.long / 2 ∧
    |R.axes.repr (x - R.center) 1| ≤ R.short / 2}

/-- The arc of total angular length `short / long` about the long-side direction.
The field is separately required to have unit norm. -/
def popularSet (R : Rectangle) (v : Plane → Plane) : Set Plane :=
  {x ∈ R.carrier | Real.cos (R.short / (2 * R.long)) ≤ inner ℝ (v x) (R.axes 0)}

/-- Admissibility uses the long-side length restriction, with no restriction when `K = 0`. -/
def Admissible (R : Rectangle) (v : Plane → Plane) (K δ : ℝ≥0) : Prop :=
  100 * (K : ℝ) * R.long ≤ 1 ∧
    (δ : ℝ≥0∞) * volume R.carrier ≤ volume (R.popularSet v)

def average (R : Rectangle) (h : Plane → ℝ) : ℝ≥0∞ :=
  (volume R.carrier)⁻¹ * ∫⁻ x in R.carrier, ‖h x‖ₑ

end Rectangle

/-- The finite-rectangle maximal function appearing in the needed specialization. -/
def rectangleMaximum {ι : Type*} [Fintype ι] (R : ι → Rectangle)
    (h : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  by
    classical
    exact Finset.univ.sup fun i => if x ∈ (R i).carrier then (R i).average h else 0

/-- Squared `L²` size; using the nonnegative integral also covers intermediate expressions. -/
def squareIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω → ℝ) : ℝ≥0∞ := ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ

/-- Lacey--Li, published result 1.10 / equation (1.11), specialized to finite
families in squared weak-type form (also arXiv:math/0601213v2, Theorem 1.4).
`C` is the weak `L²` operator constant before squaring. -/
def LaceyLiInput : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (v : Plane → Plane) (K δ : ℝ≥0),
      LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
      ∀ (n : ℕ) (R : Fin n → Rectangle),
        (∀ i, (R i).Admissible v K δ) →
        ∀ (h : Plane → ℝ), MemLp h 2 volume → ∀ t : ℝ≥0, 0 < t →
          (t : ℝ≥0∞) ^ 2 * volume {x | (t : ℝ≥0∞) < rectangleMaximum R h x} ≤
            (C : ℝ≥0∞) ^ 2 / (δ : ℝ≥0∞) * squareIntegral volume h

/-- Cubed variation of a finite scalar sequence. Repetitions in the monotone list
allow every shorter partition to be padded to length `N + 1`. -/
def variationCube {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) : ℝ≥0∞ :=
  by
    classical
    exact Finset.univ.sup fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3
      else 0

/-- Lépingle's unweighted scalar `L²` bound for `3`-variation. The constant is
uniform in the probability space, the filtration, and the finite horizon. -/
def LepingleInput : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (ℱ : Filtration ℕ m) (F : ℕ → Ω → ℝ),
        Martingale F ℱ μ → (∀ n, MemLp (F n) 2 μ) → ∀ N : ℕ,
          (∫⁻ x, variationCube F N x ^ (2 / 3 : ℝ) ∂μ) ≤
            (C : ℝ≥0∞) ^ 2 * squareIntegral μ (F N)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing localized packet variations with summable box weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def cubicVariation {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) : ℝ :=
  (finiteCubicVariation F N) ^ (1 / 3 : ℝ)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ComplexLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex Hilbert-valued averages on the actual finite line grid. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

namespace FiniteLineGrid

def complexAverage {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => (g.average μ (fun y => (F y k).re) n x : ℂ) +
    g.average μ (fun y => (F y k).im) n x * Complex.I)

end FiniteLineGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ComplexBandAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar complex packet averages on the actual line grid. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

namespace FiniteLineGrid

def scalarAverage (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (n : ℕ) (x : ℝ) : ℂ :=
  (g.average μ (fun y => (f y).re) n x : ℂ) +
    g.average μ (fun y => (f y).im) n x * Complex.I

@[simp] theorem scalarAverage_re (g : FiniteLineGrid) (μ : Measure ℝ)
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    (g.scalarAverage μ f n x).re = g.average μ (fun y => (f y).re) n x := by
  simp [scalarAverage]

@[simp] theorem scalarAverage_im (g : FiniteLineGrid) (μ : Measure ℝ)
    (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    (g.scalarAverage μ f n x).im = g.average μ (fun y => (f y).im) n x := by
  simp [scalarAverage]

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAverageComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual annular packet errors without a scale-count loss. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

def partialBandSum {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) (x : ℝ) : ℂ :=
  ∑ j, if j.val < i then f j x else 0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShiftedLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Start the actual mesh martingale at a prescribed finer level. This
allows the surrounding finite root interval to grow without changing
the packet scales used in the comparison. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert
namespace FiniteLineGrid

def shiftedFiltration (g : FiniteLineGrid) (offset : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq i := g.filtration (offset + i)
  mono' := fun _ _ h => g.filtration.mono (Nat.add_le_add_left h offset)
  le' i := g.filtration.le (offset + i)

end FiniteLineGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertAnnularVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional complex annular variation estimate, with no
dependence of the constant on the number of coordinates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

def hilbertPartialBandSum {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (i : ℕ) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => partialBandSum (fun j => f j k) i x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveLineKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive horizontal convolution kernel used for the error
majorant, with its short-interval integral bound. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

def lineKernel (l x : ℝ) : ℝ := l⁻¹ * lineEnvelope 0 l 3 x

theorem lineKernel_nonneg (l x : ℝ) (hl : 0 < l) : 0 ≤ lineKernel l x :=
  mul_nonneg (inv_nonneg.mpr hl.le) (lineEnvelope_nonneg _ _ _ _)

theorem lineKernel_shift (l s x : ℝ) :
    lineKernel l (x-s) = l⁻¹ * lineEnvelope s l 3 x := by
  simp only [lineKernel, lineEnvelope, sub_zero]

theorem lineKernel_integrable (l s : ℝ) (hl : 0 < l) :
    Integrable (fun x => lineKernel l (x-s)) := by
  simp_rw [lineKernel_shift]
  exact (integrable_lineEnvelope s l hl (by decide : 1 ≤ 3)).const_mul _

theorem integral_lineKernel_le (l s : ℝ) (hl : 0 < l) :
    (∫ x, lineKernel l (x-s)) ≤ Real.pi := by
  simp_rw [lineKernel_shift]
  rw [integral_const_mul]
  calc
    _ ≤ l⁻¹ * (Real.pi*l) :=
      mul_le_mul_of_nonneg_left (integral_lineEnvelope_le s l hl (by decide : 1 ≤ 3)) (by positivity)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual convolution of the positive error source with the horizontal
kernel. Bounded measurable sources need not be globally integrable. -/

noncomputable section
open Set MeasureTheory

namespace LipschitzHilbert

def positiveConvolution (l : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s, lineKernel l (x-s) * f s

theorem lineKernel_continuous (l : ℝ) : Continuous (lineKernel l) :=
  (continuous_iff_continuousAt.mpr (fun x => (lineEnvelope_three_hasDerivAt 0 l x).continuousAt)).const_mul _

theorem lineKernel_sub_comm (l x s : ℝ) : lineKernel l (x-s) = lineKernel l (s-x) := by
  simp only [lineKernel, lineEnvelope, sub_zero, div_pow, sub_sq_comm]

theorem positiveConvolution_integrable_at {f : ℝ → ℝ} (hf : Measurable f)
    {C l : ℝ} (hl : 0 < l) (hbound : ∀ s, ‖f s‖ ≤ C) (x : ℝ) :
    Integrable (fun s => lineKernel l (x-s) * f s) := by
  have hi : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  exact hi.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem positiveConvolution_nonneg {f : ℝ → ℝ} {l : ℝ} (hl : 0 < l)
    (hf : ∀ s, 0 ≤ f s) (x : ℝ) : 0 ≤ positiveConvolution l f x :=
  integral_nonneg (fun s => mul_nonneg (lineKernel_nonneg l (x-s) hl) (hf s))

theorem positiveConvolution_le {f : ℝ → ℝ} (hf : Measurable f) {C l : ℝ}
    (hl : 0 < l) (hC : 0 ≤ C) (hbound : ∀ s, ‖f s‖ ≤ C) (x : ℝ) :
    ‖positiveConvolution l f x‖ ≤ C * Real.pi := by
  have hi : Integrable (fun s => lineKernel l (x-s)) := by
    simp_rw [lineKernel_sub_comm l x]
    exact lineKernel_integrable l x hl
  calc
    _ ≤ ∫ s, ‖lineKernel l (x-s) * f s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s, lineKernel l (x-s) * C := by
      apply integral_mono (positiveConvolution_integrable_at hf hl hbound x).norm (hi.mul_const C)
      intro s
      change ‖lineKernel l (x-s) * f s‖ ≤ lineKernel l (x-s) * C
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (lineKernel_nonneg _ _ hl)]
      exact mul_le_mul_of_nonneg_left (hbound s) (lineKernel_nonneg _ _ hl)
    _ = C * ∫ s, lineKernel l (s-x) := by
      simp_rw [lineKernel_sub_comm l x]
      rw [integral_mul_const, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_lineKernel_le l x hl) hC

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PositiveErrorMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive convolution majorant for the error terms. Source
size and source-sum bounds remain explicit; BMO is derived for this
majorant rather than assumed for every function it dominates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

structure LineErrorSources (N : ℕ) where
  topLength : ℝ
  topLength_pos : 0 < topLength
  sourceBound : ℝ
  sourceBound_nonneg : 0 ≤ sourceBound
  sumBound : ℝ
  sumBound_nonneg : 0 ≤ sumBound
  source : Fin N → ℝ → ℝ
  measurable_source : ∀ j, Measurable (source j)
  source_nonneg : ∀ j s, 0 ≤ source j s
  source_bound : ∀ j s, source j s ≤ sourceBound
  source_sum : ∀ s, ∑ j, source j s ≤ sumBound

namespace LineErrorSources

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

def length (P : LineErrorSources N) (j : Fin N) : ℝ := P.topLength / (2 : ℝ)^j.val
def term (P : LineErrorSources N) (j : Fin N) : ℝ → ℝ := positiveConvolution (P.length j) (P.source j)
def majorant (P : LineErrorSources N) (x : ℝ) : ℝ := ∑ j, P.term j x
def shortPart (P : LineErrorSources N) (r x : ℝ) : ℝ := ∑ j, if P.length j ≤ r then P.term j x else 0
def longPart (P : LineErrorSources N) (r x : ℝ) : ℝ := ∑ j, if r < P.length j then P.term j x else 0
def meanConstant (P : LineErrorSources N) : ℝ := (1024 * Real.pi^2) * P.sumBound
def oscillationConstant (P : LineErrorSources N) : ℝ := 240 * Real.pi * P.sourceBound

end LineErrorSources
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalErrorSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the error sources with the common vertical kernel preserves
the pointwise and summed bounds used on every reference line. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem positiveConvolution_finset_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) {C l : ℝ}
    (hl : 0 < l) (hbound : ∀ j s, ‖f j s‖ ≤ C) (x : ℝ) :
    positiveConvolution l (fun s => ∑ j, f j s) x = ∑ j, positiveConvolution l (f j) x := by
  unfold positiveConvolution
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun j _ => positiveConvolution_integrable_at (hf j) hl (hbound j) x)

theorem verticalConvolution_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) (W y : ℝ) :
    Measurable (fun x => positiveConvolution W (fun z => f (x,z)) y) := by
  have hm : Measurable (fun p : ℝ × ℝ => lineKernel W (y-p.2) * f p) :=
    ((lineKernel_continuous W).measurable.comp (measurable_const.sub measurable_snd)).mul hf
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

def verticalErrorSources {N : ℕ} (f : Fin N → ℝ × ℝ → ℝ)
    (hf : ∀ j, Measurable (f j)) (L W y C M : ℝ)
    (hL : 0 < L) (hW : 0 < W) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hf0 : ∀ j p, 0 ≤ f j p) (hfC : ∀ j p, f j p ≤ C)
    (hfM : ∀ p, ∑ j, f j p ≤ M) : LineErrorSources N where
  topLength := L
  topLength_pos := hL
  sourceBound := C * Real.pi
  sourceBound_nonneg := mul_nonneg hC Real.pi_pos.le
  sumBound := M * Real.pi
  sumBound_nonneg := mul_nonneg hM Real.pi_pos.le
  source := fun j x => positiveConvolution W (fun z => f j (x,z)) y
  measurable_source := fun j => verticalConvolution_measurable (hf j) W y
  source_nonneg := fun j x => positiveConvolution_nonneg hW (fun z => hf0 j (x,z)) y
  source_bound := by
    intro j x
    have hf' : Measurable (fun z => f j (x,z)) := (hf j).comp (measurable_const.prodMk measurable_id)
    have hb (z : ℝ) : ‖f j (x,z)‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 j (x,z))]
      exact hfC j (x,z)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using positiveConvolution_le hf' hW hC hb y)
  source_sum := by
    intro x
    have hf' (j : Fin N) : Measurable (fun z => f j (x,z)) :=
      (hf j).comp (measurable_const.prodMk measurable_id)
    have hb (j : Fin N) (z : ℝ) : ‖f j (x,z)‖ ≤ C := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 j (x,z))]
      exact hfC j (x,z)
    rw [← positiveConvolution_finset_sum (fun j z => f j (x,z)) hf' hW hb y]
    have hs : Measurable (fun z => ∑ j, f j (x,z)) :=
      Finset.measurable_sum _ (fun j _ => hf' j)
    have hbs (z : ℝ) : ‖∑ j, f j (x,z)‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun j _ => hf0 j (x,z)))]
      exact hfM (x,z)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using positiveConvolution_le hs hW hM hbs y)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

def blockCount (L : ℝ) : ℕ := ⌈Real.log L ^ 2⌉₊

def stepExponent (L : ℝ) : ℕ := 2 * ⌈L ^ (7 / 10 : ℝ) / (2 * Real.log 2)⌉₊

def step (L : ℝ) : ℝ := 2 ^ stepExponent L

def branching (L : ℝ) : ℝ := step L ^ blockCount L

theorem step_pos (L : ℝ) : 0 < step L := pow_pos (by norm_num) _

theorem branching_pos (L : ℝ) : 0 < branching L := pow_pos (step_pos L) _

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ErrorSourceBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the line error data from the manuscript's actual
two-coordinate direction profile and common vertical averaging kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def actualErrorSources {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2 : ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) : LineErrorSources N := by
  let K := J+4*E
  let F := fun (j : Fin N) (p : ℝ × ℝ) =>
    A * errorSourceProfile c (C' * ((2 : ℝ)^E)^4) (a*(2 : ℝ)^j.val) |direction p-t|
  have hR : C' * ((2 : ℝ)^E)^4 ≤ c*(2 : ℝ)^K := by
    have hp : (2 : ℝ)^(4*E) = ((2 : ℝ)^E)^4 := by rw [Nat.mul_comm, pow_mul]
    apply (mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ ((2 : ℝ)^E)^4)).trans_eq
    dsimp [K]
    rw [pow_add,hp]
    ring
  have hF (j : Fin N) : Measurable (F j) := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hdirection.sub measurable_const).norm
  have hF0 (j : Fin N) (p : ℝ × ℝ) : 0 ≤ F j p :=
    mul_nonneg hA (errorSourceProfile_nonneg c _ _ _ (by positivity) (abs_nonneg _))
  have hFb (j : Fin N) (p : ℝ × ℝ) : F j p ≤ A*(1+c) :=
    mul_le_mul_of_nonneg_left (errorSourceProfile_bound c _ _ _ hc (by positivity) (abs_nonneg _)) hA
  have hFs (p : ℝ × ℝ) : (∑ j, F j p) ≤ A*((K+1 : ℕ)+4*c) := by
    dsimp [F]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_errorSourceProfile N K a c _ _ ha hc (abs_nonneg _) hR) hA
  exact verticalErrorSources F hF topLength W y (A*(1+c)) (A*((K+1 : ℕ)+4*c))
    hL hW (by positivity) (by positivity) hF0 hFb hFs

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual maxima of subinterval sums on residual segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def intervalOscillation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic energy and relative prediction deficits

The exact `p`-Lipschitz estimate for `log (1 + ‖x‖^p)` from §§9–10.
A fixed denominator then cancels from differences of log predictions,
so bounded off-path motion gives a deficit proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E]

/-- The prediction ratio with a fixed positive denominator. -/
def energyRatio (p denominator : ℝ) (x : E) : ℝ := (1 + ‖x‖ ^ p) / denominator

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MultiplierError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular multiplier error is bounded by the actual annulus-plus-
small-angle-ratio source from the manuscript. -/

noncomputable section

namespace LipschitzHilbert

def multiplierError (b : ℝ → ℂ) (t d u : ℝ) : ℂ :=
  b u - (if |u-t| ≤ d then b t else 0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SnappedLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put translated sheared packet lattices on a common reference lattice.
The site map is injective and moves each center by at most one mesh in
both coordinates. No equality of the physical and reference lattices is
assumed. -/

noncomputable section
namespace LipschitzHilbert

/-- Quantize a translated, sheared lattice without identifying distinct
sites of that lattice. The shear is measured in the reference coordinates. -/
def snappedLatticeSite (a b l W delta : ℝ) (q : ℤ × ℤ) : ℤ × ℤ :=
  (⌊a/l⌋+q.1,⌊(b+delta*l*q.1)/W⌋+q.2)

theorem snappedLatticeSite_injective (a b l W delta : ℝ) :
    Function.Injective (snappedLatticeSite a b l W delta) := by
  intro q q' h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change ⌊a/l⌋+q.1 = ⌊a/l⌋+q'.1 at hx
  have hx' : q.1 = q'.1 := add_left_cancel hx
  change ⌊(b+delta*l*q.1)/W⌋+q.2 = ⌊(b+delta*l*q'.1)/W⌋+q'.2 at hy
  rw [hx'] at hy
  exact Prod.ext hx' (add_left_cancel hy)

theorem floor_mesh_error (x l : ℝ) (hl : 0 < l) :
    |x-l*(⌊x/l⌋:ℤ)| ≤ l := by
  have hlo := Int.floor_le (x/l)
  have hhi := Int.lt_floor_add_one (x/l)
  have hlo' := (le_div_iff₀ hl).mp hlo
  have hhi' := (div_lt_iff₀ hl).mp hhi
  apply abs_le.mpr
  constructor <;> nlinarith

theorem snappedLatticeSite_horizontal (a b l W delta : ℝ) (hl : 0 < l) (q : ℤ × ℤ) :
    |(a+l*q.1)-l*(snappedLatticeSite a b l W delta q).1| ≤ l := by
  have h := floor_mesh_error a l hl
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [snappedLatticeSite,Int.cast_add]
  ring

theorem snappedLatticeSite_vertical (a b l W delta : ℝ) (hW : 0 < W) (q : ℤ × ℤ) :
    |(b+delta*l*q.1+W*q.2)-W*(snappedLatticeSite a b l W delta q).2| ≤ W := by
  have h := floor_mesh_error (b+delta*l*q.1) W hW
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp only [snappedLatticeSite,Int.cast_add]
  ring

/-- Moving a center by at most one mesh preserves any fixed decay order. -/
theorem lineEnvelope_near_center (a b l x : ℝ) (n : ℕ) (hl : 0 < l)
    (hab : |a-b| ≤ l) :
    lineEnvelope a l n x ≤ 3^n*lineEnvelope b l n x := by
  let u := (x-a)/l
  let d := (a-b)/l
  have hd : |d| ≤ 1 := by
    dsimp [d]
    rw [abs_div,abs_of_pos hl]
    exact (div_le_one hl).mpr hab
  have hd2 : d^2 ≤ 1 := by nlinarith [abs_le.mp hd,sq_abs d]
  have hv : (x-b)/l = u+d := by dsimp [u,d]; ring
  have hbase : 1+((x-b)/l)^2 ≤ 3*(1+((x-a)/l)^2) := by
    rw [hv]
    change 1+(u+d)^2 ≤ 3*(1+u^2)
    nlinarith [sq_nonneg (u-d)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+((x-b)/l)^2) hbase n
  have ha : 0 < (1+((x-a)/l)^2)^n := by positivity
  have hb : 0 < (1+((x-b)/l)^2)^n := by positivity
  unfold lineEnvelope
  rw [← one_div,← div_eq_mul_inv]
  apply (div_le_div_iff₀ ha hb).mpr
  simpa only [one_mul,mul_pow] using hp

/-- Product decay survives the actual center quantization with fixed cost. -/
theorem snappedLatticeSite_envelope (a b l W delta x y : ℝ)
    (hl : 0 < l) (hW : 0 < W) (q : ℤ × ℤ) (nx ny : ℕ) :
    lineEnvelope (a+l*q.1) l nx x *
        lineEnvelope (b+delta*l*q.1+W*q.2) W ny y ≤
      (3^nx*3^ny) *
        (lineEnvelope (l*(snappedLatticeSite a b l W delta q).1) l nx x *
          lineEnvelope (W*(snappedLatticeSite a b l W delta q).2) W ny y) := by
  have hx := lineEnvelope_near_center (a+l*q.1)
    (l*(snappedLatticeSite a b l W delta q).1) l x nx hl
    (snappedLatticeSite_horizontal a b l W delta hl q)
  have hy := lineEnvelope_near_center (b+delta*l*q.1+W*q.2)
    (W*(snappedLatticeSite a b l W delta q).2) W y ny hW
    (snappedLatticeSite_vertical a b l W delta hW q)
  have h := mul_le_mul hx hy (lineEnvelope_nonneg _ _ _ _)
    (mul_nonneg (by positivity) (lineEnvelope_nonneg _ _ _ _))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maximal bad intervals exist below a fixed largest dyadic scale. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

def MaximalBad (q top : ℤ) (bad : ℤ → ℤ → Prop) (k j : ℤ) : Prop :=
  k ≤ top ∧ bad k j ∧ ∀ l i, k < l → l ≤ top → cell q k j ⊆ cell q l i → ¬bad l i

/-- Every bad interval has a maximal bad ancestor before the prescribed
largest scale. No choice from an uncountable interval family is involved. -/
theorem exists_maximalBad {q top k j : ℤ} {bad : ℤ → ℤ → Prop}
    (hktop : k ≤ top) (hbad : bad k j) :
    ∃ l i, MaximalBad q top bad l i ∧ cell q k j ⊆ cell q l i := by
  classical
  obtain ⟨x, hx⟩ := cell_nonempty q k j
  obtain ⟨N, hN⟩ := Int.le.dest hktop
  let P : ℕ → Prop := fun n => bad (k + n) (index q (k + n) x)
  have hP0 : P 0 := by
    simpa only [P, Nat.cast_zero, add_zero, index_eq_of_mem hx] using hbad
  let n := Nat.findGreatest P N
  have hn : n ≤ N := Nat.findGreatest_le N
  have hPn : P n := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hkn : k ≤ k + (n : ℤ) := by omega
  have hntop : k + (n : ℤ) ≤ top := by omega
  refine ⟨k + n, index q (k + n) x, ⟨hntop, hPn, ?_⟩, cell_subset_index hkn hx⟩
  intro l i hnl hltop hsub hbi
  have hkl : k ≤ l := hkn.trans hnl.le
  obtain ⟨m, hm⟩ := Int.le.dest hkl
  have hmn : n < m := by omega
  have hmN : m ≤ N := by omega
  have hxi : x ∈ cell q l i := hsub (mem_index_cell q (k + n) x)
  have hmP : P m := by
    dsimp only [P]
    rw [hm, index_eq_of_mem hxi]
    exact hbi
  exact Nat.findGreatest_is_greatest hmn hmN hmP

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal Whitney cells for the ordinary tree estimate. An allowed
cell has no tile of shorter length whose center meets its triple. A
maximal allowed cell obtains its concrete witness from its parent. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
attribute [local instance] Classical.propDecidable

def center (k j : ℤ) : ℝ := left 0 k j+scale k/2

def Allowed {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ) (k j : ℤ) : Prop :=
  ∀ i ∈ tiles, ell i ≤ scale k → (3/2:ℝ)*scale k < |x i-center k j|

def Whitney {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ) (k j : ℤ) : Prop :=
  Allowed tiles x ell k j ∧ ¬Allowed tiles x ell (k+1) (parent 0 k j)

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShearedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer a packet's decay to a nearby reference slope. A bounded
normalized shear costs a fixed packet order and a fixed constant. -/

noncomputable section
namespace LipschitzHilbert

theorem unit_shear_envelope (x y beta : ℝ) (n : ℕ) (hbeta : |beta| ≤ 1) :
    lineEnvelope 0 1 (2*n) x*lineEnvelope 0 1 (2*n) (y-beta*x) ≤
      2^n*(lineEnvelope 0 1 n x*lineEnvelope 0 1 n y) := by
  let A := 1+x^2
  let B := 1+(y-beta*x)^2
  let C := 1+y^2
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg x]
  have hB : 1 ≤ B := by dsimp [B]; nlinarith [sq_nonneg (y-beta*x)]
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg y]
  have hb : beta^2 ≤ 1 := by nlinarith [abs_le.mp hbeta, sq_abs beta]
  have hbx : (beta*x)^2 ≤ x^2 := by nlinarith [sq_nonneg x]
  have hbase : C ≤ 2*A*B := by
    dsimp [A,B,C]
    nlinarith [sq_nonneg (y-2*(beta*x)), sq_nonneg x, sq_nonneg (y-beta*x),
      mul_nonneg (sq_nonneg x) (sq_nonneg (y-beta*x))]
  have hbig : A*C ≤ 2*(A*B)^2 := by
    have h1 := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ A)
    have h2 : B ≤ B^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*A^2)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ A*C) hbig n
  simp only [lineEnvelope, sub_zero, div_one]
  change (A^(2*n))⁻¹*(B^(2*n))⁻¹ ≤ 2^n*((A^n)⁻¹*(C^n)⁻¹)
  have hleft : 0 < A^(2*n)*B^(2*n) := by positivity
  have hright : 0 < A^n*C^n := by positivity
  rw [← mul_inv, ← mul_inv]
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hleft hright).mpr
  simp only [one_mul]
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using hpow

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Schwartz restrictions to affine reference lines. This applies
to general two-variable packets, with no tensor factorization. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem affineLine_antilipschitz (b s : ℝ) :
    AntilipschitzWith 1 (fun x : ℝ => (x,b+s*x)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq]
  exact le_max_left _ _

theorem affineLine_temperate (b s : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ => (x,b+s*x)) := by
  let A : ℝ →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.id ℝ ℝ).prod
    (s • ContinuousLinearMap.id ℝ ℝ)
  have h := (Function.HasTemperateGrowth.const (E := ℝ) (0,b)).add A.hasTemperateGrowth
  change Function.HasTemperateGrowth (fun x => (0,b)+A x) at h
  simpa only [A,ContinuousLinearMap.prod_apply,smul_apply,
    ContinuousLinearMap.id_apply,Prod.mk_add_mk,zero_add,smul_eq_mul] using h

def planarSchwartzSlice (f : SchwartzMap (ℝ × ℝ) ℂ) (b s : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => (x,b+s*x))
    (affineLine_temperate b s) (affineLine_antilipschitz b s) f

@[simp] theorem planarSchwartzSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ) (b s x : ℝ) :
    planarSchwartzSlice f b s x = f (x,b+s*x) := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarCovariantJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first two covariant vertical derivatives of a general planar
Schwartz packet, restricted to a reference line. -/

noncomputable section
namespace LipschitzHilbert

def planarVerticalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.evalCLM ℂ (ℝ × ℝ) ℂ (0,1) (SchwartzMap.fderivCLM ℂ (ℝ × ℝ) ℂ f)

@[simp] theorem planarVerticalDerivative_apply (f : SchwartzMap (ℝ × ℝ) ℂ) (z : ℝ × ℝ) :
    planarVerticalDerivative f z = fderiv ℝ f z (0,1) := rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSchwartzDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed product-envelope bounds for general planar Schwartz packets.
The constants are obtained from their actual weighted seminorms. -/

noncomputable section
namespace LipschitzHilbert

def planarPolynomialWeight (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (1+z.1^2)^n*(1+z.2^2)^n

theorem planarPolynomialWeight_pos (n : ℕ) (z : ℝ × ℝ) :
    0 < planarPolynomialWeight n z := by unfold planarPolynomialWeight; positivity

theorem planarPolynomialWeight_temperate (n : ℕ) :
    Function.HasTemperateGrowth (fun z : ℝ × ℝ => (planarPolynomialWeight n z : ℂ)) := by
  have hx : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  unfold planarPolynomialWeight
  fun_prop

def planarEnvelopeConstant (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.smulLeftCLM ℂ
    (fun z => (planarPolynomialWeight n z : ℂ)) f)+1

theorem planarEnvelopeConstant_pos (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    0 < planarEnvelopeConstant f n := by unfold planarEnvelopeConstant; positivity

theorem planar_schwartz_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (z : ℝ × ℝ) :
    ‖f z‖ ≤ planarEnvelopeConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  have hpos := planarPolynomialWeight_pos n z
  have h := SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.smulLeftCLM ℂ
    (fun z => (planarPolynomialWeight n z : ℂ)) f) z
  rw [SchwartzMap.smulLeftCLM_apply_apply (planarPolynomialWeight_temperate n),
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos] at h
  have hb : planarPolynomialWeight n z*‖f z‖ ≤ planarEnvelopeConstant f n := by
    unfold planarEnvelopeConstant
    linarith
  calc
    _ ≤ planarEnvelopeConstant f n/planarPolynomialWeight n z :=
      (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hb)
    _ = _ := by simp [planarPolynomialWeight,lineEnvelope,div_eq_mul_inv,mul_comm]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ScaledPlanarPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General planar Schwartz profiles in the physical packet coordinates.
The affine restriction retains Schwartz regularity and the carrier is
removed exactly by vertical covariant differentiation. -/

noncomputable section
open scoped NNReal
namespace LipschitzHilbert

theorem affineRescale_antilipschitz (a l : ℝ) (hl : l ≠ 0) :
    AntilipschitzWith ‖l‖₊ (fun x : ℝ => (x-a)/l) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [Real.dist_eq, coe_nnnorm]
  have heq : (x-a)/l-(y-a)/l = (x-y)/l := by ring
  rw [heq, abs_div]
  simp only [Real.norm_eq_abs]
  rw [mul_div_cancel₀ _ (abs_ne_zero.mpr hl)]

def scaledPlanarSlice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a l b beta : ℝ) (hl : l ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (g := fun x : ℝ => (x-a)/l) (by simp only [div_eq_mul_inv]; fun_prop)
    (affineRescale_antilipschitz a l hl) (planarSchwartzSlice f b beta)

@[simp] theorem scaledPlanarSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a l b beta : ℝ) (hl : l ≠ 0) (x : ℝ) :
    scaledPlanarSlice f a l b beta hl x = f ((x-a)/l,b+beta*((x-a)/l)) := rfl

theorem planarCarrier_temperate (a cy delta frequency y : ℝ) :
    Function.HasTemperateGrowth (fun x : ℝ =>
      Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)) := by
  exact Function.HasTemperateGrowth.comp (g := fun t : ℝ => Complex.exp (t * Complex.I)) OAI.hasTemperateGrowth_exp_mul_I (by fun_prop)

def modulatedPlanarSlice (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ =>
    Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I))
    (scaledPlanarSlice f a l ((y-cy)/W) (delta*l/W) hl)

theorem modulatedPlanarSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    modulatedPlanarSlice f a cy l W delta frequency y hl x =
      Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)*
        f ((x-a)/l,(y-cy+delta*(x-a))/W) := by
  rw [modulatedPlanarSlice, SchwartzMap.smulLeftCLM_apply_apply
    (planarCarrier_temperate a cy delta frequency y), scaledPlanarSlice_apply]
  simp only [smul_eq_mul]
  congr 2
  congr 1
  field_simp

theorem modulatedPlanarSlice_norm (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    ‖modulatedPlanarSlice f a cy l W delta frequency y hl x‖ =
      ‖f ((x-a)/l,(y-cy+delta*(x-a))/W)‖ := by
  rw [modulatedPlanarSlice_apply, norm_mul]
  have he : ‖Complex.exp ((frequency*(y-cy+delta*(x-a)) : ℝ)*Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [he, one_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform packet envelopes from general normalized planar profiles.
The bound does not depend on the carrier frequency or physical scales. -/

noncomputable section
namespace LipschitzHilbert

theorem modulatedPlanarSlice_jointContinuous (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency : ℝ) (hl : l ≠ 0) :
    Continuous (fun z : ℝ × ℝ => modulatedPlanarSlice f a cy l W delta frequency z.1 hl z.2) := by
  have heq : (fun z : ℝ × ℝ => modulatedPlanarSlice f a cy l W delta frequency z.1 hl z.2) =
      (fun z : ℝ × ℝ => Complex.exp ((frequency*(z.1-cy+delta*(z.2-a)):ℝ)*Complex.I)*
        f ((z.2-a)/l,(z.1-cy+delta*(z.2-a))/W)) := by
    funext z
    exact modulatedPlanarSlice_apply f a cy l W delta frequency z.1 hl z.2
  rw [heq]
  apply Continuous.mul (by fun_prop)
  exact f.continuous.comp (by fun_prop)

theorem modulatedPlanarSlice_envelope (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y C : ℝ) (hl : l ≠ 0) (n : ℕ)
    (hC : 0 ≤ C) (hshear : |delta*l/W| ≤ 1)
    (hf : ∀ z, ‖f z‖ ≤ C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2))
    (x : ℝ) :
    ‖modulatedPlanarSlice f a cy l W delta frequency y hl x‖ ≤
      (2^n*C)*(lineEnvelope a l n x*lineEnvelope cy W n y) := by
  rw [modulatedPlanarSlice_norm]
  have heq : (y-cy+delta*(x-a))/W =
      (y-cy)/W-(-delta*l/W)*((x-a)/l) := by
    field_simp
    ring
  have hs := unit_shear_envelope ((x-a)/l) ((y-cy)/W) (-delta*l/W) n
    (by simpa only [neg_mul, neg_div, abs_neg] using hshear)
  have hb := hf ((x-a)/l,(y-cy+delta*(x-a))/W)
  rw [heq] at hb ⊢
  apply hb.trans
  have h := mul_le_mul_of_nonneg_left hs hC
  simpa only [lineEnvelope, sub_zero, div_one, mul_left_comm C (2^n), mul_assoc] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarModulatedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three actual raw kernels for a general planar packet. The
covariant derivative differentiates its normalized vertical profile. -/

noncomputable section
namespace LipschitzHilbert

def planarProfileJet (f : SchwartzMap (ℝ × ℝ) ℂ) (ratio : ℝ)
    (i : Fin 3) : SchwartzMap (ℝ × ℝ) ℂ :=
  if i = 0 then f else if i = 1 then (ratio:ℂ) • planarVerticalDerivative f else
    (ratio:ℂ) • planarVerticalDerivative ((ratio:ℂ) • planarVerticalDerivative f)

def modulatedPlanarJet (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) : SchwartzMap ℝ ℂ :=
  modulatedPlanarSlice (planarProfileJet f (scale/W) i)
    a cy l W delta frequency y hl

theorem modulatedPlanarJet_continuous (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency scale : ℝ) (hl : l ≠ 0) (i : Fin 3) :
    Continuous (fun z : ℝ × ℝ => modulatedPlanarJet f a cy l W delta frequency scale z.1 hl i z.2) :=
  modulatedPlanarSlice_jointContinuous _ a cy l W delta frequency hl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PhysicalPlanarPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full two-dimensional Schwartz packet and its exact affine-line
restriction. This connects physical spectra to the constructed raw waves. -/

noncomputable section
namespace LipschitzHilbert

def packetCoordinates (l W θ : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun z := (z.1/l,(z.2-θ*z.1)/W)
  invFun z := (l*z.1,W*z.2+θ*(l*z.1))
  left_inv z := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv z := by ext <;> simp [hl,hW]
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' c x := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem physicalPacketCarrier_temperate (a b θ frequency : ℝ) :
    Function.HasTemperateGrowth (fun z : ℝ × ℝ =>
      Complex.exp ((frequency*((z.2-b)-θ*(z.1-a)):ℝ)*Complex.I)) := by
  have hx : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact Function.HasTemperateGrowth.comp (g := fun t : ℝ => Complex.exp (t * Complex.I)) OAI.hasTemperateGrowth_exp_mul_I (by fun_prop)

def physicalPlanarPacket (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℝ × ℝ =>
    Complex.exp ((frequency*((z.2-b)-θ*(z.1-a)):ℝ)*Complex.I))
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W θ hl hW) f).compSubConstCLM ℂ (a,b))

theorem physicalPlanarPacket_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a b l W θ frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (z : ℝ × ℝ) :
    physicalPlanarPacket f a b l W θ frequency hl hW z =
      Complex.exp ((frequency*((z.2-b)-θ*(z.1-a)):ℝ)*Complex.I)*
        f ((z.1-a)/l,((z.2-b)-θ*(z.1-a))/W) := by
  rw [physicalPlanarPacket,SchwartzMap.smulLeftCLM_apply_apply
    (physicalPacketCarrier_temperate a b θ frequency)]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSliceFourierBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product-Lebesgue Fourier transforms and transverse partial transforms
of general planar Schwartz functions. The phase is `exp(-2πi(xξ+yη))`. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def planarFourier (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) : ℂ :=
  ∫ z, Real.fourierChar (-(z.1 * frequency.1 + z.2 * frequency.2)) • f z
    ∂volume.prod volume

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PlanarSliceFourierAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript uses angular frequencies in `exp(iηy)`, whereas
mathlib's Fourier transform uses `exp(-2πi xξ)`. These definitions and
identities keep the conversion explicit. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

def planarAngularFourier (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) : ℂ :=
  planarFourier f (frequency.1 / (2 * Real.pi), frequency.2 / (2 * Real.pi))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PlanarSliceFourierDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation of a general planar Schwartz function has
the Fourier multiplier `2π i η`. Consequently every scaled covariant
vertical jet used in the packet construction preserves spectral zeros.
The proof uses one-dimensional differentiation and product Fubini, so
it does not impose a tensor decomposition on the planar packet. -/

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem planarFourier_integrand_integrable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Real.fourierChar (-(z.1 * frequency.1 + z.2 * frequency.2)) • f z)
      (volume.prod volume) := by
  apply f.integrable.norm.mono'
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      f.continuous).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Circle.norm_smul]
    exact le_rfl

theorem planarFourier_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (frequency : ℝ × ℝ) :
    planarFourier (c • f : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      c * planarFourier f frequency := by
  unfold planarFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [smul_apply, Circle.smul_def, smul_eq_mul]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal derivatives of general modulated packets. Uniform bounds
use precisely the dimensionless carrier and slope restrictions. -/

noncomputable section
namespace LipschitzHilbert

def planarHorizontalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.evalCLM ℂ (ℝ × ℝ) ℂ (1,0) (SchwartzMap.fderivCLM ℂ (ℝ × ℝ) ℂ f)

@[simp] theorem planarHorizontalDerivative_apply (f : SchwartzMap (ℝ × ℝ) ℂ) (z : ℝ × ℝ) :
    planarHorizontalDerivative f z = fderiv ℝ f z (1,0) := rfl

theorem modulatedPlanarSlice_horizontal_hasDerivAt (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y : ℝ) (hl : l ≠ 0) (x : ℝ) :
    HasDerivAt (modulatedPlanarSlice f a cy l W delta frequency y hl)
      (((frequency*delta:ℝ):ℂ)*Complex.I*modulatedPlanarSlice f a cy l W delta frequency y hl x +
        ((1/l:ℝ):ℂ)*modulatedPlanarSlice (planarHorizontalDerivative f) a cy l W delta frequency y hl x +
        ((delta/W:ℝ):ℂ)*modulatedPlanarSlice (planarVerticalDerivative f) a cy l W delta frequency y hl x) x := by
  have hg : HasDerivAt (fun t : ℝ => ((t-a)/l,(y-cy+delta*(t-a))/W)) (1/l,delta/W) x := by
    simpa only [id_eq, mul_one, zero_add] using
      (((hasDerivAt_id x).sub_const a).div_const l).prodMk
      ((((hasDerivAt_id x).sub_const a).const_mul delta).const_add (y-cy) |>.div_const W)
  have hf := (f.hasFDerivAt ((x-a)/l,(y-cy+delta*(x-a))/W)).comp_hasDerivAt x hg
  have hc := ((((((hasDerivAt_id x).sub_const a).const_mul delta).const_add
    (y-cy)).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  have h := hc.mul hf
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · beta_reduce
    exact modulatedPlanarSlice_apply f a cy l W delta frequency y hl t
  · simp only [modulatedPlanarSlice_apply,planarHorizontalDerivative_apply,
      planarVerticalDerivative_apply,Function.comp_apply,id_eq]
    have hv : (1/l,delta/W) = (1/l:ℝ) • ((1,0):ℝ × ℝ) + (delta/W:ℝ) • ((0,1):ℝ × ℝ) := by
      ext <;> simp
    rw [hv, map_add, map_smul, map_smul]
    simp only [Complex.real_smul]
    push_cast
    ring

theorem modulatedPlanarSlice_derivative_bound (f : SchwartzMap (ℝ × ℝ) ℂ)
    (a cy l W delta frequency y C M : ℝ) (hl : 0 < l) (n : ℕ)
    (hC : 0 ≤ C) (hshear : |delta*l/W| ≤ 1) (hcarrier : |frequency*delta*l| ≤ M)
    (hf : ∀ z, ‖f z‖ ≤ C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2))
    (hx : ∀ z, ‖planarHorizontalDerivative f z‖ ≤
      C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2))
    (hy : ∀ z, ‖planarVerticalDerivative f z‖ ≤
      C*(lineEnvelope 0 1 (2*n) z.1*lineEnvelope 0 1 (2*n) z.2)) (x : ℝ) :
    ‖deriv (modulatedPlanarSlice f a cy l W delta frequency y hl.ne') x‖ ≤
      ((M+2)*2^n*C/l)*(lineEnvelope a l n x*lineEnvelope cy W n y) := by
  let E := lineEnvelope a l n x*lineEnvelope cy W n y
  have hE : 0 ≤ E := mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hb := modulatedPlanarSlice_envelope f a cy l W delta frequency y C hl.ne' n hC hshear hf x
  have hbx := modulatedPlanarSlice_envelope (planarHorizontalDerivative f)
    a cy l W delta frequency y C hl.ne' n hC hshear hx x
  have hby := modulatedPlanarSlice_envelope (planarVerticalDerivative f)
    a cy l W delta frequency y C hl.ne' n hC hshear hy x
  have hM : 0 ≤ M := (abs_nonneg _).trans hcarrier
  have hc : |frequency*delta| ≤ M/l := by
    apply (le_div_iff₀ hl).mpr
    simpa only [abs_mul, abs_of_pos hl, mul_assoc] using hcarrier
  have hs : |delta/W| ≤ 1/l := by
    apply (le_div_iff₀ hl).mpr
    have heq : |delta/W| * l = |delta*l/W| := by
      simp only [abs_div, abs_mul, abs_of_pos hl]
      ring
    rw [heq]
    exact hshear
  rw [(modulatedPlanarSlice_horizontal_hasDerivAt f a cy l W delta frequency y hl.ne' x).deriv]
  calc
    _ ≤ ‖((frequency*delta:ℝ):ℂ)*Complex.I*modulatedPlanarSlice f a cy l W delta frequency y hl.ne' x‖ +
        ‖((1/l:ℝ):ℂ)*modulatedPlanarSlice (planarHorizontalDerivative f) a cy l W delta frequency y hl.ne' x‖ +
        ‖((delta/W:ℝ):ℂ)*modulatedPlanarSlice (planarVerticalDerivative f) a cy l W delta frequency y hl.ne' x‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = |frequency*delta| * ‖modulatedPlanarSlice f a cy l W delta frequency y hl.ne' x‖ +
        (1/l)*‖modulatedPlanarSlice (planarHorizontalDerivative f) a cy l W delta frequency y hl.ne' x‖ +
        |delta/W| * ‖modulatedPlanarSlice (planarVerticalDerivative f) a cy l W delta frequency y hl.ne' x‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,one_mul,
        abs_of_pos (one_div_pos.mpr hl), abs_mul, mul_assoc]
    _ ≤ (M/l)*((2^n*C)*E)+(1/l)*((2^n*C)*E)+(1/l)*((2^n*C)*E) := by
      apply add_le_add
      · exact add_le_add (mul_le_mul hc hb (norm_nonneg _) (div_nonneg hM hl.le))
          (mul_le_mul_of_nonneg_left hbx (by positivity))
      · exact mul_le_mul hs hby (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [E]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform profile constants for the first three raw waves. Scaling a
covariant derivative costs only the square of its dimensionless width. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem planarVerticalDerivative_smul (c : ℂ) (f : SchwartzMap (ℝ × ℝ) ℂ) :
    planarVerticalDerivative (c • f) = c • planarVerticalDerivative f := by
  unfold planarVerticalDerivative
  rw [map_smul, map_smul]

theorem planarHorizontalDerivative_smul (c : ℂ) (f : SchwartzMap (ℝ × ℝ) ℂ) :
    planarHorizontalDerivative (c • f) = c • planarHorizontalDerivative f := by
  unfold planarHorizontalDerivative
  rw [map_smul, map_smul]

def planarVerticalJet (f : SchwartzMap (ℝ × ℝ) ℂ) (i : Fin 3) : SchwartzMap (ℝ × ℝ) ℂ :=
  if i = 0 then f else if i = 1 then planarVerticalDerivative f else
    planarVerticalDerivative (planarVerticalDerivative f)

theorem planarProfileJet_eq (f : SchwartzMap (ℝ × ℝ) ℂ) (ratio : ℝ) (i : Fin 3) :
    planarProfileJet f ratio i = (ratio:ℂ)^i.val • planarVerticalJet f i := by
  fin_cases i
  · simp [planarProfileJet,planarVerticalJet]
  · simp [planarProfileJet,planarVerticalJet]
  · change (ratio:ℂ) • planarVerticalDerivative ((ratio:ℂ) • planarVerticalDerivative f) =
      (ratio:ℂ)^2 • planarVerticalDerivative (planarVerticalDerivative f)
    rw [planarVerticalDerivative_smul,smul_smul,pow_two]

def planarProfileConstant (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) : ℝ :=
  ∑ i : Fin 3, (planarEnvelopeConstant (planarVerticalJet f i) n +
    planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f i)) n +
    planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f i)) n)

theorem planarProfileConstant_pos (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) :
    0 < planarProfileConstant f n := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  exact add_pos (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
    (planarEnvelopeConstant_pos _ _)

theorem planar_profile_base_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (i : Fin 3) :
    ∀ z, ‖planarVerticalJet f i z‖ ≤ planarProfileConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  intro z
  apply (planar_schwartz_envelope _ n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => planarEnvelopeConstant (planarVerticalJet f j) n +
      planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f j)) n +
      planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f j)) n)
    (fun j _ => (add_pos
      (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
      (planarEnvelopeConstant_pos _ _)).le) (Finset.mem_univ i)
  change _ ≤ planarProfileConstant f n at h
  have h1 := planarEnvelopeConstant_pos (planarHorizontalDerivative (planarVerticalJet f i)) n
  have h2 := planarEnvelopeConstant_pos (planarVerticalDerivative (planarVerticalJet f i)) n
  exact (by linarith : planarEnvelopeConstant (planarVerticalJet f i) n ≤ planarProfileConstant f n)

theorem planar_profile_horizontal_base_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (i : Fin 3) :
    ∀ z, ‖planarHorizontalDerivative (planarVerticalJet f i) z‖ ≤ planarProfileConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  intro z
  apply (planar_schwartz_envelope _ n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => planarEnvelopeConstant (planarVerticalJet f j) n +
      planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f j)) n +
      planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f j)) n)
    (fun j _ => (add_pos
      (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
      (planarEnvelopeConstant_pos _ _)).le) (Finset.mem_univ i)
  change _ ≤ planarProfileConstant f n at h
  have h1 := planarEnvelopeConstant_pos (planarVerticalJet f i) n
  have h2 := planarEnvelopeConstant_pos (planarVerticalDerivative (planarVerticalJet f i)) n
  linarith

theorem planar_profile_vertical_base_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (i : Fin 3) :
    ∀ z, ‖planarVerticalDerivative (planarVerticalJet f i) z‖ ≤ planarProfileConstant f n *
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  intro z
  apply (planar_schwartz_envelope _ n z).trans
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => planarEnvelopeConstant (planarVerticalJet f j) n +
      planarEnvelopeConstant (planarHorizontalDerivative (planarVerticalJet f j)) n +
      planarEnvelopeConstant (planarVerticalDerivative (planarVerticalJet f j)) n)
    (fun j _ => (add_pos
      (add_pos (planarEnvelopeConstant_pos _ _) (planarEnvelopeConstant_pos _ _))
      (planarEnvelopeConstant_pos _ _)).le) (Finset.mem_univ i)
  change _ ≤ planarProfileConstant f n at h
  have h1 := planarEnvelopeConstant_pos (planarVerticalJet f i) n
  have h2 := planarEnvelopeConstant_pos (planarHorizontalDerivative (planarVerticalJet f i)) n
  linarith

theorem planar_profile_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (ratio R : ℝ)
    (hR : 1 ≤ R) (hr : |ratio| ≤ R) (i : Fin 3) (z : ℝ × ℝ) :
    ‖planarProfileJet f ratio i z‖ ≤ (R^2*planarProfileConstant f n)*
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  rw [planarProfileJet_eq,smul_apply,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hp : |ratio|^i.val ≤ R^2 := (pow_le_pow_left₀ (abs_nonneg _) hr _).trans
    (pow_le_pow_right₀ hR (by omega))
  have hb := planar_profile_base_envelope f n i z
  have h := mul_le_mul hp hb (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using h

theorem planar_profile_horizontal_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (ratio R : ℝ)
    (hR : 1 ≤ R) (hr : |ratio| ≤ R) (i : Fin 3) (z : ℝ × ℝ) :
    ‖planarHorizontalDerivative (planarProfileJet f ratio i) z‖ ≤ (R^2*planarProfileConstant f n)*
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  rw [planarProfileJet_eq,planarHorizontalDerivative_smul,smul_apply,norm_smul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs]
  have hp : |ratio|^i.val ≤ R^2 := (pow_le_pow_left₀ (abs_nonneg _) hr _).trans
    (pow_le_pow_right₀ hR (by omega))
  have hb := planar_profile_horizontal_base_envelope f n i z
  have h := mul_le_mul hp hb (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using h

theorem planar_profile_vertical_envelope (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ) (ratio R : ℝ)
    (hR : 1 ≤ R) (hr : |ratio| ≤ R) (i : Fin 3) (z : ℝ × ℝ) :
    ‖planarVerticalDerivative (planarProfileJet f ratio i) z‖ ≤ (R^2*planarProfileConstant f n)*
      (lineEnvelope 0 1 n z.1*lineEnvelope 0 1 n z.2) := by
  rw [planarProfileJet_eq,planarVerticalDerivative_smul,smul_apply,norm_smul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs]
  have hp : |ratio|^i.val ≤ R^2 := (pow_le_pow_left₀ (abs_nonneg _) hr _).trans
    (pow_le_pow_right₀ hR (by omega))
  have hb := planar_profile_vertical_base_envelope f n i z
  have h := mul_le_mul hp hb (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_UniformPlanarRawBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common finite collection of Schwartz seminorm bounds gives a
common raw-kernel constant for an entire packet family. The constant
is explicit and independent of the particular planar profile. -/

noncomputable section

namespace LipschitzHilbert

/-- The concrete general planar raw kernels and their horizontal
derivatives obey uniform product-envelope bounds whenever the profile
constant is uniformly bounded. The exact amplitude is
`(2^n*Cprof)*(M+2)*R^2`, and differentiation costs exactly `1/l`. -/
theorem uniform_planar_raw_bounds (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ)
    (Cprof : ℝ) (hprof : planarProfileConstant f (2 * n) ≤ Cprof)
    (a cy l W delta frequency scale R M : ℝ) (hl : 0 < l)
    (hR : 1 ≤ R) (hr : |scale / W| ≤ R) (hM : 0 ≤ M)
    (hs : |delta * l / W| ≤ 1) (hc : |frequency * delta * l| ≤ M)
    (i : Fin 3) (y x : ℝ) :
    ‖modulatedPlanarJet f a cy l W delta frequency scale y hl.ne' i x‖ ≤
      ((2 ^ n * Cprof) * (M + 2) * R ^ 2) *
        (lineEnvelope a l n x * lineEnvelope cy W n y) ∧
    ‖deriv (modulatedPlanarJet f a cy l W delta frequency scale y hl.ne' i) x‖ ≤
      (((2 ^ n * Cprof) * (M + 2) * R ^ 2) / l) *
        (lineEnvelope a l n x * lineEnvelope cy W n y) := by
  have hCprof : 0 ≤ Cprof := (planarProfileConstant_pos f (2 * n)).le.trans hprof
  let B := R ^ 2 * Cprof
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg R) hCprof
  have hcoefficient : R ^ 2 * planarProfileConstant f (2 * n) ≤ B :=
    mul_le_mul_of_nonneg_left hprof (sq_nonneg R)
  have dominate (g : ℝ × ℝ → ℂ)
      (hg : ∀ z, ‖g z‖ ≤ (R ^ 2 * planarProfileConstant f (2 * n)) *
        (lineEnvelope 0 1 (2 * n) z.1 * lineEnvelope 0 1 (2 * n) z.2)) :
      ∀ z, ‖g z‖ ≤ B *
        (lineEnvelope 0 1 (2 * n) z.1 * lineEnvelope 0 1 (2 * n) z.2) := by
    intro z
    exact (hg z).trans (mul_le_mul_of_nonneg_right hcoefficient
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have hbase := dominate _ (planar_profile_envelope f (2 * n) (scale / W) R hR hr i)
  have hdx := dominate _ (planar_profile_horizontal_envelope f (2 * n)
    (scale / W) R hR hr i)
  have hdy := dominate _ (planar_profile_vertical_envelope f (2 * n)
    (scale / W) R hR hr i)
  have hb := modulatedPlanarSlice_envelope (planarProfileJet f (scale / W) i)
    a cy l W delta frequency y B hl.ne' n hB hs hbase x
  have hd := modulatedPlanarSlice_derivative_bound (planarProfileJet f (scale / W) i)
    a cy l W delta frequency y B M hl n hB hs hc hbase hdx hdy x
  constructor
  · change ‖modulatedPlanarSlice (planarProfileJet f (scale / W) i)
        a cy l W delta frequency y hl.ne' x‖ ≤ _
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    have hfactor : 1 ≤ M + 2 := by linarith
    calc
      2 ^ n * B ≤ (2 ^ n * B) * (M + 2) :=
        le_mul_of_one_le_right (by positivity) hfactor
      _ = (2 ^ n * Cprof) * (M + 2) * R ^ 2 := by dsimp [B]; ring
  · change ‖deriv (modulatedPlanarSlice (planarProfileJet f (scale / W) i)
        a cy l W delta frequency y hl.ne') x‖ ≤ _
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B]
    ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_VariationPacketL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of packet partial sums is bounded by the sum of packet
norms. This is used for the long-scale spatial oscillation and error terms. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

def packetPartialSum {E : Type*} [AddCommMonoid E] {N : ℕ}
    (f : Fin N → E) (n : ℕ) : E := ∑ j, if j.val < n then f j else 0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hilbert duality for coefficients defined by actual analyzing
integrals. The self-pairing uses the same selected synthesizing packets. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ] [Fintype κ]

def analyzingCoefficient (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (i : σ) :
    EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ((area i)⁻¹ : ℂ) * ∫ z, g z k * conj (wave i k z) ∂μ)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual center-box assignment on a reference line and exact grouping
of the finite Schwartz synthesis. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def packetBoxIndex (u y r W x z : ℝ) : ℤ × ℤ :=
  (⌊(x - u) / r⌋, ⌊(z - y) / W⌋)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ShortPacketBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite decomposition of the short-scale synthesis into its actual
center boxes. Empty fibers are retained and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def centerBoxIndex {σ : Type*} {ι : σ → Type*} (X Z : ∀ j, ι j → ℝ)
    (u y r W : ℝ) (j : σ) (i : ι j) : ℤ × ℤ :=
  packetBoxIndex u y r W (X j i) (Z j i)

abbrev ShortBoxFiber {σ : Type*} {ι : σ → Type*}
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ) (b : ℤ × ℤ) (j : σ) :=
  {i : ι j // len j ≤ r ∧ index j i = b}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar dyadic packet family and its restriction to an actual
short-packet center box. This restriction carries no coefficient budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

structure PlanarPacketFamily (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  topLength : ℝ
  width : ℝ
  constant : ℝ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  constant_pos : 0 < constant
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  wave : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ
  wave_measurable : ∀ j i k, Measurable (fun z : ℝ × ℝ => wave j i k z.1 z.2)
  wave_bound : ∀ j i k y x, ‖wave j i k y x‖ ≤ constant *
    (lineEnvelope (baseX + (topLength/(2:ℝ)^j.val) * (site j i).1)
      (topLength/(2:ℝ)^j.val) 3 x *
     lineEnvelope (baseZ + width * (site j i).2) width 3 y)

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def length (P : PlanarPacketFamily N κ ι) (j : Fin N) : ℝ := P.topLength / (2:ℝ)^j.val

def centerX (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseX + P.length j * (P.site j i).1

def centerZ (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseZ + P.width * (P.site j i).2

theorem length_pos (P : PlanarPacketFamily N κ ι) (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def selectedWave (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (s : Σ j, ι j) (k : κ) (z : ℝ × ℝ) : ℂ :=
  if v z ≤ d s.1 then P.wave s.1 s.2 k z.1 z.2 else 0

def mainCoefficient (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (i : ι j) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
    (P.selectedWave d v) g ⟨j,i⟩

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLatticePacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual general planar packets on translated sheared lattices form
the canonical planar packet family. Only the bookkeeping sites are
quantized: the raw waves retain their original centers and profiles. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

/-- Concrete local packet data. These are geometric, seminorm and
dimensionless scale bounds, with no coefficient or concentration premise. -/
structure SourceLatticePacket (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  topLength : ℝ
  width : ℝ
  scale : ℝ
  ratioBound : ℝ
  carrierBound : ℝ
  profileBound : ℝ
  order : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  profileBound_pos : 0 < profileBound
  order_ge_three : 3 ≤ order
  ratioBound_ge_one : 1 ≤ ratioBound
  scale_bound : |scale / width| ≤ ratioBound
  carrierBound_nonneg : 0 ≤ carrierBound
  originX : Fin N → ℝ
  originZ : Fin N → ℝ
  /-- Physical packet slope minus the reference-line slope. -/
  rowSlope : Fin N → ℝ
  frequency : κ → ℝ
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  profile : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ
  profile_bound : ∀ j u k, planarProfileConstant (profile j u k) (2 * order) ≤ profileBound
  shear_bound : ∀ j, |rowSlope j * (topLength / (2 : ℝ) ^ j.val) / width| ≤ 1
  carrier_bound : ∀ j k,
    |frequency k * rowSlope j * (topLength / (2 : ℝ) ^ j.val)| ≤ carrierBound

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def length (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val

theorem length_pos (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def actualX (j : Fin N) (u : ι j) : ℝ :=
  P.originX j + P.length j * (P.site j u).1

def actualZ (j : Fin N) (u : ι j) : ℝ :=
  P.originZ j + P.rowSlope j * P.length j * (P.site j u).1 + P.width * (P.site j u).2

def snappedSite (j : Fin N) (u : ι j) : ℤ × ℤ :=
  snappedLatticeSite (P.originX j) (P.originZ j) (P.length j) P.width (P.rowSlope j)
    (P.site j u)

theorem snappedSite_injective (j : Fin N) : Function.Injective (P.snappedSite j) :=
  (snappedLatticeSite_injective _ _ _ _ _).comp (P.site_injective j)

def raw (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) : SchwartzMap ℝ ℂ :=
  modulatedPlanarJet (P.profile j u k) (P.actualX j u) (P.actualZ j u)
    (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale y (P.length_pos j).ne' i

def amplitude : ℝ :=
  (2 ^ P.order * P.profileBound) * (P.carrierBound + 2) * P.ratioBound ^ 2

def constant : ℝ := P.amplitude * 3 ^ (2 * P.order)

theorem amplitude_pos : 0 < P.amplitude := by
  have hR : 0 < P.ratioBound := lt_of_lt_of_le (by norm_num) P.ratioBound_ge_one
  have hM : 0 < P.carrierBound + 2 := by linarith [P.carrierBound_nonneg]
  exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) P.profileBound_pos) hM)
    (sq_pos_of_pos hR)

theorem constant_pos : 0 < P.constant :=
  mul_pos P.amplitude_pos (pow_pos (by norm_num) _)

theorem raw_shear_bound (j : Fin N) : |(-P.rowSlope j) * P.length j / P.width| ≤ 1 := by
  simpa only [length, neg_mul, neg_div, abs_neg] using P.shear_bound j

theorem raw_carrier_bound (j : Fin N) (k : κ) :
    |P.frequency k * (-P.rowSlope j) * P.length j| ≤ P.carrierBound := by
  simpa only [length, mul_neg, neg_mul, abs_neg] using P.carrier_bound j k

theorem raw_bound_actual (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.amplitude *
      (lineEnvelope (P.actualX j u) (P.length j) P.order x *
        lineEnvelope (P.actualZ j u) P.width P.order y) := by
  exact (uniform_planar_raw_bounds (P.profile j u k) P.order P.profileBound
    (P.profile_bound j u k) (P.actualX j u) (P.actualZ j u) (P.length j) P.width
    (-P.rowSlope j) (P.frequency k) P.scale P.ratioBound P.carrierBound
    (P.length_pos j) P.ratioBound_ge_one P.scale_bound P.carrierBound_nonneg
    (P.raw_shear_bound j) (P.raw_carrier_bound j k) i y x).1

theorem raw_derivative_bound_actual (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.raw i j u k y) x‖ ≤ (P.amplitude / P.length j) *
      (lineEnvelope (P.actualX j u) (P.length j) P.order x *
        lineEnvelope (P.actualZ j u) P.width P.order y) := by
  exact (uniform_planar_raw_bounds (P.profile j u k) P.order P.profileBound
    (P.profile_bound j u k) (P.actualX j u) (P.actualZ j u) (P.length j) P.width
    (-P.rowSlope j) (P.frequency k) P.scale P.ratioBound P.carrierBound
    (P.length_pos j) P.ratioBound_ge_one P.scale_bound P.carrierBound_nonneg
    (P.raw_shear_bound j) (P.raw_carrier_bound j k) i y x).2

theorem snapped_envelope (j : Fin N) (u : ι j) (y x : ℝ) :
    lineEnvelope (P.actualX j u) (P.length j) P.order x *
        lineEnvelope (P.actualZ j u) P.width P.order y ≤
      3 ^ (2 * P.order) *
        (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) P.order x *
          lineEnvelope (P.width * (P.snappedSite j u).2) P.width P.order y) := by
  have h := snappedLatticeSite_envelope (P.originX j) (P.originZ j) (P.length j)
    P.width (P.rowSlope j) x y (P.length_pos j) P.width_pos (P.site j u) P.order P.order
  have hp : (3 : ℝ) ^ P.order * 3 ^ P.order = 3 ^ (2 * P.order) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [actualX, actualZ, snappedSite, hp] using h

theorem raw_bound (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.constant *
      (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) P.order x *
        lineEnvelope (P.width * (P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_bound_actual i j u k y x).trans
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x) P.amplitude_pos.le
  simpa only [constant, mul_assoc] using h

theorem raw_derivative_bound (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.raw i j u k y) x‖ ≤ (P.constant / P.length j) *
      (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) P.order x *
        lineEnvelope (P.width * (P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_derivative_bound_actual i j u k y x).trans
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x)
    (div_nonneg P.amplitude_pos.le (P.length_pos j).le)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [constant]
  ring

theorem raw_bound_three (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.constant *
      (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) 3 x *
        lineEnvelope (P.width * (P.snappedSite j u).2) P.width 3 y) := by
  apply (P.raw_bound i j u k y x).trans
  apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
    (lineEnvelope_antitone _ _ _ P.order_ge_three) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

/-- Canonical sites with base coordinates zero, carrying the original
raw waves at their actual translated sheared lattice centers. -/
def family : PlanarPacketFamily N κ ι where
  baseX := 0
  baseZ := 0
  topLength := P.topLength
  width := P.width
  constant := P.constant
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  constant_pos := P.constant_pos
  site := P.snappedSite
  site_injective := P.snappedSite_injective
  wave := P.raw 0
  wave_measurable := by
    intro j u k
    exact (modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale
      (P.length_pos j).ne' 0).measurable
  wave_bound := by
    intro j u k y x
    simpa only [zero_add, length] using P.raw_bound_three 0 j u k y x

@[simp] theorem family_length (j : Fin N) : P.family.length j = P.length j := rfl

@[simp] theorem family_wave (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    P.family.wave j u k y = P.raw 0 j u k y := rfl

@[simp] theorem family_centerX (j : Fin N) (u : ι j) :
    P.family.centerX j u = P.length j * (P.snappedSite j u).1 := by
  simp only [PlanarPacketFamily.centerX, family_length]
  exact zero_add _

@[simp] theorem family_centerZ (j : Fin N) (u : ι j) :
    P.family.centerZ j u = P.width * (P.snappedSite j u).2 := by
  exact zero_add _

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- The source's local label multiplicity, using half-open intervals
to assign boundary labels unambiguously. -/
def LocalMultiplicity (labels : Finset ι) (slope : ι → ℝ) (d : ℝ) (M : ℕ) : Prop :=
  ∀ a : ℝ, (labels.filter (fun i => a ≤ slope i ∧ slope i < a + d)).card ≤ M

/-- Each scale has its own label assignment, but the same finite set of
slots suffices for all scales. Inactive slots may be represented by an
empty spatial lattice. -/
def slots {J : Type*} {Label : J → Type*} (labels : ∀ j, Finset (Label j))
    {B : ℕ} (hcard : ∀ j, (labels j).card ≤ B) (j : J) : labels j ↪ Fin B := by
  classical
  exact Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hcard j))

/-- Recover the optional label for a slot without choosing any
distinguished label at an empty scale. -/
def labelAtSlot {A : Type*} {B : ℕ} (e : A ↪ Fin B) (b : Fin B) : Option A :=
  if h : ∃ i, e i = b then some h.choose else none

/-- The spatial items retained in one label slot at a fixed scale. -/
def SlotItem {A : Type*} {B : ℕ} (e : A ↪ Fin B) (Item : A → Type*) (b : Fin B) :=
  {p : Sigma Item // e p.1 = b}

/-- Although labels can have overlapping integer sites, one slot never
mixes two labels at a fixed scale. Its original spatial site map is
therefore injective, as required by the packet-family constructor. -/
theorem slotItem_site_injective {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    {Item : A → Type*} (site : ∀ i, Item i → ℤ × ℤ)
    (hsite : ∀ i, Function.Injective (site i)) (b : Fin B) :
    Function.Injective (fun p : SlotItem e Item b => site p.1.1 p.1.2) := by
  rintro ⟨⟨i, u⟩, hi⟩ ⟨⟨j, v⟩, hj⟩ h
  have hij : i = j := e.injective (hi.trans hj.symm)
  subst j
  apply Subtype.ext
  exact congrArg (Sigma.mk i) (hsite i h)

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual source lattices with several labels at each scale split into
the uniformly many slots constructed in `SourceSlopeLabels`. No packets
are inserted at an empty scale. The selected profiles, physical centers,
carrier frequencies and spectra are unchanged. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

/-- Common packet bounds with a finite set of translated lattice labels
at each scale. All bounds are imposed only on labels that are present. -/
structure SourceLabeledLattice (N : ℕ) (κ : Type) (Label : Fin N → Type)
    (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)] where
  topLength : ℝ
  width : ℝ
  scale : ℝ
  ratioBound : ℝ
  carrierBound : ℝ
  profileBound : ℝ
  order : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  profileBound_pos : 0 < profileBound
  order_ge_three : 3 ≤ order
  ratioBound_ge_one : 1 ≤ ratioBound
  scale_bound : |scale / width| ≤ ratioBound
  carrierBound_nonneg : 0 ≤ carrierBound
  labels : ∀ j, Finset (Label j)
  originX : ∀ j, labels j → ℝ
  originZ : ∀ j, labels j → ℝ
  rowSlope : ∀ j, labels j → ℝ
  frequency : κ → ℝ
  site : ∀ j (l : labels j), Item j l → ℤ × ℤ
  site_injective : ∀ j l, Function.Injective (site j l)
  profile : ∀ j (l : labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ
  profile_bound : ∀ j l u k,
    planarProfileConstant (profile j l u k) (2 * order) ≤ profileBound
  shear_bound : ∀ j l, |rowSlope j l * (topLength / (2 : ℝ) ^ j.val) / width| ≤ 1
  carrier_bound : ∀ j l k,
    |frequency k * rowSlope j l * (topLength / (2 : ℝ) ^ j.val)| ≤ carrierBound

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

def length (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val

theorem length_pos (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def actualX (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originX j l + P.length j * (P.site j l u).1

def actualZ (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originZ j l + P.rowSlope j l * P.length j * (P.site j l u).1 +
    P.width * (P.site j l u).2

def raw (i : Fin 3) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ)
    (y : ℝ) : SchwartzMap ℝ ℂ :=
  modulatedPlanarJet (P.profile j l u k) (P.actualX j l u) (P.actualZ j l u)
    (P.length j) P.width (-P.rowSlope j l) (P.frequency k) P.scale y (P.length_pos j).ne' i

def physicalPacket (t : ℝ) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  physicalPlanarPacket (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u + t * P.actualX j l u) (P.length j) P.width
    (t + P.rowSlope j l) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

def constant : ℝ :=
  ((2 ^ P.order * P.profileBound) * (P.carrierBound + 2) * P.ratioBound ^ 2) *
    3 ^ (2 * P.order)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

def slotEmbedding (j : Fin N) : P.labels j ↪ Fin B := SourceSlopeLabels.slots P.labels hcard j

abbrev SlotItem (b : Fin B) (j : Fin N) :=
  SourceSlopeLabels.SlotItem (P.slotEmbedding hcard j) (fun l => Item j l) b

instance slotItemFintype (b : Fin B) (j : Fin N) : Fintype (P.SlotItem hcard b j) := by
  unfold SlotItem SourceSlopeLabels.SlotItem
  infer_instance

/-- The value is used only when the corresponding slot has an item.
Zero is a harmless geometric default when that slot is empty. -/
def slotValue (b : Fin B) (j : Fin N) (f : P.labels j → ℝ) : ℝ :=
  (SourceSlopeLabels.labelAtSlot (P.slotEmbedding hcard j) b).elim 0 f

/-- One genuine translated-lattice family per slot. No hypotheses on a
selector are introduced for missing labels or empty scales. -/
def slotted (b : Fin B) : SourceLatticePacket N κ (P.SlotItem hcard b) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  originX := fun j => P.slotValue hcard b j (P.originX j)
  originZ := fun j => P.slotValue hcard b j (P.originZ j)
  rowSlope := fun j => P.slotValue hcard b j (P.rowSlope j)
  frequency := P.frequency
  site := fun j p => P.site j p.1.1 p.1.2
  site_injective := fun j => SourceSlopeLabels.slotItem_site_injective
    (P.slotEmbedding hcard j) (P.site j) (P.site_injective j) b
  profile := fun j p k => P.profile j p.1.1 p.1.2 k
  profile_bound := fun j p k => P.profile_bound j p.1.1 p.1.2 k
  shear_bound := by
    intro j
    cases h : SourceSlopeLabels.labelAtSlot (P.slotEmbedding hcard j) b with
    | none => simp [slotValue, h]
    | some l => simpa [slotValue, h] using P.shear_bound j l
  carrier_bound := by
    intro j k
    cases h : SourceSlopeLabels.labelAtSlot (P.slotEmbedding hcard j) b with
    | none => simpa [slotValue, h] using P.carrierBound_nonneg
    | some l => simpa [slotValue, h] using P.carrier_bound j l k

@[simp] theorem slotted_length (b : Fin B) (j : Fin N) :
    (P.slotted hcard b).length j = P.length j := rfl

@[simp] theorem slotted_constant (b : Fin B) :
    (P.slotted hcard b).constant = P.constant := rfl

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

structure PacketLatticeData (N : ℕ) (κ : Type) (Label : Fin N → Type)
    (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)] where
  topLength : ℝ
  width : ℝ
  scale : ℝ
  ratioBound : ℝ
  profileBound : ℝ
  order : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  profileBound_pos : 0 < profileBound
  order_ge_three : 3 ≤ order
  ratioBound_ge_one : 1 ≤ ratioBound
  scale_bound : |scale / width| ≤ ratioBound
  labels : ∀ j, Finset (Label j)
  originX : ∀ j, labels j → ℝ
  originZ : ∀ j, labels j → ℝ
  rowSlope : ∀ j, labels j → ℝ
  frequency : κ → ℝ
  site : ∀ j (l : labels j), Item j l → ℤ × ℤ
  site_injective : ∀ j l, Function.Injective (site j l)
  profile : ∀ j (l : labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ
  profile_bound : ∀ j l u k,
    planarProfileConstant (profile j l u k) (2 * order) ≤ profileBound

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def length (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val

theorem length_pos (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def actualX (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originX j l + P.length j * (P.site j l u).1

def actualZ (j : Fin N) (l : P.labels j) (u : Item j l) : ℝ :=
  P.originZ j l + P.rowSlope j l * P.length j * (P.site j l u).1 +
    P.width * (P.site j l u).2

def physicalPacket (t : ℝ) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    SchwartzMap (ℝ × ℝ) ℂ :=
  physicalPlanarPacket (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u + t * P.actualX j l u) (P.length j) P.width
    (t + P.rowSlope j l) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

def referenceLabels (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l ∈ P.labels j,
    P.length j ≤ referenceLength ∧
      |oldSlope + P.rowSlope j ⟨l,h⟩ - newSlope| ≤ cone * w / P.length j)

def referenceOriginalLabel (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) : P.labels j :=
  ⟨l.val, (Finset.mem_filter.mp l.property).1⟩

theorem referenceLabel_bounds (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) :
    P.length j ≤ referenceLength ∧
      |P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
        (oldSlope - newSlope)| ≤ cone * w / P.length j := by
  obtain ⟨h, hshort, hangle⟩ := (Finset.mem_filter.mp l.property).2
  have heq : (⟨l.val,h⟩ : P.labels j) =
      P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l := Subtype.ext rfl
  rw [heq] at hangle
  refine ⟨hshort, ?_⟩
  convert hangle using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

/-- The reference lattice derives both dimensionless bounds from its
cone. No bound on the slopes of the original packet family is used. -/
def referenceFamily (oldSlope newSlope referenceLength cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F / w) : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := F * cone
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := mul_nonneg hF hcone
  labels := P.referenceLabels oldSlope newSlope referenceLength cone w
  originX := fun j l => P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  originZ := fun j l =>
    P.originZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
      (oldSlope - newSlope) * P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  rowSlope := fun j l =>
    P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) + (oldSlope - newSlope)
  frequency := P.frequency
  site := fun j l => P.site j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  site_injective := fun j l => P.site_injective j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile := fun j l => P.profile j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile_bound := fun j l => P.profile_bound j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  shear_bound := by
    intro j l
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    change |(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
      (oldSlope - newSlope)) * P.length j / P.width| ≤ 1
    rw [abs_div, abs_mul, abs_of_pos (P.length_pos j), abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr (((le_div_iff₀ (P.length_pos j)).mp h).trans hwide)
  carrier_bound := by
    intro j l k
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    have hr := (le_div_iff₀ (P.length_pos j)).mp h
    change |P.frequency k * (P.rowSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) +
        (oldSlope - newSlope)) * P.length j| ≤ F * cone
    rw [abs_mul, abs_mul, abs_of_pos (P.length_pos j), mul_assoc]
    calc
      _ ≤ (F / w) * (cone * w) := mul_le_mul (hfrequency k) hr
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F * cone := by field_simp

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

@[simp] theorem referenceFamily_length (j : Fin N) : (Q).length j = P.length j := rfl

@[simp] theorem referenceFamily_actualX (j : Fin N)
    (l : (Q).labels j) (u : Item j l) :
    (Q).actualX j l u = P.actualX j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := rfl

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SincMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual even sinc-product mask from (src-8), including its
quadratic approximation to one and the stated logarithmic-scale error. -/

noncomputable section

namespace LipschitzHilbert

def sincProductMask (n : ℕ) (x y : ℝ) : ℝ := (Real.sinc x*Real.sinc y)^(2*n)

theorem sincProductMask_nonneg (n : ℕ) (x y : ℝ) : 0 ≤ sincProductMask n x y := by
  unfold sincProductMask
  exact Even.pow_nonneg (even_two_mul n) _

theorem sincProductMask_le_one (n : ℕ) (x y : ℝ) : sincProductMask n x y ≤ 1 := by
  have h : |Real.sinc x*Real.sinc y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sinc_le_one x) (Real.abs_sinc_le_one y)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hp := pow_le_pow_left₀ (abs_nonneg _) h (2*n)
  exact (le_abs_self _).trans (by simpa only [sincProductMask, abs_pow, one_pow] using hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMaskApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

def topSincMask (L A x y : ℝ) : ℝ :=
  sincProductMask ⌈L⌉₊ (x/(L^A)) (y/(L^A))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

def topProfile (D : ℝ) (z : ℝ × ℝ) : ℝ := (1 + (|z.1| + |z.2|)) ^ (-D)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

def mask (T : SlopeBox) (L A : ℝ) (z : ℝ × ℝ) : ℝ :=
  topSincMask L A (T.horizontal z) (T.transverse z)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopAreaAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized intersection averages and top-area weights. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.SlopeBox

def area (T : SlopeBox) : ℝ := T.length*T.width

theorem area_pos (T : SlopeBox) : 0 < T.area := mul_pos T.length_pos T.width_pos

def areaWeight (T : SlopeBox) : ℝ≥0 := ⟨T.area,T.area_pos.le⟩

@[simp] theorem coe_areaWeight (T : SlopeBox) : (T.areaWeight:ℝ) = T.area := rfl

@[simp] theorem ennreal_areaWeight (T : SlopeBox) : (T.areaWeight:ℝ≥0∞) =
    ENNReal.ofReal T.area := ENNReal.coe_nnreal_eq T.areaWeight

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityKeepers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing-length selection of the actual spatial and angular density
tests. Keeper witnesses are disjoint even when their spatial boxes overlap. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

def densitySpatialBox (T : SlopeBox) (K : ℝ) : Set (ℝ×ℝ) :=
  {z | |z.1-T.x| ≤ K*T.length ∧
    |(z.2-T.y)-T.slope*(z.1-T.x)| ≤ K*T.width}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityScaledForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular grid has physical scale w/topLength. Keeping that scale
explicit allows arbitrary vertical band width and dyadic source lengths. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

def scaledAngularCell (unit : ℝ) (q k j : ℤ) : Set ℝ :=
  {s | s/unit ∈ DyadicLineGrid.cell q k j}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density kernel has a quantitative tail outside a dilated slope
box. This turns a weighted density test into the unweighted witness used
by the finite keeper construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert
namespace SlopeBox

def densityKernel (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) : ℝ :=
  (1+T.radius z)^(-D)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteBandDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation commutes with the actual finite band sums.
The covariant derivative uses the same carrier in every band of a fixed
coordinate, so no carrier-frequency factor is lost. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

def scalarBandPartial {N : ℕ} (F : Fin N → ℝ → ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  ∑ j, if j.val < n then F j y else 0

def bandIntervalSignal {N : ℕ} {κ : Type*} (F : Fin N → κ → ℝ → ℂ)
    (a b : ℕ) (y : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => scalarBandPartial (fun j => F j k) b y -
    scalarBandPartial (fun j => F j k) a y)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketVectorDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-free synthesis and derivative estimates on a reference line.
The multiplication of a Hilbert coefficient by a packet is componentwise. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem diagonal_packet_norm {κ : Type*} [Fintype κ]
    (c : EuclideanSpace ℂ κ) (v : κ → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hv : ∀ k, ‖v k‖ ≤ K) :
    ‖WithLp.toLp 2 (fun k => c k * v k)‖ ≤ K * ‖c‖ := by
  have hs : ‖WithLp.toLp 2 (fun k => c k * v k)‖ ^ 2 ≤ (K * ‖c‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    change ‖c k * v k‖ ^ 2 ≤ K ^ 2 * ‖c k‖ ^ 2
    rw [norm_mul, mul_pow, mul_comm (K ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hv k) 2)
      (sq_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => c k * v k)),
    mul_nonneg hK (norm_nonneg c)]

def vectorPacketSynthesis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => packetSynthesis (fun i => c i k) (fun i => f i k) x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingCoefficientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-independent bound on one analyzing coefficient, obtained
from the common scalar envelope of its diagonal multiplier. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem analyzingCoefficient_norm_le {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (area : σ → ℝ) (wave : σ → κ → Ω → ℂ)
    (g : Ω → EuclideanSpace ℂ κ) (i : σ) (W : Ω → ℝ)
    (ha : 0 < area i) (hW : Integrable W μ) (hW0 : ∀ z, 0 ≤ W z)
    (hint : ∀ k, Integrable (fun z => g z k * conj (wave i k z)) μ)
    (hg : ∀ z, ‖g z‖ ≤ 1) (hw : ∀ k z, ‖wave i k z‖ ≤ W z) :
    ‖analyzingCoefficient μ area wave g i‖ ≤ (area i)⁻¹ * ∫ z, W z ∂μ := by
  let F : Ω → EuclideanSpace ℂ κ := fun z =>
    WithLp.toLp 2 (fun k => g z k * conj (wave i k z))
  have hF : Integrable F μ := integrable_piLp_iff.mpr hint
  have hbound (z : Ω) : ‖F z‖ ≤ W z := by
    have h := diagonal_packet_norm (g z) (fun k => conj (wave i k z)) (hW0 z)
      (fun k => by simpa only [RCLike.norm_conj] using hw k z)
    exact h.trans ((mul_le_mul_of_nonneg_left (hg z) (hW0 z)).trans_eq (mul_one _))
  have heq : analyzingCoefficient μ area wave g i = (area i)⁻¹ • ∫ z, F z ∂μ := by
    ext k
    change ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (wave i k z) ∂μ) =
      (area i)⁻¹ • (∫ z, F z ∂μ) k
    rw [eval_integral_piLp hint, Complex.real_smul, Complex.ofReal_inv]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
  exact (norm_integral_le_integral_norm F).trans (integral_mono hF.norm hW hbound)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarCoefficientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform pointwise normalization of the actual main coefficients,
with no dependence on the number of Hilbert coordinates. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert
namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def envelope (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) (z : ℝ × ℝ) : ℝ :=
  P.constant * (lineEnvelope (P.centerZ j i) P.width 1 z.1 *
    lineEnvelope (P.centerX j i) (P.length j) 1 z.2)

theorem envelope_nonneg (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j)
    (z : ℝ × ℝ) : 0 ≤ P.envelope j i z :=
  mul_nonneg P.constant_pos.le (mul_nonneg (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _))

theorem envelope_integrable (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) :
    Integrable (P.envelope j i) :=
  ((integrable_lineEnvelope_one _ _ P.width_pos).mul_prod
    (integrable_lineEnvelope_one _ _ (P.length_pos j))).const_mul P.constant

theorem integral_envelope (P : PlanarPacketFamily N κ ι) (j : Fin N) (i : ι j) :
    (∫ z, P.envelope j i z) = (P.constant * Real.pi^2) * (P.length j * P.width) := by
  unfold envelope
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul,
    integral_lineEnvelope_one _ _ P.width_pos,
    integral_lineEnvelope_one _ _ (P.length_pos j)]
  ring

theorem selectedWave_bound (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (s : Σ j, ι j) (k : κ) (z : ℝ × ℝ) :
    ‖P.selectedWave d v s k z‖ ≤ P.envelope s.1 s.2 z := by
  unfold selectedWave
  split_ifs
  · apply (P.wave_bound s.1 s.2 k z.1 z.2).trans
    unfold envelope centerX centerZ
    apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
    rw [mul_comm (lineEnvelope _ _ 1 z.1)]
    exact mul_le_mul (lineEnvelope_antitone _ _ _ (by decide : 1 ≤ 3))
      (lineEnvelope_antitone _ _ _ (by decide : 1 ≤ 3))
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  · simpa only [norm_zero] using P.envelope_nonneg s.1 s.2 z

theorem mainCoefficient_norm (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (i : ι j) :
    ‖P.mainCoefficient d v g j i‖ ≤ P.constant * Real.pi^2 := by
  have hm (k : κ) : Measurable (P.selectedWave d v ⟨j,i⟩ k) :=
    Measurable.ite (measurableSet_le hv measurable_const) (P.wave_measurable j i k) measurable_const
  have hint (k : κ) :
      Integrable (fun z => g z k * conj (P.selectedWave d v ⟨j,i⟩ k z)) := by
    have hgm : Measurable (fun z => g z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    apply (P.envelope_integrable j i).mono'
      (hgm.mul (continuous_star.measurable.comp (hm k))).aestronglyMeasurable
    filter_upwards [] with z
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_star]
    have hgk := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
    exact (mul_le_mul_of_nonneg_right hgk (norm_nonneg _)).trans
      (by simpa only [one_mul] using P.selectedWave_bound d v ⟨j,i⟩ k z)
  have h := analyzingCoefficient_norm_le volume
    (fun s : Σ j, ι j => P.length s.1 * P.width) (P.selectedWave d v) g ⟨j,i⟩
    (P.envelope j i) (mul_pos (P.length_pos j) P.width_pos)
    (P.envelope_integrable j i) (P.envelope_nonneg j i) hint hg1
    (P.selectedWave_bound d v ⟨j,i⟩)
  change ‖P.mainCoefficient d v g j i‖ ≤ _ at h
  rw [P.integral_envelope] at h
  have hz : P.length j * P.width ≠ 0 := (mul_pos (P.length_pos j) P.width_pos).ne'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  symm
  calc
    _ = (P.constant * Real.pi^2) * ((P.length j * P.width)⁻¹ * (P.length j * P.width)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hz, mul_one]

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_LinePacketFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite packet data on a reference line, with local coefficient
budgets kept explicit. No concentration or synthesis estimate is part of
the data. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

structure LinePacketFamily (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  baseX : ℝ
  baseZ : ℝ
  topLength : ℝ
  width : ℝ
  lineY : ℝ
  constant : ℝ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  constant_pos : 0 < constant
  coeff : ∀ j, ι j → EuclideanSpace ℂ κ
  wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  coeff_norm : ∀ j i, ‖coeff j i‖ ≤ 1
  wave_bound : ∀ j i k x, ‖wave j i k x‖ ≤ constant *
    (lineEnvelope (baseX + (topLength / (2 : ℝ) ^ j.val) * (site j i).1)
      (topLength / (2 : ℝ) ^ j.val) 3 x *
      lineEnvelope (baseZ + width * (site j i).2) width 2 lineY)
  deriv_bound : ∀ j i k x, ‖deriv (wave j i k) x‖ ≤
    (constant / (topLength / (2 : ℝ) ^ j.val)) *
    (lineEnvelope (baseX + (topLength / (2 : ℝ) ^ j.val) * (site j i).1)
      (topLength / (2 : ℝ) ^ j.val) 3 x *
      lineEnvelope (baseZ + width * (site j i).2) width 2 lineY)

namespace LinePacketFamily

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def length (P : LinePacketFamily N κ ι) (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val
def centerX (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseX + P.length j * (P.site j i).1
def centerZ (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) : ℝ :=
  P.baseZ + P.width * (P.site j i).2
def packets (P : LinePacketFamily N κ ι) (j : Fin N) (k : κ) : SchwartzMap ℝ ℂ :=
  packetSynthesis (fun i => P.coeff j i k) (fun i => P.wave j i k)
def shortPackets (P : LinePacketFamily N κ ι) (r : ℝ) (j : Fin N) (k : κ) : SchwartzMap ℝ ℂ :=
  if P.length j ≤ r then P.packets j k else 0
def longPackets (P : LinePacketFamily N κ ι) (r : ℝ) (j : Fin N) (k : κ) : SchwartzMap ℝ ℂ :=
  if r < P.length j then P.packets j k else 0
def variation (P : LinePacketFamily N κ ι) (x : ℝ) : ℝ :=
  cubicVariation (fun n => hilbertPartialBandSum P.packets n x) N

def HasLocalBudget (P : LinePacketFamily N κ ι) (B : ℝ) : Prop :=
  ∀ u r : ℝ, 0 < r → ∀ b : ℤ × ℤ,
    (∑ j, P.length j * ∑ i : ShortBoxFiber P.length
      (centerBoxIndex P.centerX P.centerZ u P.lineY r P.width) r b j, ‖P.coeff j i‖ ^ 2) ≤ B * r

end LinePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzedLineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual analyzing coefficients, normalized once, define the line
packet family used in concentration. Their local budget is proved. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert
namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def coefficientScale (P : PlanarPacketFamily N κ ι) : ℝ := P.constant * Real.pi^2

theorem coefficientScale_pos (P : PlanarPacketFamily N κ ι) : 0 < P.coefficientScale :=
  mul_pos P.constant_pos (pow_pos Real.pi_pos _)

def analyzedLine (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y : ℝ)
    (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant / P.length j) *
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
       lineEnvelope (P.centerZ j i) P.width 2 y)) : LinePacketFamily N κ ι where
  baseX := P.baseX
  baseZ := P.baseZ
  topLength := P.topLength
  width := P.width
  lineY := y
  constant := P.constant
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  constant_pos := P.constant_pos
  coeff := fun j i => P.coefficientScale⁻¹ • P.mainCoefficient d v g j i
  wave := fun j i k => P.wave j i k y
  site := P.site
  site_injective := P.site_injective
  coeff_norm := by
    intro j i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr P.coefficientScale_pos)]
    apply (mul_le_mul_of_nonneg_left (P.mainCoefficient_norm d v hv g hg hg1 j i)
      (inv_nonneg.mpr P.coefficientScale_pos.le)).trans_eq
    exact inv_mul_cancel₀ P.coefficientScale_pos.ne'
  wave_bound := by
    intro j i k x
    apply (P.wave_bound j i k y x).trans
    apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
    apply mul_le_mul_of_nonneg_left (lineEnvelope_antitone _ _ _ (by decide : 2 ≤ 3))
      (lineEnvelope_nonneg _ _ _ _)
  deriv_bound := hderiv

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_LinePacketReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacement synthesis waves retain the already proved analyzing
coefficient budget. This is used for polynomially weighted sums and their
demodulated vertical derivatives. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert
namespace LinePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def replaceWaves (P : LinePacketFamily N κ ι) (C : ℝ) (hC : 0 < C)
    (wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (hbound : ∀ j i k x, ‖wave j i k x‖ ≤ C *
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY))
    (hderiv : ∀ j i k x, ‖deriv (wave j i k) x‖ ≤ (C / P.length j) *
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY)) : LinePacketFamily N κ ι :=
  { P with
    constant := C
    constant_pos := hC
    wave := wave
    wave_bound := hbound
    deriv_bound := hderiv }

end LinePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def planarPacketBand (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ) : ℂ :=
  ∑ i, coeff j i k * wave j i k y x

def planarPacketInterval (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  bandIntervalSignal (fun j k => planarPacketBand coeff wave j k x) a b y

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact horizontal dilation for Schwartz packets, including the Fourier
and measure factors needed to normalize different top lengths. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal
namespace LipschitzHilbert

def schwartzDilation (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun x : ℝ => r*x) (by fun_prop)
    (show AntilipschitzWith ‖r⁻¹‖₊ (fun x : ℝ => r*x) by
      simpa only [sub_zero,div_eq_mul_inv,inv_inv,mul_comm] using
        affineRescale_antilipschitz 0 r⁻¹ (inv_ne_zero hr)) f

@[simp] theorem schwartzDilation_apply (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) (x : ℝ) :
    schwartzDilation f r hr x = f (r*x) := rfl

theorem schwartzDilation_deriv (f : SchwartzMap ℝ ℂ) (r : ℝ) (hr : r ≠ 0) (x : ℝ) :
    deriv (schwartzDilation f r hr) x = (r:ℂ)*deriv f (r*x) := by
  have h := (f.hasDerivAt (r*x)).scomp x ((hasDerivAt_id x).const_mul r)
  simpa only [schwartzDilation,SchwartzMap.compCLMOfAntilipschitz_apply,Function.comp_apply,
    id_eq,mul_one,Complex.real_smul] using h.deriv

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarHorizontalRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a top's horizontal length while retaining its packet
lattice and its original analyzing coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem lineEnvelope_horizontalDilation (a l r x : ℝ) (n : ℕ) (hr : r ≠ 0) :
    lineEnvelope (a/r) (l/r) n x = lineEnvelope a l n (r*x) := by
  unfold lineEnvelope
  congr 3
  field_simp

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def horizontalRescale (P : PlanarPacketFamily N κ ι) (r : ℝ) (hr : 0 < r) :
    PlanarPacketFamily N κ ι where
  baseX := P.baseX/r
  baseZ := P.baseZ
  topLength := P.topLength/r
  width := P.width
  constant := P.constant
  topLength_pos := div_pos P.topLength_pos hr
  width_pos := P.width_pos
  constant_pos := P.constant_pos
  site := P.site
  site_injective := P.site_injective
  wave := fun j i k y => schwartzDilation (P.wave j i k y) r hr.ne'
  wave_measurable := by
    intro j i k
    exact (P.wave_measurable j i k).comp
      ((measurable_fst).prodMk (measurable_const.mul measurable_snd))
  wave_bound := by
    intro j i k y x
    have hcx : P.baseX/r+(P.topLength/r/(2:ℝ)^j.val)*(P.site j i).1 =
        (P.baseX+(P.topLength/(2:ℝ)^j.val)*(P.site j i).1)/r := by ring
    have hlen : P.topLength/r/(2:ℝ)^j.val = (P.topLength/(2:ℝ)^j.val)/r := by ring
    rw [hcx,hlen,lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    exact P.wave_bound j i k y (r*x)

@[simp] theorem horizontalRescale_length (P : PlanarPacketFamily N κ ι) (r : ℝ) (hr : 0 < r) (j : Fin N) :
    (P.horizontalRescale r hr).length j = P.length j/r := by
  unfold horizontalRescale length
  ring

@[simp] theorem horizontalRescale_centerX (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).centerX j i = P.centerX j i/r := by
  simp only [centerX,horizontalRescale_length]
  change P.baseX/r+P.length j/r*(P.site j i).1 = _
  ring

@[simp] theorem horizontalRescale_centerZ (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).centerZ j i = P.centerZ j i := rfl

@[simp] theorem horizontalRescale_wave (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (j : Fin N) (i : ι j) (k : κ) (y x : ℝ) :
    (P.horizontalRescale r hr).wave j i k y x = P.wave j i k y (r*x) := rfl

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarProfilePolarization
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common profile constants remain uniform under the four unit
phases used in complex polarization. The proof uses their actual
weighted Schwartz seminorm definition, without taking a maximum over
the finite packet family. -/

noncomputable section

namespace LipschitzHilbert

theorem planarVerticalDerivative_add (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    planarVerticalDerivative (f + g) = planarVerticalDerivative f + planarVerticalDerivative g := by
  unfold planarVerticalDerivative
  rw [map_add, map_add]

theorem planarHorizontalDerivative_add (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    planarHorizontalDerivative (f + g) =
      planarHorizontalDerivative f + planarHorizontalDerivative g := by
  unfold planarHorizontalDerivative
  rw [map_add, map_add]

theorem planarVerticalJet_add (f g : SchwartzMap (ℝ × ℝ) ℂ) (i : Fin 3) :
    planarVerticalJet (f + g) i = planarVerticalJet f i + planarVerticalJet g i := by
  fin_cases i <;> simp [planarVerticalJet, planarVerticalDerivative_add]

theorem planarVerticalJet_smul (c : ℂ) (f : SchwartzMap (ℝ × ℝ) ℂ) (i : Fin 3) :
    planarVerticalJet (c • f) i = c • planarVerticalJet f i := by
  fin_cases i <;> simp [planarVerticalJet, planarVerticalDerivative_smul]

theorem planarEnvelopeConstant_add_smul_le (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (n : ℕ) :
    planarEnvelopeConstant (f + c • g) n ≤
      planarEnvelopeConstant f n + ‖c‖ * planarEnvelopeConstant g n := by
  let W := SchwartzMap.smulLeftCLM ℂ (fun z : ℝ × ℝ => (planarPolynomialWeight n z : ℂ))
  let p := SchwartzMap.seminorm ℂ (E := ℝ × ℝ) (F := ℂ) 0 0
  change p (W (f + c • g)) + 1 ≤ (p (W f) + 1) + ‖c‖ * (p (W g) + 1)
  rw [map_add, map_smul]
  have h := map_add_le_add p (W f) (c • W g)
  rw [map_smul_eq_mul] at h
  nlinarith [norm_nonneg c]

/-- The precise common profile constant is subadditive under
polarization, with the expected modulus of the scalar coefficient. -/
theorem planarProfileConstant_add_smul_le (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (n : ℕ) :
    planarProfileConstant (f + c • g) n ≤
      planarProfileConstant f n + ‖c‖ * planarProfileConstant g n := by
  simp only [planarProfileConstant, planarVerticalJet_add, planarVerticalJet_smul,
    planarHorizontalDerivative_add, planarHorizontalDerivative_smul,
    planarVerticalDerivative_add, planarVerticalDerivative_smul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h0 := planarEnvelopeConstant_add_smul_le (planarVerticalJet f i)
    (planarVerticalJet g i) c n
  have hx := planarEnvelopeConstant_add_smul_le (planarHorizontalDerivative (planarVerticalJet f i))
    (planarHorizontalDerivative (planarVerticalJet g i)) c n
  have hy := planarEnvelopeConstant_add_smul_le (planarVerticalDerivative (planarVerticalJet f i))
    (planarVerticalDerivative (planarVerticalJet g i)) c n
  nlinarith

theorem planarProfileConstant_add_unit_smul_le (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) :
    planarProfileConstant (f + c • g) n ≤
      planarProfileConstant f n + planarProfileConstant g n := by
  simpa only [hc, one_mul] using planarProfileConstant_add_smul_le f g c n

/-- Two profiles with the same bound have polarization profiles bounded
by twice that constant, uniformly for every unit complex phase. -/
theorem planarProfileConstant_polarization_bound (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) (C : ℝ)
    (hf : planarProfileConstant f n ≤ C) (hg : planarProfileConstant g n ≤ C) :
    planarProfileConstant (f + c • g) n ≤ 2 * C := by
  exact (planarProfileConstant_add_unit_smul_le f g c hc n).trans (by linarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticePolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit-phase profile combinations construct genuine source packet
families on the same lattice with a factor-two change in the raw constant. -/

noncomputable section
namespace LipschitzHilbert

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)

/-- Change the profiles, retaining every site, center, carrier and scale. -/
def withProfile : SourceLatticePacket N κ ι :=
  { P with profile := alt, profile_bound := hAlt }

@[simp] theorem withProfile_length (j : Fin N) :
    (P.withProfile alt hAlt).length j = P.length j := rfl

@[simp] theorem withProfile_actualX (j : Fin N) (u : ι j) :
    (P.withProfile alt hAlt).actualX j u = P.actualX j u := rfl

@[simp] theorem withProfile_actualZ (j : Fin N) (u : ι j) :
    (P.withProfile alt hAlt).actualZ j u = P.actualZ j u := rfl

@[simp] theorem withProfile_constant : (P.withProfile alt hAlt).constant = P.constant := rfl

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticePolarizationSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polarization preserves the original physical packet spectrum.
Both profiles use the same carrier and geometry, so their linear
combination has no Fourier support outside their shared wedge and band. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem physicalPlanarPacket_add_smul (f g : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a b l W θ frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    physicalPlanarPacket (f + c • g) a b l W θ frequency hl hW =
      physicalPlanarPacket f a b l W θ frequency hl hW +
        c • physicalPlanarPacket g a b l W θ frequency hl hW := by
  ext z
  simp only [physicalPlanarPacket_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem planarFourier_add (f g : SchwartzMap (ℝ × ℝ) ℂ) (frequency : ℝ × ℝ) :
    planarFourier (f + g : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      planarFourier f frequency + planarFourier g frequency := by
  unfold planarFourier
  simp only [add_apply, smul_add]
  exact integral_add (planarFourier_integrand_integrable f frequency)
    (planarFourier_integrand_integrable g frequency)

theorem planarAngularFourier_add_smul (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (frequency : ℝ × ℝ) :
    planarAngularFourier (f + c • g : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      planarAngularFourier f frequency + c * planarAngularFourier g frequency := by
  unfold planarAngularFourier
  rw [planarFourier_add, planarFourier_smul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

abbrev PacketIndex := Σ j, Σ l : P.labels j, Item j l

/-- Replace only the profiles in the original labeled collection. -/
abbrev withProfile (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j l u k,
      planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound) :
    SourceLabeledLattice N κ Label Item :=
  { P with profile := alt, profile_bound := hAlt }

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

/-- The source interval before splitting labels into lattice slots. -/
def rawInterval (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) : EuclideanSpace ℂ κ :=
  planarPacketInterval (ι := fun j => Σ l : P.labels j, Item j l) (fun j p => coeff j p.1 p.2)
    (fun j p k t s => P.raw i j p.1 p.2 k t s) lower upper x y

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density is the supremum of the manuscript's actual
weighted box tests. Exceeding a threshold supplies a concrete test, which
can then be fed to the finite keeper construction. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

structure OrdinaryDensityTile where
  center : ℝ×ℝ
  level : ℤ
  cell : ℤ

structure OrdinaryDensityTest (ell0 w W tau : ℝ) (q : ℤ) (tile : OrdinaryDensityTile) where
  top : SlopeBox
  level : ℤ
  cell : ℤ
  length_eq : top.length = ell0/DyadicLineGrid.scale level
  width_eq : top.width = W
  length_le : top.length ≤ tau
  tile_length_le : ell0/DyadicLineGrid.scale tile.level ≤ top.length
  center_mem : tile.center ∈ densitySpatialBox top (1/2)
  slope_mem_tile : top.slope ∈ scaledAngularCell (w/ell0) q tile.level tile.cell
  slope_mem_self : top.slope ∈ scaledAngularCell (w/ell0) q level cell

def densityAverage (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (omega : Set ℝ) : ℝ :=
  (∫ z in E ∩ u ⁻¹' omega, T.densityKernel 203 z ∂volume.prod volume)/T.area

namespace OrdinaryDensityTile

def densityValues (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) : Set ℝ :=
  insert 0 (Set.range fun test : OrdinaryDensityTest ell0 w W tau q tile =>
    densityAverage test.top E u (scaledAngularCell (w/ell0) q test.level test.cell))

def density (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) : ℝ :=
  sSup (tile.densityValues ell0 w W tau q E u)

end OrdinaryDensityTile
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarFixedScaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-length synthesis estimate in section 3. A single translated
box lattice has bounded overlap. Summing squared bin components gives a
constant independent of the number of packets and frequency bins. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def planarFixedSynthesis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ i, c i k * f i k z)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Own-box density and the short-packet estimate for unrestricted
lattice slopes. Only the intrinsic two-dimensional profile is used. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

abbrev PacketIndex := Σ j : Fin N, Σ l : P.labels j, Item j l

def densityTile (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ)
    (q : P.PacketIndex) : OrdinaryDensityTile where
  center := (P.actualX q.1 q.2.1 q.2.2,
    P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2)
  level := q.1.val
  cell := cell q.1 q.2.1

def ordinaryDensity (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (q : P.PacketIndex) : ℝ :=
  (P.densityTile oldSlope cell q).density P.topLength w P.width tau grid E u

/-- The actual spatial rectangle and direction of a source packet. -/
def ownBox (oldSlope : ℝ) (q : P.PacketIndex) : SlopeBox where
  x := P.actualX q.1 q.2.1 q.2.2
  y := P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2
  slope := oldSlope+P.rowSlope q.1 q.2.1
  length := P.length q.1
  width := P.width
  length_pos := P.length_pos q.1
  width_pos := P.width_pos

/-- The ordinary density includes each packet's own rectangle. -/
def ownDensityTest (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ)
    (grid : ℤ) (w tau : ℝ) (q : P.PacketIndex)
    (hlen : P.length q.1≤tau)
    (hslope : oldSlope+P.rowSlope q.1 q.2.1 ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    OrdinaryDensityTest P.topLength w P.width tau grid (P.densityTile oldSlope cell q) where
  top := P.ownBox oldSlope q
  level := q.1.val
  cell := cell q.1 q.2.1
  length_eq := by simp only [ownBox,length,DyadicLineGrid.scale,zpow_natCast]
  width_eq := rfl
  length_le := hlen
  tile_length_le := by
    simpa only [densityTile,ownBox,length,DyadicLineGrid.scale,zpow_natCast] using le_refl (P.length q.1)
  center_mem := by
    simp only [densitySpatialBox,densityTile,ownBox,mem_ofPred_eq,sub_self,mul_zero,abs_zero]
    exact ⟨mul_nonneg (by norm_num) (P.length_pos q.1).le,
      mul_nonneg (by norm_num) P.width_pos.le⟩
  slope_mem_tile := hslope
  slope_mem_self := hslope


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative witness radius for the ordinary density selection. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def densityRadiusConstant : ℝ := max 1 (2*(∫ z, topProfile 3 z ∂volume.prod volume))

def densityRadius (eta : ℝ) : ℝ :=
  densityRadiusConstant * max 1 (eta^(-(1/100:ℝ)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataOrdinaryDensityForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density selection, retaining its sharp witness radius
and original angular cells. Empty packet sets require no dummy keeper. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure OrdinaryDensityForest (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (w tau eta : ℝ) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) where
  keepers : Finset packets
  top : keepers → SlopeBox
  assigned : packets → keepers
  witness : keepers → Set (ℝ×ℝ)
  measurable : ∀ i, MeasurableSet (witness i)
  disjoint : Pairwise fun i j => Disjoint (witness i) (witness j)
  inside : ∀ i z, z ∈ witness i → z ∈ E ∧
    z ∈ densitySpatialBox (top i) (densityRadius eta) ∧
    |u z-(top i).slope| ≤ w/(top i).length
  mass : ∀ i, (eta/2)*(top i).area ≤ (volume.prod volume).real (witness i)
  width : ∀ i, (top i).width = P.width
  short : ∀ i, (top i).length ≤ tau
  area : (∑ i, (top i).area) ≤ 2*(volume.prod volume).real E/eta
  length_le : ∀ q : packets, P.length q.val.1 ≤ (top (assigned q)).length
  center : ∀ q : packets,
    (P.actualX q.val.1 q.val.2.1 q.val.2.2,P.actualZ q.val.1 q.val.2.1 q.val.2.2) ∈
      densitySpatialBox (top (assigned q)) (5*densityRadius eta)
  direction : ∀ q : packets, (top (assigned q)).slope ∈
    scaledAngularCell (w/P.topLength) grid q.val.1.val (cell q.val.1 q.val.2.1)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSignedSizeTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed size tests used in ordinary tree selection. Failing tests
have a packet witness and admit the manuscript's near-extremal direction. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def sizeDirection (negative : Bool) (s : ℝ) : ℝ := if negative then -s else s

def sizeTestPackets (negative : Bool) (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (remaining : Finset P.PacketIndex) (T : SlopeBox) : Finset P.PacketIndex :=
  remaining.filter fun q => P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
    cb*w/P.length q.1 ≤ sizeDirection negative (T.slope-P.rowSlope q.1 q.2.1)

def sizeTestEnergy (negative : Bool) (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (remaining : Finset P.PacketIndex) (T : SlopeBox) : ℝ :=
  ∑ q∈P.sizeTestPackets negative w cb cell grid remaining T,
    ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width

def sizeTestFails (negative : Bool) (w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (remaining : Finset P.PacketIndex) (T : SlopeBox) : Prop :=
  T.width=P.width ∧ T.length≤tau ∧
    sigma^2*T.area/2<P.sizeTestEnergy negative w cb cell grid c remaining T

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSizeStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite signed size-selection loop. Test directions are
chosen near the extremum; all tiles in the enlarged top are deleted. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def sizeDeletePackets (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (T : SlopeBox) : Finset P.PacketIndex :=
  R.filter fun q => P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T A ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)

inductive SizeStoppingRun (negative : Bool) (w cb tau sigma epsilon A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Finset P.PacketIndex → List SlopeBox → Finset P.PacketIndex → Prop
  | stop (R : Finset P.PacketIndex)
      (hgood : ∀ T, ¬P.sizeTestFails negative w cb tau sigma cell grid c R T) :
      SizeStoppingRun negative w cb tau sigma epsilon A cell grid c R [] R
  | step (R : Finset P.PacketIndex) (T : SlopeBox) (tops : List SlopeBox)
      (remaining : Finset P.PacketIndex)
      (hfail : P.sizeTestFails negative w cb tau sigma cell grid c R T)
      (hfirst : ∀ U, P.sizeTestFails negative w cb tau sigma cell grid c R U →
        sizeDirection negative T.slope < sizeDirection negative U.slope+epsilon)
      (htail : SizeStoppingRun negative w cb tau sigma epsilon A cell grid c
        (R\P.sizeDeletePackets w A cell grid R T) tops remaining) :
      SizeStoppingRun negative w cb tau sigma epsilon A cell grid c R (T::tops) remaining

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSizeSelectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint recorded tests and the exact energy bookkeeping for the
finite signed size-selection run. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def packetEnergySum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (R : Finset P.PacketIndex) : ℝ :=
  ∑ q∈R, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataScaleRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Drop a finite initial scale segment without changing any physical
packet in the remaining dyadic family. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def dropIndex (first : Fin N) (j : Fin (N-first.val)) : Fin N :=
  ⟨first.val+j.val,by have := j.isLt; have := first.isLt; omega⟩

def dropScales (first : Fin N) :
    PacketLatticeData (N-first.val) κ (fun j => Label (dropIndex first j))
      (fun j l => Item (dropIndex first j) l) where
  topLength := P.length first
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.length_pos first
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  labels := fun j => P.labels (dropIndex first j)
  originX := fun j => P.originX (dropIndex first j)
  originZ := fun j => P.originZ (dropIndex first j)
  rowSlope := fun j => P.rowSlope (dropIndex first j)
  frequency := P.frequency
  site := fun j => P.site (dropIndex first j)
  site_injective := fun j => P.site_injective (dropIndex first j)
  profile := fun j => P.profile (dropIndex first j)
  profile_bound := fun j => P.profile_bound (dropIndex first j)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularGridRebase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dropping dyadic packet scales rebases the same angular grid. The
alternating shift changes the grid sign at odd starting levels. -/
noncomputable section
open Set
namespace LipschitzHilbert
open DyadicLineGrid

theorem scaledAngularCell_eq_Ico (unit : ℝ) (hunit : 0<unit) (q k j : ℤ) :
    scaledAngularCell unit q k j=Ico (unit*left q k j) (unit*left q k (j+1)) := by
  ext s
  change (left q k j ≤ s/unit ∧ s/unit<left q k (j+1)) ↔ _
  rw [le_div_iff₀ hunit,div_lt_iff₀ hunit]
  simp only [mul_comm,mem_Ico]

theorem angular_shift_rebase (q h k : ℤ) :
    shift ((h.negOnePow : ℤ)*q) k=shift q (h+k) := by
  simp only [shift,Int.negOnePow_add,Units.val_mul,Int.cast_mul]
  ring

theorem angular_left_rebase (q h k j : ℤ) :
    scale h*left ((h.negOnePow : ℤ)*q) k j=left q (h+k) j := by
  unfold left
  rw [angular_shift_rebase]
  simp only [scale,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

theorem scaledAngularCell_rebase (unit : ℝ) (hunit : 0<unit) (q h k j : ℤ) :
    scaledAngularCell (unit*scale h) ((h.negOnePow : ℤ)*q) k j=
      scaledAngularCell unit q (h+k) j := by
  rw [scaledAngularCell_eq_Ico _ (mul_pos hunit (scale_pos h)),
    scaledAngularCell_eq_Ico _ hunit]
  congr 1 <;> rw [mul_assoc,angular_left_rebase]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityRebase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted density tests are invariant under a dyadic change of
starting scale. Their physical boxes and integrals are unchanged. -/
noncomputable section
open Set
namespace LipschitzHilbert
open DyadicLineGrid

def OrdinaryDensityTile.rebase (tile : OrdinaryDensityTile) (h : ℤ) : OrdinaryDensityTile :=
  { tile with level := tile.level-h }

theorem density_rebase_length (ell0 : ℝ) (h k : ℤ) :
    (ell0/scale h)/scale (k-h)=ell0/scale k := by
  simp only [scale,zpow_sub₀ (by norm_num : (2:ℝ)≠0)]
  field_simp

theorem density_rebase_cell (ell0 w : ℝ) (hell0 : 0<ell0) (hw : 0<w)
    (q h k j : ℤ) :
    scaledAngularCell (w/(ell0/scale h)) ((h.negOnePow : ℤ)*q) (k-h) j=
      scaledAngularCell (w/ell0) q k j := by
  have he : w/(ell0/scale h)=(w/ell0)*scale h := by field_simp
  rw [he,scaledAngularCell_rebase _ (div_pos hw hell0)]
  congr 1
  omega

def OrdinaryDensityTest.rebase {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (test : OrdinaryDensityTest ell0 w W tau q tile)
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w) :
    OrdinaryDensityTest (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) (tile.rebase h) where
  top := test.top
  level := test.level-h
  cell := test.cell
  length_eq := test.length_eq.trans (density_rebase_length ell0 h test.level).symm
  width_eq := test.width_eq
  length_le := test.length_le
  tile_length_le := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_length] using test.tile_length_le
  center_mem := test.center_mem
  slope_mem_tile := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_cell ell0 w hell0 hw] using test.slope_mem_tile
  slope_mem_self := by
    simpa only [density_rebase_cell ell0 w hell0 hw] using test.slope_mem_self

def OrdinaryDensityTest.restore {ell0 w W tau : ℝ} {q : ℤ} {tile : OrdinaryDensityTile}
    (h : ℤ) (hell0 : 0<ell0) (hw : 0<w)
    (test : OrdinaryDensityTest (ell0/scale h) w W tau ((h.negOnePow : ℤ)*q) (tile.rebase h)) :
    OrdinaryDensityTest ell0 w W tau q tile where
  top := test.top
  level := test.level+h
  cell := test.cell
  length_eq := by
    rw [test.length_eq,←density_rebase_length ell0 h (test.level+h)]
    simp only [add_sub_cancel_right]
  width_eq := test.width_eq
  length_le := test.length_le
  tile_length_le := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_length] using test.tile_length_le
  center_mem := test.center_mem
  slope_mem_tile := by
    simpa only [OrdinaryDensityTile.rebase,density_rebase_cell ell0 w hell0 hw] using test.slope_mem_tile
  slope_mem_self := by
    have he := density_rebase_cell ell0 w hell0 hw q h (test.level+h) test.cell
    rw [add_sub_cancel_right] at he
    rw [←he]
    exact test.slope_mem_self

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDropPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite packet subsets after dropping an initial scale segment. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
attribute [local instance] Classical.propDecidable

def dropPacket (first : Fin N) (q : (P.dropScales first).PacketIndex) : P.PacketIndex :=
  ⟨dropIndex first q.1,⟨q.2.1,q.2.2⟩⟩

def dropPackets (first : Fin N) (Q : Finset P.PacketIndex) :
    Finset (P.dropScales first).PacketIndex :=
  Finset.univ.filter (fun q => P.dropPacket first q∈Q)

@[simp] theorem mem_dropPackets (first : Fin N) (Q : Finset P.PacketIndex)
    (q : (P.dropScales first).PacketIndex) :
    q∈P.dropPackets first Q ↔ P.dropPacket first q∈Q := by
  simp only [dropPackets,Finset.mem_filter,Finset.mem_univ,true_and]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketReferenceSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unrestricted family passes its original spectra to every local
reference lattice without enlarging either frequency strip. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

@[simp] theorem referenceFamily_slope (j : Fin N) (l : (Q).labels j) :
    newSlope + (Q).rowSlope j l = oldSlope + P.rowSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) := by
  change newSlope + (P.rowSlope j _ + (oldSlope-newSlope)) = _
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_TileEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def tileEnvelope (a b l W : ℝ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  lineEnvelope a l n z.1 * lineEnvelope b W n z.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularErrorConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-scale convolution majorant for coefficients of the actual
angular multiplier error, including its two-coordinate direction profile. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def angularErrorWave {ι κ : Type*} (b : ι → κ → ℝ → ℂ)
    (ψ : ι → κ → ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (i : ι) (k : κ) (z : ℝ × ℝ) : ℂ :=
  multiplierError (b i k) t d (u z) * ψ i k z

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledErrorFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic angular errors on translated lattices with bounded local
multiplicity of slope labels. The common source is counted before integration. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

structure LabeledAngularErrorFamily (N : ℕ) (Λ : Fin N → Type) (κ : Type)
    (ι : ∀ j, Λ j → Type) [∀ j, Fintype (Λ j)] [Fintype κ]
    [∀ j b, Fintype (ι j b)] where
  topLength : ℝ
  width : ℝ
  angleBase : ℝ
  referenceSlope : ℝ
  smallRatio : ℝ
  wideConstant : ℝ
  exponent : ℕ
  wideExponent : ℕ
  packetBound : ℝ
  multiplierBound : ℝ
  multiplierLip : ℝ
  radius : ℝ
  radiusBound : ℕ
  multiplicity : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  angleBase_pos : 0 < angleBase
  smallRatio_pos : 0 < smallRatio
  smallRatio_le : smallRatio ≤ 1
  wideConstant_le : wideConstant ≤ smallRatio*(2:ℝ)^wideExponent
  wideRatio_ge : 1 ≤ wideConstant*((2:ℝ)^exponent)^4
  packetBound_nonneg : 0 ≤ packetBound
  multiplierBound_nonneg : 0 ≤ multiplierBound
  multiplierLip_nonneg : 0 ≤ multiplierLip
  radius_le : radius ≤ radiusBound
  direction : ℝ×ℝ → ℝ
  direction_measurable : Measurable direction
  test : ℝ×ℝ → EuclideanSpace ℂ κ
  test_measurable : Measurable test
  test_bound : ∀ z, ‖test z‖ ≤ 1
  originX : ∀ j, Λ j → ℝ
  originY : ∀ j, Λ j → ℝ
  slope : ∀ j, Λ j → ℝ
  localMultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (slope j)
    (angleBase*(2:ℝ)^j.val) multiplicity
  site : ∀ j b, ι j b → ℤ×ℤ
  site_injective : ∀ j b, Function.Injective (site j b)
  multiplier : ∀ j, Λ j → κ → ℝ → ℂ
  multiplier_measurable : ∀ j b k, Measurable (multiplier j b k)
  multiplier_bounded : ∀ j b k s, ‖multiplier j b k s‖ ≤ multiplierBound
  multiplier_support : ∀ j b k s, multiplier j b k s ≠ 0 →
    |s-slope j b| ≤ radius*(angleBase*(2:ℝ)^j.val)
  multiplier_near : ∀ j b k s, |s-referenceSlope| ≤ smallRatio*(angleBase*(2:ℝ)^j.val) →
    ‖multiplier j b k s-multiplier j b k referenceSlope‖ ≤
      multiplierLip*(|s-referenceSlope|/(angleBase*(2:ℝ)^j.val))
  multiplier_far : ∀ j b k s,
    (wideConstant*((2:ℝ)^exponent)^4)*(angleBase*(2:ℝ)^j.val) < |s-referenceSlope| →
      multiplier j b k s = 0
  wave : ∀ j b, ι j b → κ → ℝ×ℝ → ℂ
  wave_measurable : ∀ j b i k, Measurable (wave j b i k)
  wave_bound : ∀ j b i k z, ‖wave j b i k z‖ ≤ packetBound*
    tileEnvelope (originX j b+(topLength/(2:ℝ)^j.val)*(site j b i).1)
      (originY j b+width*(site j b i).2) (topLength/(2:ℝ)^j.val) width 6 z

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

def length (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) : ℝ :=
  P.topLength/(2:ℝ)^j.val

def angleStep (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) : ℝ :=
  P.angleBase*(2:ℝ)^j.val

def coefficient (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (b : Λ j)
    (i : ι j b) : EuclideanSpace ℂ κ :=
  analyzingCoefficient volume (fun _ : ι j b => P.length j*P.width)
    (angularErrorWave (fun _ k => P.multiplier j b k) (P.wave j b)
      P.direction P.referenceSlope (P.angleStep j)) P.test i

def scaleError (P : LabeledAngularErrorFamily N Λ κ ι) (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ b, ∑ i, ‖P.coefficient j b i‖*tileEnvelope
    (P.originX j b+P.length j*(P.site j b i).1)
    (P.originY j b+P.width*(P.site j b i).2) (P.length j) P.width 6 (x,y)

def error (P : LabeledAngularErrorFamily N Λ κ ι) (y x : ℝ) : ℝ :=
  ∑ j, P.scaleError j y x

def sourceAmplitude (P : LabeledAngularErrorFamily N Λ κ ι) : ℝ :=
  ((64*(4*Real.pi)^2)*(2*((2*P.radiusBound+1)*P.multiplicity):ℕ))*
    (P.packetBound*(2*P.multiplierBound+P.multiplierLip))

theorem sourceAmplitude_nonneg (P : LabeledAngularErrorFamily N Λ κ ι) :
    0 ≤ P.sourceAmplitude := by
  have := P.packetBound_nonneg
  have := P.multiplierBound_nonneg
  have := P.multiplierLip_nonneg
  unfold sourceAmplitude
  positivity

def sources (P : LabeledAngularErrorFamily N Λ κ ι) (y : ℝ) : LineErrorSources N :=
  actualErrorSources P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def absoluteConstant : ℝ :=
  ((2^P.order*P.profileBound)*P.ratioBound^2)*3^(2*P.order)

def snappedSite (j : Fin N) (l : P.labels j) (u : Item j l) : ℤ×ℤ :=
  snappedLatticeSite (P.originX j l) (P.originZ j l) (P.length j) P.width
    (P.rowSlope j l) (P.site j l u)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceLabeledAngularErrorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The labeled dyadic error family formed from the original physical
packets and selectors, with an exact measure-preserving coefficient identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def physicalAngularErrorCoefficient (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (angularErrorWave (fun _ k => b j l k) (fun u k => P.physicalPacket t j l u k)
      v t (a*(2:ℝ)^j.val)) g u

/-- The original positive error sum evaluated at a physical point. -/
def physicalAngularError (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  ∑ j, ∑ l : P.labels j, ∑ u : Item j l,
    ‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
      tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (z.1,z.2-t*z.1)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCoefficientSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original labeled physical coefficient splits into its centered
frozen selector and angular error, without changing synthesis packets. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalMultiplierCoefficient (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun u k z => b j l k (v z)*P.physicalPacket t j l u k z) g u

def physicalFrozenCenteredCoefficient (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun u k z => if |v z-t| ≤ a*(2:ℝ)^j.val then
      b j l k t*P.physicalPacket t j l u k z else 0) g u

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def physicalMultiplierCoefficient (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun u k z => b j l k (v z)*P.physicalPacket t j l u k z) g u

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected tree from an unrestricted packet lattice has a genuine
bounded reference lattice. Only the selected packets are present, and
their original physical waves are preserved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)

def selectedLabels (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ (h : l∈P.labels j) (u : Item j l),
    (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈S)

def selectedOriginalLabel (j : Fin N) (l : P.selectedLabels S j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

def SelectedItem (j : Fin N) (l : Label j) :=
  {u : Item j l // ∃ h : l∈P.labels j, (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈S}

instance selectedItemFintype (j : Fin N) (l : Label j) : Fintype (P.SelectedItem S j l) :=
  inferInstanceAs (Fintype {u : Item j l // ∃ h : l∈P.labels j,
    (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex)∈S})

theorem selectedLabel_has_packet (j : Fin N) (l : P.selectedLabels S j) :
    ∃ u : Item j l, (⟨j,⟨P.selectedOriginalLabel S j l,u⟩⟩ : P.PacketIndex)∈S := by
  obtain ⟨h,u,hu⟩ := (Finset.mem_filter.mp l.property).2
  exact ⟨u,hu⟩

variable (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)

include hnear in
theorem selectedLabel_near (j : Fin N) (l : P.selectedLabels S j) :
    |P.rowSlope j (P.selectedOriginalLabel S j l)-t|≤Cb*w/P.length j := by
  obtain ⟨u,hu⟩ := P.selectedLabel_has_packet S j l
  exact hnear ⟨j,⟨P.selectedOriginalLabel S j l,u⟩⟩ hu

def selectedReference : SourceLabeledLattice N κ Label (P.SelectedItem S) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := F*Cb
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := mul_nonneg hF hCb
  labels := P.selectedLabels S
  originX := fun j l => P.originX j (P.selectedOriginalLabel S j l)
  originZ := fun j l => P.originZ j (P.selectedOriginalLabel S j l)-
    t*P.originX j (P.selectedOriginalLabel S j l)
  rowSlope := fun j l => P.rowSlope j (P.selectedOriginalLabel S j l)-t
  frequency := P.frequency
  site := fun j l u => P.site j (P.selectedOriginalLabel S j l) u.val
  site_injective := fun j l => (P.site_injective j (P.selectedOriginalLabel S j l)).comp
    Subtype.val_injective
  profile := fun j l u k => P.profile j (P.selectedOriginalLabel S j l) u.val k
  profile_bound := fun j l u k => P.profile_bound j (P.selectedOriginalLabel S j l) u.val k
  shear_bound := by
    intro j l
    have hr := (le_div_iff₀ (P.length_pos j)).mp (P.selectedLabel_near S t Cb w hnear j l)
    change |(P.rowSlope j (P.selectedOriginalLabel S j l)-t)*P.length j/P.width|≤1
    rw [abs_div,abs_mul,abs_of_pos (P.length_pos j),abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr (hr.trans hwide)
  carrier_bound := by
    intro j l k
    have hr := (le_div_iff₀ (P.length_pos j)).mp (P.selectedLabel_near S t Cb w hnear j l)
    change |P.frequency k*(P.rowSlope j (P.selectedOriginalLabel S j l)-t)*P.length j|≤F*Cb
    rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j),mul_assoc]
    calc
      _ ≤ (F/w)*(Cb*w) := mul_le_mul (hfrequency k) hr
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F*Cb := by field_simp

local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

@[simp] theorem selectedReference_actualX (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) :
    (Q).actualX j l u=P.actualX j (P.selectedOriginalLabel S j l) u.val := rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted interval-maximal synthesis on actual separated
source trees, conditional only on the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

def physicalTreePartial (P : SourceLabeledLattice N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  packetPartialSum (fun j => planarFixedSynthesis
    (fun q : Σ l : P.labels j, Item j l => c j q.1 q.2)
    (fun q k => P.physicalPacket t j q.1 q.2 k) z) n

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen selector values multiply the original Schwartz profiles.
They preserve the common seminorm bound, geometry and physical spectrum;
no new packet or concentration assumption is introduced. -/

noncomputable section
namespace LipschitzHilbert

theorem planarEnvelopeConstant_smul_le (f : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    planarEnvelopeConstant (c • f) n ≤ planarEnvelopeConstant f n := by
  let W := SchwartzMap.smulLeftCLM ℂ (fun z : ℝ × ℝ => (planarPolynomialWeight n z : ℂ))
  let p := SchwartzMap.seminorm ℂ (E := ℝ × ℝ) (F := ℂ) 0 0
  change p (W (c • f)) + 1 ≤ p (W f) + 1
  rw [map_smul, map_smul_eq_mul]
  have h := mul_le_of_le_one_left (apply_nonneg p (W f)) hc
  linarith

theorem planarProfileConstant_smul_le (f : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    planarProfileConstant (c • f) n ≤ planarProfileConstant f n := by
  simp only [planarProfileConstant, planarVerticalJet_smul,
    planarHorizontalDerivative_smul, planarVerticalDerivative_smul]
  apply Finset.sum_le_sum
  intro i _
  exact add_le_add (add_le_add
    (planarEnvelopeConstant_smul_le _ c hc n)
    (planarEnvelopeConstant_smul_le _ c hc n))
    (planarEnvelopeConstant_smul_le _ c hc n)

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

def frozenProfile : SourceLatticePacket N κ ι :=
  { P with
    profile := fun j u k => c j u k • P.profile j u k
    profile_bound := fun j u k =>
      (planarProfileConstant_smul_le _ _ (hc j u k) _).trans (P.profile_bound j u k) }

@[simp] theorem frozenProfile_constant : (P.frozenProfile c hc).constant = P.constant := rfl

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SincMaskMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global motion of the actual sinc-product mask.  The integral formula
handles the origin without a quotient singularity. -/

noncomputable section
open scoped Interval

namespace LipschitzHilbert

theorem sinc_eq_integral_cos (x : ℝ) :
    Real.sinc x = ∫ t in (0:ℝ)..1, Real.cos (t*x) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [intervalIntegral.integral_comp_mul_right _ hx, integral_cos]
  simp [Real.sinc_of_ne_zero hx, div_eq_mul_inv, mul_comm]

/-- A global bound, including either endpoint equal to zero. -/
theorem abs_sinc_sub_sinc_le (x y : ℝ) :
    |Real.sinc x-Real.sinc y| ≤ |x-y| := by
  have hi (v : ℝ) : IntervalIntegrable (fun t : ℝ => Real.cos (t*v))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [sinc_eq_integral_cos x, sinc_eq_integral_cos y,
    ← intervalIntegral.integral_sub (hi x) (hi y)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := |x-y|)
    (f := fun t : ℝ => Real.cos (t*x)-Real.cos (t*y)) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb
  · intro t ht
    simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
    calc
      ‖Real.cos (t*x)-Real.cos (t*y)‖ ≤ |t*x-t*y| :=
        Real.abs_cos_sub_cos_le _ _
      _ = |t| * |x-y| := by rw [← mul_sub, abs_mul]
      _ ≤ 1 * |x-y| := mul_le_mul_of_nonneg_right
        (by rw [abs_of_pos ht.1]; exact ht.2) (abs_nonneg _)
      _ = _ := one_mul _

theorem abs_sinc_product_sub_le (x₁ y₁ x₀ y₀ : ℝ) :
    |Real.sinc x₁*Real.sinc y₁-Real.sinc x₀*Real.sinc y₀| ≤
      |x₁-x₀|+|y₁-y₀| := by
  calc
    _ = |(Real.sinc x₁-Real.sinc x₀)*Real.sinc y₁+
        Real.sinc x₀*(Real.sinc y₁-Real.sinc y₀)| := by congr 1; ring
    _ ≤ |(Real.sinc x₁-Real.sinc x₀)*Real.sinc y₁|+
        |Real.sinc x₀*(Real.sinc y₁-Real.sinc y₀)| := abs_add_le _ _
    _ = |Real.sinc x₁-Real.sinc x₀| * |Real.sinc y₁|+
        |Real.sinc x₀| * |Real.sinc y₁-Real.sinc y₀| := by rw [abs_mul, abs_mul]
    _ ≤ |x₁-x₀| * 1+1 * |y₁-y₀| := add_le_add
      (mul_le_mul (abs_sinc_sub_sinc_le _ _) (Real.abs_sinc_le_one _)
        (abs_nonneg _) (abs_nonneg _))
      (mul_le_mul (Real.abs_sinc_le_one _) (abs_sinc_sub_sinc_le _ _)
        (abs_nonneg _) zero_le_one)
    _ = _ := by ring

theorem sincProductMask_motion (n : ℕ) (x₁ y₁ x₀ y₀ : ℝ) :
    |sincProductMask n x₁ y₁-sincProductMask n x₀ y₀| ≤
      (2*(n:ℝ))*(|x₁-x₀|+|y₁-y₀|) := by
  have hprod (x y : ℝ) : |Real.sinc x*Real.sinc y| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (Real.abs_sinc_le_one x)
      (Real.abs_sinc_le_one y) (abs_nonneg _) zero_le_one
  have hm : max |Real.sinc x₁*Real.sinc y₁| |Real.sinc x₀*Real.sinc y₀| ≤ 1 :=
    max_le (hprod _ _) (hprod _ _)
  have hp : max |Real.sinc x₁*Real.sinc y₁| |Real.sinc x₀*Real.sinc y₀| ^
      (2*n-1) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀
      (le_trans (abs_nonneg _) (le_max_left _ _)) hm (2*n-1)
  calc
    _ ≤ |Real.sinc x₁*Real.sinc y₁-Real.sinc x₀*Real.sinc y₀| * (2*n:ℕ)*
        max |Real.sinc x₁*Real.sinc y₁| |Real.sinc x₀*Real.sinc y₀|^(2*n-1) :=
      abs_pow_sub_pow_le _ _ (2*n)
    _ ≤ (|x₁-x₀|+|y₁-y₀|)*(2*n:ℕ)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (abs_sinc_product_sub_le _ _ _ _)
        (Nat.cast_nonneg _)) hp (by positivity) (by positivity)
    _ = _ := by push_cast; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SincMaskSchwartz
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth sinc multipliers preserve Schwartz packets. The derivative
bounds follow from the same compact cosine average used for the mask's
Fourier support; no assertion about a singular quotient at zero is used. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology
namespace LipschitzHilbert

def sincJet (n : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Ioc (0:ℝ) 1, t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2)

theorem sincJet_integrand_bound (n : ℕ) (x t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
    ‖t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2)‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos ht.1]
  exact (mul_le_mul (pow_le_one₀ ht.1.le ht.2) (Real.abs_cos_le_one _)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem sincJet_integrable (n : ℕ) (x : ℝ) :
    Integrable (fun t => t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2))
      (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply (integrable_const (1:ℝ)).mono'
  · exact (by fun_prop : Continuous (fun t : ℝ =>
      t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sincJet_integrand_bound n x t ht

theorem sincJet_bound (n : ℕ) (x : ℝ) : ‖sincJet n x‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le (integrable_const (1:ℝ))
    (show ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) 1),
      ‖t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2)‖ ≤ 1 by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact sincJet_integrand_bound n x t ht)
  simpa [sincJet] using h

theorem sincJet_continuous (n : ℕ) : Continuous (sincJet n) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => (1:ℝ))
  · intro x
    exact (sincJet_integrable n x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact sincJet_integrand_bound n x t ht
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun t => by fun_prop)

theorem sincJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (sincJet n) (sincJet (n+1) x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0:ℝ) 1)) (s := univ)
    (F := fun x t : ℝ => t^n*Real.cos (t*x+(n:ℝ)*Real.pi/2))
    (F' := fun x t : ℝ => t^(n+1)*Real.cos (t*x+((n+1:ℕ):ℝ)*Real.pi/2))
    (bound := fun _ => (1:ℝ))
    (show univ ∈ nhds x from Filter.univ_mem)
    (Filter.Eventually.of_forall (fun y => (sincJet_integrable n y).aestronglyMeasurable))
    (sincJet_integrable n x) (sincJet_integrable (n+1) x).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro y _
      exact sincJet_integrand_bound (n+1) y t ht)
    (integrable_const _) (by
      filter_upwards [] with t
      intro y _
      have hd := (((hasDerivAt_id y).const_mul t).add_const
        ((n:ℝ)*Real.pi/2)).cos.const_mul (t^n)
      simp only [id_eq,mul_one] at hd
      convert hd using 1
      all_goals try with_reducible_and_instances rfl
      have hc : Real.cos (t*y+((n+1:ℕ):ℝ)*Real.pi/2) =
          -Real.sin (t*y+(n:ℝ)*Real.pi/2) := by
        rw [show t*y+((n+1:ℕ):ℝ)*Real.pi/2 =
          (t*y+(n:ℝ)*Real.pi/2)+Real.pi/2 by push_cast; ring,
          Real.cos_add_pi_div_two]
      rw [hc,pow_succ]
      ring)
  exact h.2

theorem sincJet_deriv (n : ℕ) : deriv (sincJet n) = sincJet (n+1) := by
  funext x
  exact (sincJet_hasDerivAt n x).deriv

theorem sincJet_contDiff (n : ℕ) : ContDiff ℝ ∞ (sincJet n) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing n with
  | zero => exact contDiff_zero.mpr (sincJet_continuous n)
  | succ k ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
      refine ⟨fun x => (sincJet_hasDerivAt n x).differentiableAt,?_,?_⟩
      · simp
      · rw [sincJet_deriv]
        exact ih (n+1)

theorem sincJet_zero : sincJet 0 = Real.sinc := by
  funext x
  rw [sinc_eq_integral_cos,intervalIntegral.integral_of_le zero_le_one]
  simp only [sincJet,pow_zero,Nat.cast_zero,zero_mul,zero_div,add_zero,one_mul]

theorem sincJet_iteratedDeriv (n : ℕ) : iteratedDeriv n Real.sinc = sincJet n := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,sincJet_zero]
  | succ n ih => rw [iteratedDeriv_succ,ih,sincJet_deriv]

/-- All real sinc derivatives are uniformly bounded by one. -/
theorem norm_iteratedDeriv_sinc_le_one (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sinc x‖ ≤ 1 := by
  rw [sincJet_iteratedDeriv]
  exact sincJet_bound n x

theorem sinc_hasTemperateGrowth : Function.HasTemperateGrowth Real.sinc := by
  refine ⟨?_,fun n => ⟨0,1,fun x => ?_⟩⟩
  · rw [← sincJet_zero]
    exact sincJet_contDiff 0
  · simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,pow_zero,mul_one] using
      norm_iteratedDeriv_sinc_le_one n x

theorem sincProductAffine_hasTemperateGrowth (n : ℕ) (a b c d : ℝ) :
    Function.HasTemperateGrowth
      (fun x : ℝ => (sincProductMask n (a*x+b) (c*x+d):ℂ)) := by
  apply Function.Complex.hasTemperateGrowth_ofReal.comp
  exact ((sinc_hasTemperateGrowth.comp (by fun_prop)).mul
    (sinc_hasTemperateGrowth.comp (by fun_prop))).pow (2*n)

/-- Multiplication by the actual even mask is a Schwartz operation. -/
def sincProductSchwartz (f : SchwartzMap ℝ ℂ) (n : ℕ) (a b c d : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x : ℝ => (sincProductMask n (a*x+b) (c*x+d):ℂ)) f

@[simp] theorem sincProductSchwartz_apply (f : SchwartzMap ℝ ℂ)
    (n : ℕ) (a b c d x : ℝ) :
    sincProductSchwartz f n a b c d x = (sincProductMask n (a*x+b) (c*x+d):ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (sincProductAffine_hasTemperateGrowth n a b c d) f x

theorem sincProductSchwartz_norm_le (f : SchwartzMap ℝ ℂ)
    (n : ℕ) (a b c d x : ℝ) :
    ‖sincProductSchwartz f n a b c d x‖ ≤ ‖f x‖ := by
  rw [sincProductSchwartz_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sincProductMask_nonneg _ _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (sincProductMask_le_one _ _ _)

theorem sincProductAffine_lipschitz (n : ℕ) (a b c d : ℝ) :
    LipschitzWith ⟨2*(n:ℝ)*(|a|+|c|),by positivity⟩
      (fun x : ℝ => (sincProductMask n (a*x+b) (c*x+d):ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := sincProductMask_motion n (a*x+b) (c*x+d) (a*y+b) (c*y+d)
  have ha : |a*x+b-(a*y+b)| = |a| * |x-y| := by
    rw [show a*x+b-(a*y+b) = a*(x-y) by ring,abs_mul]
  have hc : |c*x+d-(c*y+d)| = |c| * |x-y| := by
    rw [show c*x+d-(c*y+d) = c*(x-y) by ring,abs_mul]
  rw [ha,hc] at h
  simp only [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  change |sincProductMask n (a*x+b) (c*x+d)-sincProductMask n (a*y+b) (c*y+d)| ≤
    (2*(n:ℝ)*(|a|+|c|))*|x-y|
  calc
    _ ≤ 2*(n:ℝ)*(|a| * |x-y|+|c| * |x-y|) := h
    _ = _ := by ring

/-- The extra derivative cost is precisely the sum of mask slopes. -/
theorem sincProductSchwartz_deriv_le (f : SchwartzMap ℝ ℂ)
    (n : ℕ) (a b c d x : ℝ) :
    ‖deriv (sincProductSchwartz f n a b c d) x‖ ≤
      ‖deriv f x‖+(2*(n:ℝ)*(|a|+|c|))*‖f x‖ := by
  let m : ℝ → ℂ := fun y => (sincProductMask n (a*y+b) (c*y+d):ℂ)
  have hm : DifferentiableAt ℝ m x :=
    (sincProductAffine_hasTemperateGrowth n a b c d).1.differentiable (by simp) x
  have hd : ‖deriv m x‖ ≤ 2*(n:ℝ)*(|a|+|c|) :=
    norm_deriv_le_of_lipschitz (sincProductAffine_lipschitz n a b c d)
  have hb : ‖m x‖ ≤ 1 := by
    simpa only [m,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sincProductMask_nonneg _ _ _)] using sincProductMask_le_one n (a*x+b) (c*x+d)
  have heq : (sincProductSchwartz f n a b c d : ℝ → ℂ) = fun y => m y*f y := by
    funext y
    exact sincProductSchwartz_apply f n a b c d y
  rw [heq]
  change ‖deriv (m*(f : ℝ → ℂ)) x‖ ≤ _
  rw [deriv_mul hm (f.differentiableAt)]
  calc
    _ ≤ ‖deriv m x‖*‖f x‖+‖m x‖*‖deriv f x‖ := by
      simpa only [norm_mul] using norm_add_le (deriv m x*f x) (m x*deriv f x)
    _ ≤ (2*(n:ℝ)*(|a|+|c|))*‖f x‖+1*‖deriv f x‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SincMaskedLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact sinc-masked synthesis waves retain the analyzing budget and
have a factor-two envelope constant when their derivative bandwidth is
at most the packet's inverse length. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace LipschitzHilbert.LinePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : LinePacketFamily N κ ι) (n : ℕ)
  (a b c d : ∀ j, ι j → κ → ℝ)

theorem sincMasked_bound (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    ‖sincProductSchwartz (P.wave j u k) n (a j u k) (b j u k) (c j u k) (d j u k) x‖ ≤
      (2*P.constant)*(lineEnvelope (P.centerX j u) (P.length j) 3 x*
        lineEnvelope (P.centerZ j u) P.width 2 P.lineY) := by
  apply (sincProductSchwartz_norm_le (P.wave j u k) n _ _ _ _ x).trans
  apply (P.wave_bound j u k x).trans
  exact mul_le_mul_of_nonneg_right (by linarith [P.constant_pos])
    (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))

theorem sincMasked_deriv
    (hband : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j)
    (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    ‖deriv (sincProductSchwartz (P.wave j u k) n (a j u k) (b j u k) (c j u k) (d j u k)) x‖ ≤
      ((2*P.constant)/P.length j)*(lineEnvelope (P.centerX j u) (P.length j) 3 x*
        lineEnvelope (P.centerZ j u) P.width 2 P.lineY) := by
  let E := lineEnvelope (P.centerX j u) (P.length j) 3 x*
    lineEnvelope (P.centerZ j u) P.width 2 P.lineY
  have hE : 0 ≤ E := mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ ‖deriv (P.wave j u k) x‖+
        (2*(n:ℝ)*(|a j u k|+|c j u k|))*‖P.wave j u k x‖ :=
      sincProductSchwartz_deriv_le (P.wave j u k) n _ _ _ _ x
    _ ≤ (P.constant/P.length j)*E+
        (2*(n:ℝ)*(|a j u k|+|c j u k|))*(P.constant*E) :=
      add_le_add (P.deriv_bound j u k x)
        (mul_le_mul_of_nonneg_left (P.wave_bound j u k x) (by positivity))
    _ ≤ (P.constant/P.length j)*E+(1/P.length j)*(P.constant*E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (hband j u k)
        (mul_nonneg P.constant_pos.le hE))
    _ = _ := by dsimp only [E]; ring

/-- Only the synthesis waves change. Coefficients and all lattice
geometry are retained literally. -/
def sincMasked
    (hband : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j) :
    LinePacketFamily N κ ι :=
  P.replaceWaves (2*P.constant) (mul_pos (by norm_num) P.constant_pos)
    (fun j u k => sincProductSchwartz (P.wave j u k) n (a j u k) (b j u k) (c j u k) (d j u k))
    (P.sincMasked_bound n a b c d) (P.sincMasked_deriv n a b c d hband)

variable (hband : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j)

@[simp] theorem sincMasked_coeff (j : Fin N) (u : ι j) :
    (P.sincMasked n a b c d hband).coeff j u = P.coeff j u := rfl

@[simp] theorem sincMasked_wave (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.sincMasked n a b c d hband).wave j u k x =
      (sincProductMask n (a j u k*x+b j u k) (c j u k*x+d j u k):ℂ)*P.wave j u k x :=
  sincProductSchwartz_apply (P.wave j u k) n _ _ _ _ x

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PositivePacketSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive lattice square estimate and local coefficient energy on
one reference line. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def envelope (P : LinePacketFamily N κ ι) (j : Fin N) (i : ι j) (x : ℝ) : ℝ :=
  lineEnvelope (P.centerX j i) (P.length j) 3 x * lineEnvelope (P.centerZ j i) P.width 2 P.lineY

def positiveScale (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) : ℝ :=
  ∑ i, ‖P.coeff j i‖ * P.envelope j i x

def coefficientEnergy (P : LinePacketFamily N κ ι) (j : Fin N) (x : ℝ) : ℝ :=
  ∑ i, ‖P.coeff j i‖ ^ 2 * P.envelope j i x

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SquareLineConcentration
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every-line BMO and moments of the positive packet square function. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

def squareSum (P : LinePacketFamily N κ ι) (x : ℝ) : ℝ := ∑ j, P.positiveScale j x ^ 2
def shortSquare (P : LinePacketFamily N κ ι) (r x : ℝ) : ℝ :=
  ∑ j, if P.length j ≤ r then P.positiveScale j x ^ 2 else 0
def longSquare (P : LinePacketFamily N κ ι) (r x : ℝ) : ℝ :=
  ∑ j, if r < P.length j then P.positiveScale j x ^ 2 else 0
def squareFunction (P : LinePacketFamily N κ ι) (x : ℝ) : ℝ := Real.sqrt (P.squareSum x)
def squareMeanConstant (B : ℝ) : ℝ := (65536 * Real.pi) * (4 * Real.pi) ^ 6 * B

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-line packets are normalized at their actual horizontal
length before applying the published scalar variation input. The local
coefficient budget is independent of that length, the number of scales,
and the Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def referencePlanarFamily : PlanarPacketFamily N κ ι :=
  P.family.horizontalRescale P.topLength P.topLength_pos

theorem family_derivative (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.family.wave j u k y) x‖ ≤ (P.family.constant/P.family.length j)*
      (lineEnvelope (P.family.centerX j u) (P.family.length j) 3 x*
        lineEnvelope (P.family.centerZ j u) P.width 2 y) := by
  apply (P.raw_derivative_bound 0 j u k y x).trans
  change _ ≤ (P.constant/P.length j)*_
  rw [P.family_centerX,P.family_centerZ]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg P.constant_pos.le (P.length_pos j).le)
  exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
    (lineEnvelope_antitone _ _ _ (Nat.le_trans (by decide : 2 ≤ 3) P.order_ge_three))
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem referencePlanarFamily_derivative (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.referencePlanarFamily.wave j u k y) x‖ ≤
      (P.referencePlanarFamily.constant/P.referencePlanarFamily.length j)*
        (lineEnvelope (P.referencePlanarFamily.centerX j u) (P.referencePlanarFamily.length j) 3 x*
          lineEnvelope (P.referencePlanarFamily.centerZ j u) P.width 2 y) := by
  change ‖deriv (schwartzDilation (P.family.wave j u k y) P.topLength P.topLength_pos.ne') x‖ ≤ _
  rw [schwartzDilation_deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.topLength_pos]
  dsimp only [referencePlanarFamily]
  rw [PlanarPacketFamily.horizontalRescale_centerX,PlanarPacketFamily.horizontalRescale_length,
    PlanarPacketFamily.horizontalRescale_centerZ,
    lineEnvelope_horizontalDilation _ _ P.topLength _ _ P.topLength_pos.ne']
  have h := mul_le_mul_of_nonneg_left (P.family_derivative j u k y (P.topLength*x)) P.topLength_pos.le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change (P.constant/(P.length j/P.topLength))*_ = _
  field_simp [(P.length_pos j).ne',P.topLength_pos.ne']
  change P.constant * _ * _ * P.length j = P.length j * _ * _ * P.constant
  ring

variable (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def referenceAnalyzedLine (y : ℝ) : LinePacketFamily N κ ι :=
  P.referencePlanarFamily.analyzedLine d
    (fun z => v (z.1,P.topLength*z.2))
    (hv.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun z => g (z.1,P.topLength*z.2))
    (hg.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd)))
    (fun _z => hg1 _) y (fun j u k x => P.referencePlanarFamily_derivative j u k y x)

@[simp] theorem referenceAnalyzedLine_wave (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).wave j u k x =
      P.raw 0 j u k y (P.topLength*x) := rfl

@[simp] theorem referenceAnalyzedLine_topLength (y : ℝ) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).topLength = 1 := by
  change P.topLength/P.topLength = 1
  exact div_self P.topLength_pos.ne'

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMixedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference moments with distinct analyzing and synthesizing profiles.
The selector is frozen only in the analyzing coefficient; it is not
multiplied into the synthesis a second time. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

def mixedReferenceLine (y : ℝ) : LinePacketFamily N κ ι :=
  let A := (P.frozenProfile c hc).referenceAnalyzedLine d v hv g hg hg1 y
  let S := (P.withProfile alt hAlt).referenceAnalyzedLine d v hv g hg hg1 y
  { S with coeff := A.coeff, coeff_norm := A.coeff_norm }

@[simp] theorem mixedReferenceLine_wave (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).wave j u k x =
      (P.withProfile alt hAlt).raw 0 j u k y (P.topLength*x) := rfl

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSynthesisEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise norms of actual vector packets are controlled by the
same positive main and error envelopes used in the reference tails. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def positiveEnvelope (j : Fin N) (l : P.labels j) (u : Item j l) (y x : ℝ) : ℝ :=
  lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 3 x*
    lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 2 y

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledPositiveSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source coefficient supplies the positive per-length
main/error bound for every residual subset, with original synthesis waves. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalMainScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ l : P.labels j, ∑ u : Item j l,
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledVariationSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed masked variation uses the full original analyzing
coefficients. Its centered main part has the narrow-slot variation
bound; its angular error is bounded by the positive physical error
sum, using the carrier-free synthesis envelope. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

def physicalMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalMultiplierCoefficient t b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

def physicalMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum (fun j => P.physicalMaskedBand
    alt hAlt t b v g T L A y j x)) N

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem eligible_of_add (g : AngularGrid) {cutoff precision : ℝ}
    (hp : 0 ≤ precision) (base steps : ℕ)
    (h : g.eligible cutoff precision (base + steps)) :
    g.eligible cutoff precision base := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    exact g.eligible_parent hp (base + steps) (by simpa only [Nat.add_succ] using h)

theorem eligible_of_le (g : AngularGrid) {cutoff precision : ℝ} (hp : 0 ≤ precision)
    {base level : ℕ} (hle : base ≤ level) (h : g.eligible cutoff precision level) :
    g.eligible cutoff precision base := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.eligible_of_add hp base steps h

/-- The extra tops come from nearby next-level cells outside the immediate
parent, and all belong to the same block ancestor. -/
def outsideNearTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) : Finset ι := by
  classical
  exact (g.cellTops tops slope precision cutoff base (g.index base s)).filter fun i =>
    g.eligible cutoff (precision i) (level + 1) ∧
    g.neighbors (level + 1) gap (g.index (level + 1) s) (g.index (level + 1) (slope i)) ∧
    g.index level (slope i) ≠ g.index level s

def boundaryTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) : Finset ι := by
  classical
  exact g.cellTops tops slope precision cutoff level (g.index level s) ∪
    g.outsideNearTops tops slope precision cutoff base level gap s

def boundaryMass (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (base level : ℕ) (gap s : ℝ) (x : X) : ℝ :=
  ∑ i ∈ g.boundaryTops tops slope precision cutoff base level gap s, weight i x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem exists_ineligible (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) :
    ∃ n : ℕ, ¬g.eligible cutoff precision n := by
  have hG : (1 : ℝ) < g.branching := by
    exact_mod_cast (show 1 < g.branching by have := g.branching_ge_two; omega)
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near
    (le_max_left 1 (cutoff / precision)) hG
  refine ⟨n + 1, ?_⟩
  unfold eligible
  have h := (div_lt_iff₀ hp).mp ((le_max_right 1 (cutoff / precision)).trans_lt hn)
  nlinarith

def lastEligible (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) : ℕ :=
  Nat.find (g.exists_ineligible cutoff precision hp) - 1

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopping-level bands are intervals of the original source length
index. This is the bridge from interval concentration to summation by
parts over angular stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def rawBand (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (j : Fin N) (x y : ℝ) : EuclideanSpace ℂ κ :=
  vectorPacketSynthesis (fun p : Σ l : P.labels j, Item j l => coeff j p.1 p.2)
    (fun p k => P.raw i j p.1 p.2 k y) x

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularPacketAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet amplitudes for the actual translated angular grid.
The stopping level belongs to the packet, independently of when its
assigned top loses eligibility. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {σ E : Type*} [AddCommMonoid E] [Module ℂ E]

def packetPathProduct (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (lower upper : ℕ) (slope : ℝ) : ℂ :=
  ∏ j ∈ Finset.Ico lower upper, transition j (g.index (j + 1) slope)

def packetSet (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (level : ℕ) (cell : ℤ) : Finset σ := by
  classical
  exact packets.filter (fun s => g.index level (slope s) = cell ∧ level ≤ stop s)

def packetAmplitude (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (level : ℕ) (cell : ℤ) : E :=
  ∑ s ∈ g.packetSet packets slope stop level cell,
    g.packetPathProduct transition level (stop s) (slope s) • base s

def packetResidual (g : AngularGrid) (packets : Finset σ) (slope : σ → ℝ) (stop : σ → ℕ)
    (base : σ → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) : E := by
  classical
  exact ∑ s ∈ (g.packetSet packets slope stop lower cell).filter (fun s => stop s < upper),
    g.packetPathProduct transition lower (stop s) (slope s) • base s

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAnalyticWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic transition weights for the shared angular packet family.
The exact modulus is the child-to-boundary mass ratio raised to the
real part of the corresponding complex parameter. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

def analyticTransition (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) : ℂ :=
  Complex.exp (phase level * (Real.log (mass (level + 1) cell / boundary level cell) : ℂ))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

def sourceBoundaryMass (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (level : ℕ) (cell : ℤ) (x : X) : ℝ :=
  g.boundaryMass tops slope precision cutoff weight (level+1-K) level
    (gap level) (g.center (level+1) cell) x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

def sourceTransition (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X) :
    ℕ → ℤ → ℂ :=
  analyticTransition (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x) phase

def sourcePacketBase (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : σ → E) (a : ℝ) (x : X) (s : σ) : E :=
  ((g.mass tops slope precision cutoff weight (stop s)
    (g.index (stop s) (slope (assigned s))) x ^ (-a) : ℝ) : ℂ) • value s

def sourcePacketAmplitude (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E)
    (phase : ℕ → ℂ) (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) : E :=
  g.packetAmplitude packets (fun s => slope (assigned s)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x) level cell

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAmplitudeIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shared source amplitude is entire on every affine complex
line. Its equal-coordinate value gives exactly the boundary-weighted
packet sum, and its block identity uses the same amplitude for all shifts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

def sourceBoundaryCoefficient (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (N : ℕ) (top : ι) (a : ℝ) (x : X) : ℝ :=
  ∏ j ∈ Finset.range N,
    (g.mass tops slope precision cutoff weight j (g.index j (slope top)) x /
      g.sourceBoundaryMass tops slope precision cutoff weight K gap j
        (g.index (j+1) (slope top)) x)^a

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ResidualOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Abel summation bounds the actual weighted packet increments by the
unweighted maximum over subintervals of their common prefix sequence. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def packetPrefix {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) : E :=
  ∑ j ∈ Finset.range n, f j

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_VertexIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrating the vertex amount

The actual finite terminal flow gives pointwise good-path domination on the
large-mass region. Integrating that domination together with the
small-mass estimate extracts the normalized vertex energy from its
nonnegative amount. This is the finite nonnegative assembly in §11.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ ι : Type*} [MeasurableSpace α] [Fintype κ] [Fintype ι] {N : ℕ}

attribute [local instance] Classical.propDecidable

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual vertex amount from §11. -/
def vertexAmount (n : ℝ) (A : E) (a p : ℝ) : ℝ := n + n ^ (a - p) * ‖A‖ ^ p

end Energy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LocalMinimaSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted independent-set selection by local minima of a size-biased order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev IndependentSelection (G : ι → ι → Prop) :=
  {s : Finset ι // (s : Set ι).Pairwise (fun i j => ¬G i j)}

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SkippedLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging along selected generations of the actual line grid. Angular
blocks may have different numbers of steps; no uniform block length is needed. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.FiniteLineGrid

/-- The ancestor map across any number of generations of the same grid. -/
def ancestor (g : FiniteLineGrid) (steps : ℕ) (i : Fin (g.branching^g.depth)) :
    Fin (g.branching^g.depth) :=
  ⟨i.val/g.branching^steps,(Nat.div_le_self _ _).trans_lt i.isLt⟩

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineWindow
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual coarse line cell carries a local grid with exactly the same
fine partitions as the global line grid. This identifies the local
prediction factors before they are patched over coarse cells. -/

noncomputable section
open Set
namespace LipschitzHilbert.FiniteLineGrid

def lineWindow (g : FiniteLineGrid) (coarse i depth : ℕ) : FiniteLineGrid where
  branching := g.branching
  branching_pos := g.branching_pos
  origin := g.origin+g.meshWidth coarse*i
  width := g.meshWidth coarse
  width_pos := g.meshWidth_pos coarse
  depth := depth

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShiftedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted block endpoints of §8. The first block is allowed
to be shorter. Every transition has one phase tag, and each completed
block contains its distinguished phase exactly at the last transition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

def endpoint (σ : Fin K) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 1 + σ.val + j * K

@[simp] theorem endpoint_zero (σ : Fin K) : endpoint σ 0 = 0 := rfl

@[simp] theorem endpoint_succ (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 1) = 1 + σ.val + j * K := rfl

theorem endpoint_strictMono (_hK : 0 < K) (σ : Fin K) : StrictMono (endpoint σ) := by
  apply strictMono_nat_of_lt_succ
  intro j
  cases j with
  | zero => simp
  | succ j => simp only [endpoint_succ, Nat.succ_mul]; omega

end LipschitzHilbert.ShiftedBlocks

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path mass at shifted block endpoints is set to zero as soon as
the distinguished top becomes ineligible, even if other tops continue.
The actual drop has the same factor-two reference-window comparison,
including this terminal block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def shiftedPathMass {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (x : X) (j : ℕ) : ℝ :=
  if g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j) then
    g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x else 0

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMassStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite mass stopping index. A terminal ineligible top has
zero path mass, so the source cutoff is attained without a positive lower
bound on any individual top weight. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def firstMassStop (n : ℕ → ℝ) (count : ℕ) (M : ℝ) : ℕ :=
  if h : ∃ j : ℕ, j ≤ count ∧ n j ≤ M then Nat.find h else count

namespace AngularGrid

/-- One common finite terminal generation works for every point: the
chosen top has become ineligible there, independently of its weight. -/
theorem exists_shifted_terminal {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) :
    ∃ count : ℕ, ¬g.eligible cutoff precision (ShiftedBlocks.endpoint σ count) := by
  obtain ⟨count,hcount⟩ := g.exists_ineligible cutoff precision hp
  refine ⟨count,fun he => hcount (g.eligible_of_le hp.le ?_ he)⟩
  have h := (ShiftedBlocks.endpoint_strictMono hK σ).id_le count
  exact h

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceMarkedPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marking belongs to an entire coarse line cell. On every unmarked
cell the prediction factor is exactly one. In particular a cell containing
an inactive point cannot contribute a marked factor. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace LipschitzHilbert.FiniteLineGrid
attribute [local instance] Classical.propDecidable

def markedValue (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (value : ℝ → ℝ) (x : ℝ) : ℝ :=
  if marked (g.index coarse x).val then value x else 1

def markedError (g : FiniteLineGrid) (coarse : ℕ) (marked : ℕ → Prop)
    (error : ℝ → ℝ) (x : ℝ) : ℝ :=
  if marked (g.index coarse x).val then error x else 0

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's marking rule uses the infimum of the parent mass
and the supremum of its absolute drop over the entire line cell. The
possible unmarked large drop is the last active index, hence is unique. -/

noncomputable section
open Set
namespace LipschitzHilbert

/-- The exact two inequalities in the source's cell marking rule. -/
def sourceMarkedCell (I : Set ℝ) (n h : ℝ → ℝ) (M : ℝ) : Prop :=
  M < sInf (n '' I) ∧ (1/2:ℝ) ≤ sSup (h '' I)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source node ratio and its snapshot graph predictor, with the original
child amplitudes and masses kept explicit. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The exact source prediction in mass-normalized child variables. -/
def sourcePredictionValue (p μ n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) : ℝ :=
  energyRatio p (1+∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p)
    (∑ i, (((c i/n)^(1-μ):ℝ):ℂ) • (lam i • ((c i)^(μ-1) • A i)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockChildren
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual block children are the nonempty eligible-top cells. Their
canonical representatives are slopes of eligible tops, including cells
whose packet amplitude is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def sourceBlockCells {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ) : Finset ℤ :=
  ((g.cellTops tops slope precision cutoff lower parent).filter
    (fun t => g.eligible cutoff (precision t) upper)).image (fun t => g.index upper (slope t))

def sourceBlockTop {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) : ι :=
  (Finset.mem_image.mp c.property).choose

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized prediction is exactly the source node ratio with its
packet residual removed. The denominator retains the stopped-top mass
and every nonempty eligible child, including zero-amplitude children. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {ι κ : Type} [Fintype ι] [Fintype κ]

def sourceNodeDenominator (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ)
    (α p : ℝ) : ℝ := n+∑ i, c i^(α-p)*‖A i‖^p

def sourceNodeRatio (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ)
    (α p : ℝ) (parentAmplitude : EuclideanSpace ℂ κ) : ℝ :=
  vertexAmount n parentAmplitude α p/sourceNodeDenominator n c A α p

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact propagation of source residual packets. The same angular
transition product occurs at every shift. A packet continuing in the
path child therefore acquires a coefficient depending only on its stop
level; Abel summation applies to one fixed raw packet prefix. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {ι X : Type*}

def sourceContinuingPackets (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (packets : Finset σ) (assigned : σ → ι)
    (upper : ℕ) (pathSlope : ℝ) : Finset σ :=
  packets.filter (fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper
    (g.index upper pathSlope))

end AngularGrid

namespace AngularGrid
variable {σ ι X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The residual subset is fixed by the path and stopping levels. It
does not depend on the point at which the amplitude is evaluated. -/
def fixedPathResidualPackets (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (level : ℕ → ℕ) (count : ℕ) (pathSlope : ℝ) : Finset σ :=
  packets.filter (fun q => ∃ j < count, (level j ≤ stop q ∧ stop q < level (j+1)) ∧
    assigned q ∈ g.cellTops tops slope precision cutoff (level (j+1))
      (g.index (level (j+1)) pathSlope))

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed reference collection is a literal restriction of the
original labels. Its new reference coordinates keep every selected
profile, integer site and physical packet unchanged. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def referenceLabels (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N) :
    Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l ∈ P.labels j,
    P.length j ≤ referenceLength ∧
      |oldSlope+P.rowSlope j ⟨l,h⟩-newSlope| ≤ cone*w/P.length j)

def referenceOriginalLabel (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

theorem referenceLabel_bounds (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (l : P.referenceLabels oldSlope newSlope referenceLength cone w j) :
    P.length j ≤ referenceLength ∧
      |P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
        (oldSlope-newSlope)| ≤ cone*w/P.length j := by
  obtain ⟨h,hshort,hangle⟩ := (Finset.mem_filter.mp l.property).2
  have heq : (⟨l.val,h⟩ : P.labels j) =
      P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l := Subtype.ext rfl
  rw [heq] at hangle
  refine ⟨hshort,?_⟩
  convert hangle using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

/-- Only labels in the fixed short reference cone remain. All spatial
items in those labels retain the original lattice and profile. -/
def referenceFamily (oldSlope newSlope referenceLength cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w) : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := F*cone
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := mul_nonneg hF hcone
  labels := P.referenceLabels oldSlope newSlope referenceLength cone w
  originX := fun j l => P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  originZ := fun j l =>
    P.originZ j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+
      (oldSlope-newSlope)*P.originX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  rowSlope := fun j l =>
    P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+(oldSlope-newSlope)
  frequency := P.frequency
  site := fun j l => P.site j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  site_injective := fun j l => P.site_injective j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile := fun j l => P.profile j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  profile_bound := fun j l => P.profile_bound j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)
  shear_bound := by
    intro j l
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    change |(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+(oldSlope-newSlope))*P.length j/P.width| ≤ 1
    rw [abs_div,abs_mul,abs_of_pos (P.length_pos j),abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr (((le_div_iff₀ (P.length_pos j)).mp h).trans hwide)
  carrier_bound := by
    intro j l k
    have h := (P.referenceLabel_bounds oldSlope newSlope referenceLength cone w j l).2
    have hr := (le_div_iff₀ (P.length_pos j)).mp h
    change |P.frequency k*(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)+(oldSlope-newSlope))*P.length j| ≤ F*cone
    rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j),mul_assoc]
    calc
      _ ≤ (F/w)*(cone*w) := mul_le_mul (hfrequency k) hr
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F*cone := by field_simp

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

abbrev RefLabel (j : Fin N) := P.referenceLabels oldSlope newSlope referenceLength cone w j

@[simp] theorem referenceFamily_length (j : Fin N) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).length j =
      P.length j := rfl

@[simp] theorem referenceFamily_actualX (j : Fin N)
    (l : P.RefLabel oldSlope newSlope referenceLength cone w j) (u : Item j l) :
    (P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency).actualX j l u =
      P.actualX j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common reference lattice collects the uniquely assigned packets
from all tops. Disjointness is imposed on the actual sites, not paid for
by summing bounds over top labels. Profiles and waves are unchanged. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

namespace SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Retain the common scale/label geometry while supplying actual
packet sites and profiles from a subcollection or disjoint union. -/
def referenceItems (I : ∀ j, Label j → Type) [∀ j l, Fintype (I j l)]
    (site : ∀ j (l : P.labels j), I j l → ℤ×ℤ)
    (hinj : ∀ j l, Function.Injective (site j l))
    (profile : ∀ j (l : P.labels j), I j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hprofile : ∀ j l u k, planarProfileConstant (profile j l u k) (2*P.order) ≤ P.profileBound) :
    SourceLabeledLattice N κ Label I where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.labels
  originX := P.originX
  originZ := P.originZ
  rowSlope := P.rowSlope
  frequency := P.frequency
  site := site
  site_injective := hinj
  profile := profile
  profile_bound := hprofile
  shear_bound := P.shear_bound
  carrier_bound := P.carrier_bound

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLabeledPacketRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any fixed residual packet subset is itself a lattice family, with
unchanged geometry, analyzing integrals and alternate synthesis waves.
Restricting the item fibers preserves the lattice constants exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def RestrictedPacketItem (Q : Finset P.PacketIndex) (j : Fin N) (l : Label j) :=
  {u : Item j l // ∃ h : l ∈ P.labels j, (⟨j,⟨⟨l,h⟩,u⟩⟩ : P.PacketIndex) ∈ Q}

instance restrictedPacketItemFintype (Q : Finset P.PacketIndex) (j : Fin N) (l : Label j) :
    Fintype (P.RestrictedPacketItem Q j l) := by
  unfold RestrictedPacketItem
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def restrictPackets (Q : Finset P.PacketIndex) :
    SourceLabeledLattice N κ Label (P.RestrictedPacketItem Q) :=
  P.referenceItems (P.RestrictedPacketItem Q)
    (fun j l u => P.site j l u.val)
    (fun j l => (P.site_injective j l).comp Subtype.val_injective)
    (fun j l u k => P.profile j l u.val k)
    (fun j l u k => P.profile_bound j l u.val k)

@[simp] theorem restrictPackets_absoluteConstant (Q : Finset P.PacketIndex) :
    (P.restrictPackets Q).absoluteConstant = P.absoluteConstant := rfl

@[simp] theorem restrictPackets_constant (Q : Finset P.PacketIndex) :
    (P.restrictPackets Q).constant = P.constant := rfl

@[simp] theorem restrictPackets_physicalPacket (Q : Finset P.PacketIndex) (t : ℝ)
    (j : Fin N) (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) (k : κ) :
    (P.restrictPackets Q).physicalPacket t j l u k = P.physicalPacket t j l u.val k := rfl

@[simp] theorem restrictPackets_physicalMultiplierCoefficient (Q : Finset P.PacketIndex)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N)
    (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) :
    (P.restrictPackets Q).physicalMultiplierCoefficient t b v g j l u =
      P.physicalMultiplierCoefficient t b v g j l u.val := rfl

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Alternate synthesis profiles are restricted along the same item map. -/
def restrictedAlternate (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) (k : κ) :
    SchwartzMap (ℝ×ℝ) ℂ := alt j l u.val k

include hAlt in
theorem restrictedAlternate_bound (Q : Finset P.PacketIndex) (j : Fin N)
    (l : (P.restrictPackets Q).labels j) (u : P.RestrictedPacketItem Q j l) (k : κ) :
    planarProfileConstant (P.restrictedAlternate alt Q j l u k)
      (2*(P.restrictPackets Q).order) ≤ (P.restrictPackets Q).profileBound :=
  hAlt j l u.val k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAllStrongMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable-scale coordinate maximal functions on the plane, with
uniform strong L² control. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def allHorizontalMaximal (q : ℤ) (f : ℝ×ℝ → ℝ) : ℝ×ℝ → ℝ :=
  monotoneMaximal (fun N : ℕ => horizontalMaximal q (N:ℤ) (2*N) f)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridPlane
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three-grid coordinate majorants on the plane. The construction has
uniform bounds both on L² and on bounded functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

def threeHorizontalMaximal (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  ∑ q : GridChoice, allHorizontalMaximal q.val f z

def threeVerticalMaximal (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  threeHorizontalMaximal (f ∘ Prod.swap) z.swap

def threeStrongMaximal (f : ℝ×ℝ → ℝ) : ℝ×ℝ → ℝ :=
  threeHorizontalMaximal (threeVerticalMaximal f)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining transverse tail in the long-tree density estimate:
412 powers in squared energy absorb twice the density loss 203, leaving
the summable sixth power. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def transverseTailConstant : ℝ := ∑' n : ℤ, ((1+|(n:ℝ)|)^6)⁻¹

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVectorSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar packet coordinates assemble into an actual vector
Schwartz function. Fourier cutoffs pass through the same coordinates. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]
attribute [local instance] Classical.propDecidable

def vectorCoordinate (k : κ) : EuclideanSpace ℂ κ →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : κ => ℂ) k

omit [Fintype κ] in
@[simp] theorem vectorCoordinate_apply (k : κ) (v : EuclideanSpace ℂ κ) :
    vectorCoordinate k v=v k := rfl

def vectorCoordinateInjection (k : κ) : ℂ →L[ℂ] EuclideanSpace ℂ κ :=
  ContinuousLinearMap.toSpanSingleton ℂ (PiLp.single 2 k 1)

@[simp] theorem vectorCoordinateInjection_apply (k j : κ) (z : ℂ) :
    vectorCoordinateInjection k z j=if j=k then z else 0 := by
  classical
  simp only [vectorCoordinateInjection,ContinuousLinearMap.toSpanSingleton_apply,
    PiLp.smul_apply,PiLp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

def vectorSchwartz {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : κ → SchwartzMap D ℂ) : SchwartzMap D (EuclideanSpace ℂ κ) :=
  ∑ k, (f k).postcompCLM (vectorCoordinateInjection k)

@[simp] theorem vectorSchwartz_apply {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : κ → SchwartzMap D ℂ) (x : D) (k : κ) : vectorSchwartz f x k=f k x := by
  classical
  simp only [vectorSchwartz,sum_apply,SchwartzMap.postcompCLM_apply,WithLp.ofLp_sum,Finset.sum_apply,
    vectorCoordinateInjection_apply]
  simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums of the original scalar planar packets are actual vector
Schwartz maps, and their coordinate cutoffs follow from those of the
nonzero summands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Schwartz-map representative of the manuscript's fixed synthesis. -/
def planarSynthesisSchwartz (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  vectorSchwartz (fun k => ∑ i, c i k • f i k)

@[simp] theorem planarSynthesisSchwartz_apply (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    planarSynthesisSchwartz c f z=planarFixedSynthesis c f z := by
  ext k
  simp only [planarSynthesisSchwartz,vectorSchwartz_apply,sum_apply,smul_apply,
    smul_eq_mul,planarFixedSynthesis,WithLp.ofLp_toLp]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeSpectrum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Schwartz representatives and coordinate spectra of tree
partial sums. Only packets longer than the cell scale are used. -/
noncomputable section
open FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ : Type} [Fintype κ]

namespace SourceLabeledLattice
variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def physicalTreePartialSchwartz (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  ∑ j : Fin N, if j.val<n then planarSynthesisSchwartz
    (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
    (fun a k => P.physicalPacket t j a.1 a.2 k) else 0

@[simp] theorem physicalTreePartialSchwartz_apply (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) :
    P.physicalTreePartialSchwartz t c n z=P.physicalTreePartial t c n z := by
  unfold physicalTreePartialSchwartz physicalTreePartial packetPartialSum
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [planarSynthesisSchwartz_apply,zero_apply]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue stripwise estimates over the actual countable Whitney partition.
Finite-subfamily bounds imply integrability and the same global bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)

abbrev CellIndex := {p : ℤ×ℤ // Whitney tiles x ell p.1 p.2}

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongCellMask
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent-witness density test supplies the common mask and
mass bounds on the disjoint cells used in long-tree integration. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

abbrev DensityWhitneyCell := CellIndex (Finset.univ : Finset P.PacketIndex)
  (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenWhitneyLocal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frozen local function on the actual typed Whitney partition,
and transport of the finite long-tree estimate to those indices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
open SourceWhitney
attribute [local instance] Classical.propDecidable

def extendWhitneyMask (Omega : P.DensityWhitneyCell → Set ℝ) (p : ℤ×ℤ) : Set ℝ :=
  if hp : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2
  then Omega ⟨p,hp⟩ else ∅

@[simp] theorem extendWhitneyMask_val (Omega : P.DensityWhitneyCell → Set ℝ)
    (i : P.DensityWhitneyCell) : P.extendWhitneyMask Omega i.val=Omega i := by
  simp only [extendWhitneyMask,dite_eq_left i.property]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def referenceEnvelopeConstant : ℝ :=
  ((2^P.order*P.profileBound)*P.ratioBound^2)*3^(2*P.order)

def referenceTreeConstant (C : ℝ) (B K : ℕ) (Lip : ℝ) : ℝ :=
  27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*P.profileBound+
  Real.sqrt (C*(B:ℝ))*P.referenceEnvelopeConstant+
  32^106*(B:ℝ)*P.referenceEnvelopeConstant*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
    (32*2^203)*9*transverseTailConstant

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDropTreeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite selected-tree sums after a change of starting scale. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

@[simp] theorem dropScales_treeConstant (first : Fin N) (C : ℝ) (B K : ℕ) (Lip : ℝ) :
    (P.dropScales first).referenceTreeConstant C B K Lip=P.referenceTreeConstant C B K Lip := rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataVectorEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference-direction scalar envelope controls the actual
componentwise packet synthesis without a frequency-dimension factor. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A coefficient vector multiplying the original physical packet. -/
def packetVector
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPartial
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical scale partial sums and their continuous interval maximum
for unrestricted packet data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable


def physicalTreePartial (P : PacketLatticeData N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  packetPartialSum (fun j => planarFixedSynthesis
    (fun q : Σ l : P.labels j, Item j l => c j q.1 q.2)
    (fun q k => P.physicalPacket t j q.1 q.2 k) z) n

def physicalTreeMaximal (P : PacketLatticeData N κ Label Item) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  intervalOscillation (fun n => P.physicalTreePartial t c n z) N 0 N

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedPrefix
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distant longer packets in a fixed selected tree form an actual
initial scale segment, so their norm is bounded by its interval maximum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def onPackets (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  if (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈S then c j l u else 0

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataFarGram
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distant-scale Gram contribution of an actual selected tree is
bounded by the short-packet envelope paired with its interval maximum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def longPacketSum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (T : Finset P.PacketIndex) (gap : ℕ) (i : Fin N) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q∈T.filter (fun q => q.1.val+gap≤ i.val), P.packetVector c q z

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedGram
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact far-Gram grouping over the actual selected records, followed
by the global near/far energy assembly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def farPairing (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S T : Finset P.PacketIndex) (gap : ℕ) : ℂ :=
  ∑ s∈S, ∫ z, inner ℂ (P.packetVector c s z) (P.longPacketSum c T gap s.1 z)
    ∂volume.prod volume

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedDuality
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

namespace PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- Coefficients of the original physical packets, before selector masks. -/
def ordinaryCoefficient (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) g ⟨j,⟨l,u⟩⟩

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedBoxSeparation
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distant-scale boxes from the actual positive size-selection run cannot
overlap in the common direction of an interacting longer tree. -/
noncomputable section
open Set
namespace LipschitzHilbert

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A packet's spatial box expressed in a fixed comparison direction. -/
def directionBox (t : ℝ) (q : P.PacketIndex) : SlopeBox where
  x := P.actualX q.1 q.2.1 q.2.2
  y := P.actualZ q.1 q.2.1 q.2.2
  slope := t
  length := P.length q.1
  width := P.width
  length_pos := P.length_pos q.1
  width_pos := P.width_pos

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataInteractionGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short family used in the selected-tree argument is defined by
actual nonzero Gram interactions. Its angular geometry follows from the
packet spectra, rather than being a separate analytic premise. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def interactingShortPackets (S T : Finset P.PacketIndex) (gap : ℕ) : Finset P.PacketIndex :=
  S.filter fun s => ∃ q∈T, q.1.val+gap ≤ s.1.val ∧ ∃ k : κ,
    (∫ z, inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume)≠0

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PacketDataSignedInteractionPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Gram-interacting short packets from one selected top obey
the packing estimate needed by the far-tree bound. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketLatticeData.SizeStoppingRun
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable {P : PacketLatticeData N κ Label Item} {negative : Bool}
  {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

def selectedEnvelopePackingConstant (cb : ℝ) (gap M Q : ℕ) : ℝ :=
  (gap:ℝ)*((((2*Q+1)*M:ℕ):ℝ)*(((1+(1:ℝ)^2)*(1+((1:ℝ)*(1+cb/4))^2))*(4*Real.pi)^2))

end LipschitzHilbert.PacketLatticeData.SizeStoppingRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def selectedNearConstant (P : PacketLatticeData N κ Label Item) (gap M Q : ℕ) : ℝ :=
  ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*
    ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)

def selectedFarConstant (P : PacketLatticeData N κ Label Item)
    (cb D C : ℝ) (packGap M Q : ℕ) : ℝ :=
  (4*P.profileBound*D)^2*256*
    (82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
      1296*Real.pi^2*(((3*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelConfig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and selector data for the ordinary model. None of
these parameters depends on the input function or the tested set. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure OrdinaryModelConfig (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex) where
  cStar : ℝ
  cEta : ℝ
  CEta : ℝ
  cb : ℝ
  Cv : ℝ
  w : ℝ
  tau : ℝ
  epsilon : ℝ
  A : ℝ
  margin : ℝ
  F : ℝ
  radius : ℝ
  Lip : ℝ
  M : ℕ
  Q : ℕ
  gap : ℕ
  packGap : ℕ
  R : ℕ
  K : ℕ
  D0 : ℕ
  cell : ∀ j, P.labels j → ℤ
  grid : ℤ
  selector : ∀ j, P.labels j → κ → ℝ → ℂ
  hcStar : 0 ≤ cStar
  hcEta : 0 < cEta
  hCEta : 0≤CEta
  hCv : 0≤Cv
  hcb : 0 < cb
  hcbQuarter : cb≤1/4
  hspectral : cStar < cEta*cb
  hepsilon : 0<epsilon
  hw : 0<w
  hW : w≤P.width
  hF : 0≤F
  hfreq : ∀ k, |P.frequency k|≤F/w
  hgap : (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4
  hpack : (1+cb/4)/(2:ℝ)^packGap ≤ cb/4
  hmargin : cb/2 ≤ margin-cStar/cEta
  hA : 2*(1+(1+cb/4))+1/2≤A
  hQ : cb/4≤Q
  hQnear : 2*cStar/cEta≤Q
  hR : (1:ℝ)≤R
  horder : 207≤P.order
  hD0 : A≤D0
  htime : tau≤P.topLength
  hwide : 1 ≤ radius+1
  hK : radius+1≤(2:ℝ)^K
  hLip : 0≤Lip
  hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M
  hrow : ∀ q∈initial, P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength)
    grid q.1.val (cell q.1 q.2.1)
  hlength : ∀ q∈initial, P.length q.1≤tau
  heps : ∀ q∈initial, epsilon ≤ cb*(w/P.length q.1)/4
  spectrum : ∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
    |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta
  margin_spectrum : ∀ s∈initial, ∀ k xi et,
    planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,et)≠0 →
    Icc (-xi/et-margin*(w/P.length s.1)) (-xi/et+margin*(w/P.length s.1))⊆
      scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)
  bin : ∀ q∈initial, ∀ k xi et,
    planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
      |et-P.frequency k|≤Cv/P.width
  measurable : ∀ j l k, Measurable (selector j l k)
  bounded : ∀ j l k s, ‖selector j l k s‖≤1
  away : ∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|
  support : ∀ j l k s, selector j l k s≠0 →
    s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)
  radius_bound : ∀ j l k s, selector j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)
  near : ∀ j l k s t, |s-t|≤w/P.length j →
    ‖selector j l k s-selector j l k t‖≤Lip*(|s-t|/(w/P.length j))

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def sizeAreaConstant (d : OrdinaryModelConfig P initial) (CS : ℝ) : ℝ :=
  4*(selectedNearConstant P d.gap d.M d.Q+
    2*Real.sqrt (2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q))

def stepConstant (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  Real.sqrt 2*(2*(625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip)+
    ((((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip)*d.sizeAreaConstant CS)

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrdinaryModelNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed choices of the separation gaps in the ordinary packet model.
They depend only on the spectral and selector constants, never on the
number of scales, sites, carriers, or the input functions. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

structure OrdinaryModelNumerics (cStar cEta cb radius : ℝ) where
  gap : ℕ
  packGap : ℕ
  K : ℕ
  hgap : (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4
  hpack : (1+cb/4)/(2:ℝ)^packGap ≤ cb/4
  hK : radius+1≤(2:ℝ)^K

theorem exists_ordinary_model_numerics (cStar cEta cb radius : ℝ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hcb : 0 < cb)
    (hsmall : cStar/cEta < cb/4) :
    Nonempty (OrdinaryModelNumerics cStar cEta cb radius) := by
  let a := cStar/cEta
  let delta := cb/4-a
  have ha : 0≤a := div_nonneg hcStar hcEta.le
  have hd : 0<delta := sub_pos.mpr hsmall
  obtain ⟨gap,hgap⟩ := pow_unbounded_of_one_lt ((a+1)/delta) (by norm_num : (1:ℝ)<2)
  obtain ⟨packGap,hpack⟩ := pow_unbounded_of_one_lt ((1+cb/4)/(cb/4))
    (by norm_num : (1:ℝ)<2)
  obtain ⟨K,hK⟩ := pow_unbounded_of_one_lt (radius+1) (by norm_num : (1:ℝ)<2)
  refine ⟨⟨gap,packGap,K,?_,?_,hK.le⟩⟩
  · have hp : 0<(2:ℝ)^gap := pow_pos (by norm_num) _
    have hp' : 0<(2:ℝ)^(gap+1) := pow_pos (by norm_num) _
    have hg : a+1<2^gap*delta := (div_lt_iff₀ hd).mp hgap
    have hg' : (a+1)/(2:ℝ)^(gap+1)≤delta := by
      apply (div_le_iff₀ hp').mpr
      rw [pow_succ]
      nlinarith
    have he : a*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) =
        a+(a+1)/(2:ℝ)^(gap+1) := by ring
    change a*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1) ≤ cb/4
    rw [he]
    dsimp only [delta] at hg'
    linarith
  · have hp : 0<(2:ℝ)^packGap := pow_pos (by norm_num) _
    have hc : 0 < cb/4 := by positivity
    exact (div_le_iff₀ hp).mpr (by
      have h := (div_lt_iff₀ hc).mp hpack
      nlinarith)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrdinaryModelConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the ordinary model from its geometric data. The numerical
parameters are fixed before the finite packet collection is chosen. The
auxiliary positive cutoff is chosen below every packet's angular scale. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem length_le_topLength (P : PacketLatticeData N κ Label Item) (j : Fin N) :
    P.length j≤P.topLength := by
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) _)).mpr
  have h : (1:ℝ)≤2^j.val := one_le_pow₀ (by norm_num)
  nlinarith [P.topLength_pos]

def ordinaryModelOfGeometry (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex)
    (cStar cEta CEta cb Cv w F radius : ℝ) (M : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4)
    (num : OrdinaryModelNumerics cStar cEta cb radius)
    (hw : 0<w) (hW : w≤P.width) (hF : 0≤F) (hr : 0 ≤ radius)
    (horder : 207≤P.order) (hfreq : ∀ k, |P.frequency k|≤F/w)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (hrow : ∀ q∈initial, P.rowSlope q.1 q.2.1∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (spectrum : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta)
    (margin_spectrum : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-cb*(w/P.length q.1)) (-xi/et+cb*(w/P.length q.1))⊆
          scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (bin : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (measurable : ∀ j l k, Measurable (selector j l k))
    (bounded : ∀ j l k s, ‖selector j l k s‖≤1)
    (away : ∀ j l k s, selector j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|)
    (support : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (radius_bound : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l| ≤ radius*(w/P.length j))
    (near : ∀ j l k s t, |s-t|≤w/P.length j →
      ‖selector j l k s-selector j l k t‖≤|s-t|/(w/P.length j)) :
    OrdinaryModelConfig P initial where
  cStar := cStar
  cEta := cEta
  CEta := CEta
  cb := cb
  Cv := Cv
  w := w
  tau := P.topLength
  epsilon := cb*w/(4*P.topLength)
  A := 5
  margin := cb
  F := F
  radius := radius
  Lip := 1
  M := M
  Q := 1
  gap := num.gap
  packGap := num.packGap
  R := 1
  K := num.K
  D0 := 5
  cell := cell
  grid := grid
  selector := selector
  hcStar := hcStar
  hcEta := hcEta
  hCEta := hCEta
  hCv := hCv
  hcb := hcb
  hcbQuarter := hcbQuarter
  hspectral := by
    have h : cStar/cEta < cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  hepsilon := div_pos (mul_pos hcb hw) (mul_pos (by norm_num) P.topLength_pos)
  hw := hw
  hW := hW
  hF := hF
  hfreq := hfreq
  hgap := num.hgap
  hpack := num.hpack
  hmargin := by linarith
  hA := by linarith
  hQ := by norm_num; linarith
  hQnear := by
    norm_num only [Nat.cast_one]
    rw [show 2*cStar/cEta=2*(cStar/cEta) by ring]
    linarith
  hR := by norm_num
  horder := horder
  hD0 := by norm_num
  htime := le_rfl
  hwide := by linarith
  hK := num.hK
  hLip := by norm_num
  hlocal := hlocal
  hrow := hrow
  hlength := fun q _ => P.length_le_topLength q.1
  heps := by
    intro q _
    have hl := P.length_pos q.1
    have hle := P.length_le_topLength q.1
    calc
      cb*w/(4*P.topLength) = (cb*w/4)/P.topLength := by ring
      _ ≤ (cb*w/4)/P.length q.1 := div_le_div_of_nonneg_left (by positivity) hl hle
      _ = cb*(w/P.length q.1)/4 := by ring
  spectrum := spectrum
  margin_spectrum := margin_spectrum
  bin := fun s _ => bin s.1 s.2.1 s.2.2
  measurable := measurable
  bounded := bounded
  away := away
  support := support
  radius_bound := radius_bound
  near := by simpa only [one_mul] using near

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThresholdSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform summation over any finite family of dyadic density thresholds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def ordinaryThresholdRatio : ℝ := (2:ℝ)^(-(1/5:ℝ))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniversalEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit uniform model cost, including zero energy, zero tested
measure, and all positive density thresholds. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

def ordinaryDensityUpper : ℝ := max 1 (∫ z, topProfile 203 z ∂volume.prod volume)

namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def modelCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*d.stepConstant CD CS CT

end OrdinaryModelConfig

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelCostPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial dependence of the explicit model cost on the two packet
adaptation bounds. All remaining factors involve fixed geometric data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

 def ordinaryTreeUnitCost (C : ℝ) (B K : ℕ) (Lip : ℝ) : ℝ :=
  27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203+
  Real.sqrt (C*(B:ℝ))+
  32^106*(B:ℝ)*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
    (32*2^203)*9*transverseTailConstant

 def selectedNearUnitCost (gap M Q : ℕ) : ℝ :=
  ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*Real.pi^2)

 def selectedFarUnitCost (cb D C : ℝ) (packGap M Q : ℕ) : ℝ :=
  (4*D)^2*256*(82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
    1296*Real.pi^2*(((3*M:ℕ):ℝ)*C)

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def unitSizeAreaCost (d : OrdinaryModelConfig P initial) (CS : ℝ) : ℝ :=
  4*(selectedNearUnitCost d.gap d.M d.Q+
    2*Real.sqrt (2*selectedFarUnitCost d.cb (Real.sqrt 2) CS d.packGap d.M d.Q))

def unitStepCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  Real.sqrt 2*(2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip)+
    (((4*d.D0+1)^2:ℕ):ℝ)*ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip*d.unitSizeAreaCost CS)

def unitModelCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*d.unitStepCost CD CS CT

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical weights for the bounded-input, unequal-measure estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def reverseThresholdRatio : ℝ := (2:ℝ)^(-(1/20:ℝ))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformCappedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform dyadic removal: all non-geometric constants are chosen before
the translated packet lattice and finite collection. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def boundedSizeCost (d : OrdinaryModelConfig P initial) (CZ : ℝ) : ℝ :=
  1+((3*d.M:ℕ):ℝ)*CZ*P.referenceEnvelopeConstant^2

def reverseStepCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+(2*(625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip)+
    (((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip*
      d.sizeAreaConstant CS)*
    max (Real.sqrt (d.boundedSizeCost CZ)) (Real.sqrt 2)*max U 2

end OrdinaryModelConfig

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformReverseModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reverse estimate from actual finite removals. The four input
constants are independent of packet count, translation and the scale interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def reverseModelCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+(8/(1-reverseThresholdRatio))*d.reverseStepCost CD CS CT CZ U

end OrdinaryModelConfig

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReverseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial dependence of the reverse estimate on packet adaptation.
Its remaining constants use only the fixed geometric parameters. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def reverseCoreUnitCost (d : OrdinaryModelConfig P initial) (CD CS CT : ℝ) : ℝ :=
  2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip)+
    (((4*d.D0+1)^2:ℕ):ℝ)*ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip*
      d.unitSizeAreaCost CS

def unitReverseStepCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+d.reverseCoreUnitCost CD CS CT*
    max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*max U 2

def unitReverseModelCost (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) : ℝ :=
  1+(8/(1-reverseThresholdRatio))*d.unitReverseStepCost CD CS CT CZ U

end LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrdinaryModelConstructionCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cost of the constructed ordinary models is a fixed number.
In particular it has no dependence on the finite lattice or translation. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

def OrdinaryModelNumerics.modelUnitCost {cStar cEta cb radius : ℝ}
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT : ℝ) : ℝ :=
  1+(8*ordinaryDensityUpper/(1-ordinaryThresholdRatio))*
    (Real.sqrt 2*(2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD (3*M) num.K 1)+
      ((21^2:ℕ):ℝ)*ordinaryTreeUnitCost CT (3*M) num.K 1*
        (4*(selectedNearUnitCost num.gap M 1+
          2*Real.sqrt (2*selectedFarUnitCost cb (Real.sqrt 2) CS num.packGap M 1)))))

def OrdinaryModelNumerics.reverseUnitCost {cStar cEta cb radius : ℝ}
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT CZ : ℝ) : ℝ :=
  1+(8/(1-reverseThresholdRatio))*
    (1+(2*(625*densityRadiusConstant^2*ordinaryTreeUnitCost CD (3*M) num.K 1)+
      ((21^2:ℕ):ℝ)*ordinaryTreeUnitCost CT (3*M) num.K 1*
        (4*(selectedNearUnitCost num.gap M 1+
          2*Real.sqrt (2*selectedFarUnitCost cb (Real.sqrt 2) CS num.packGap M 1))))*
      max (Real.sqrt (1+((3*M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*max ordinaryDensityUpper 2)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous packet identity in §2, with the actual convolution
kernels and the exact area normalization. Absolute integrability follows
from L1 kernels and input and a bounded measurable test. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

abbrev planeMeasure : Measure (ℝ × ℝ) := volume.prod volume

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SharpKernelComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint envelopes control sharp truncation versus a telescoped
kernel. The profile conditions are local construction obligations. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def sharpTimeKernel (r R t : ℝ) : ℂ :=
  if r < |t| ∧ |t| < R then (t : ℂ)⁻¹ else 0

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PublishedHilbertInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additional classical one-dimensional input needed only for the
horizontal remainder. Grafakos, Classical Fourier Analysis, 3rd edition,
GTM 249, Springer (2014), Theorem 5.1.12, printed p.323 (PDF p.338),
DOI 10.1007/978-1-4939-1194-3. The maximal Hilbert bound gives this smaller
consequence for differences of two inner truncations. The factor pi from
the book's normalization is absorbed in C. Only p=3/2 and p=4 are used.
This is an explicit proposition, not an axiom or an asserted proof. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def oneDimensionalTruncatedHilbert (r R : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, PacketRepresentation.sharpTimeKernel r R t*f (x-t)

def HorizontalHilbertInput : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, p=3/2 ∨ p=4 →
    ∀ r R : ℝ, 0 < r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^p) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^p)≤C^p*(∫ x, ‖f x‖^p)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RankedMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive integral maximal functions for the line and square grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [MeasurableSpace X]

def rankedMaximal (μ : Measure X) (Q : ι → Set X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RestrictedStrongOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted logarithmic estimate controls the actual L2 operator
norm. A finite truncation's preliminary continuity suffices; its original
continuity bound does not enter the final constant. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

abbrev HilbertLp (μ : Measure X) := Lp (EuclideanSpace ℂ κ) 2 μ

def HasRestrictedLogBound (μ : Measure X)
    (B : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ →L[ℝ] ℂ) (C : ℝ) : Prop :=
  ∀ F G : Set X, MeasurableSet F → MeasurableSet G → μ F≠∞ → μ G≠∞ →
    0<μ.real F → 0<μ.real G →
    ∀ (u v : X → EuclideanSpace ℂ κ), Measurable u → Measurable v →
      (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
      (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
    ∀ (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
      ‖B (hu.toLp u) (hv.toLp v)‖≤C*((1+|Real.log (μ.real F/μ.real G)|)^3)⁻¹*
        Real.sqrt (μ.real F)*Real.sqrt (μ.real G)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ScalarRestrictedStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar complex instance of the proved restricted-to-strong
estimate, transported through the one-dimensional orthonormal basis. -/
noncomputable section
open MeasureTheory Function Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

def HasScalarRestrictedLogBound (mu : Measure X)
    (B : Lp ℂ 2 mu →L[ℝ] Lp ℂ 2 mu →L[ℝ] ℂ) (C : ℝ) : Prop :=
  ∀ F G : Set X, MeasurableSet F → MeasurableSet G → mu F≠∞ → mu G≠∞ →
    0 < mu.real F → 0 < mu.real G →
    ∀ (u v : X → ℂ), Measurable u → Measurable v →
      (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
      (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
    ∀ (hu : MemLp u 2 mu) (hv : MemLp v 2 mu),
      ‖B (hu.toLp u) (hv.toLp v)‖≤C*((1+|Real.log (mu.real F/mu.real G)|)^3)⁻¹*
        Real.sqrt (mu.real F)*Real.sqrt (mu.real G)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SquareMaximalWeakL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weak L1 square maximal majorant using nine fixed grid pairs. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

def squareSup (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun q : GridChoice × GridChoice => gridSquareSup q.1.val q.2.val f z)

def centeredSquare (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  Icc (c.1-r) (c.1+r) ×ˢ Icc (c.2-r) (c.2+r)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineBad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Popular intervals produce maximal bad intervals in two fixed grids. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.DyadicLineGrid

def Bad (q : ℤ) (f : ℝ → ℝ) (β : ℝ) (k j : ℤ) : Prop :=
  β * scale k ≤ ∫ x in cell q k j, f x

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A jointly measurable count of the actual maximal dyadic occurrences. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.DyadicLineGrid

variable {X B : Type*} [MeasurableSpace X]

abbrev Occurrence (B : Type*) := ℤ × B × ℤ × ℤ

def selectedSet (f : B → X × ℝ → ℝ) (top : ℤ) (β : ℝ) (a : Occurrence B) :
    Set (X × ℝ) :=
  {p | a.1 ∈ ({0, 1} : Finset ℤ) ∧
    MaximalBad a.1 top (Bad a.1 (fun x => f a.2.1 (p.1, x)) β) a.2.2.1 a.2.2.2 ∧
    p.2 ∈ cell a.1 a.2.2.1 a.2.2.2}

def selectedCount (f : B → X × ℝ → ℝ) (top : ℤ) (β : ℝ) (p : X × ℝ) : ℝ≥0∞ :=
  ∑' a : Occurrence B, (selectedSet f top β a).indicator 1 p

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineRootCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The count in one grid agrees on a root with the count of its selected descendants. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

abbrev GridOccurrence (B : Type*) := B × ℤ × ℤ

def maximalCell {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ)
    (a : GridOccurrence B) : Set ℝ :=
  if MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2 then cell q a.2.1 a.2.2 else ∅

def gridCount {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ) : ℝ → ℝ≥0∞ :=
  occurrenceCount (maximalCell f q top β)

def RootOccurrence {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ) (j : ℤ) :=
  {a : GridOccurrence B // MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2 ∧
    cell q a.2.1 a.2.2 ⊆ cell q top j}

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicLineRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only a controlled total length of root cells meets a bounded interval. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.DyadicLineGrid

def rootBand (q k : ℤ) (a b : ℝ) : Finset ℤ :=
  Finset.Icc (index q k a) (index q k b)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveLineMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive line maximal functions. Extended integrals give pointwise
monotonicity, including on exceptional lines, which is needed by the
finite rectangle removal algorithm. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

abbrev LineCellIndex := ℤ × ℤ

def positiveGridLine (q : ℤ) (f : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  rankedMaximal volume (fun p : LineCellIndex => cell q p.1 p.2) f

def positiveGridHorizontal (q : ℤ) (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  positiveGridLine q (fun x => f (x,z.2)) z.1

def positiveHorizontal (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun q : GridChoice => positiveGridHorizontal q.val f z)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def referenceCondition (oldSlope newSlope referenceLength cone w : ℝ)
    (j : Fin N) (l : P.labels j) : Prop :=
  P.length j ≤ referenceLength ∧
    |oldSlope+P.rowSlope j l-newSlope| ≤ cone*w/P.length j

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact label restriction and finite tag partitions for the unrestricted
packet family. Neither operation changes a packet or a lattice site. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable {Tag : Type*} [Fintype Tag] (tag : ∀ j, P.labels j → Tag)

/-- Replacing the analyzing profile keeps all physical geometry. -/
def withProfile (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound) :
    PacketLatticeData N κ Label Item :=
  { P with profile := alt, profile_bound := hAlt }

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical main-square and masked-variation tails after exact
recombination of the fixed narrow-label slots. Constants are selected
before the packet family, its scale range, and the physical interval. -/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalMainSquare (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) : ℝ :=
  Real.sqrt (∑ j, P.physicalMainScale t a b v g j y x^2)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveReference
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow main reference family retains only labels active at the
frozen direction. Inactive labels contribute exactly zero, so neither
the square nor the masked variation needs spectral assumptions there. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

def frozenActiveLabels (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l ∈ P.labels j, ∃ k, b j ⟨l,h⟩ k t ≠ 0)

def frozenActiveOriginalLabel (j : Fin N) (l : P.frozenActiveLabels t b j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

def frozenActiveFamily : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.frozenActiveLabels t b
  originX := fun j l => P.originX j (P.frozenActiveOriginalLabel t b j l)
  originZ := fun j l => P.originZ j (P.frozenActiveOriginalLabel t b j l)
  rowSlope := fun j l => P.rowSlope j (P.frozenActiveOriginalLabel t b j l)
  frequency := P.frequency
  site := fun j l => P.site j (P.frozenActiveOriginalLabel t b j l)
  site_injective := fun j l => P.site_injective j (P.frozenActiveOriginalLabel t b j l)
  profile := fun j l => P.profile j (P.frozenActiveOriginalLabel t b j l)
  profile_bound := fun j l => P.profile_bound j (P.frozenActiveOriginalLabel t b j l)
  shear_bound := fun j l => P.shear_bound j (P.frozenActiveOriginalLabel t b j l)
  carrier_bound := fun j l => P.carrier_bound j (P.frozenActiveOriginalLabel t b j l)

@[simp] theorem frozenActiveFamily_constant : (P.frozenActiveFamily t b).constant = P.constant := rfl

@[simp] theorem frozenActiveFamily_physicalPacket (s : ℝ) (j : Fin N)
    (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) (k : κ) :
    (P.frozenActiveFamily t b).physicalPacket s j l u k =
      P.physicalPacket s j (P.frozenActiveOriginalLabel t b j l) u k := rfl

@[simp] theorem frozenActiveFamily_positiveEnvelope (j : Fin N)
    (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) (y x : ℝ) :
    (P.frozenActiveFamily t b).positiveEnvelope j l u y x =
      P.positiveEnvelope j (P.frozenActiveOriginalLabel t b j l) u y x := rfl

@[simp] theorem frozenActiveFamily_raw (i : Fin 3) (j : Fin N)
    (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) (k : κ) (y : ℝ) :
    (P.frozenActiveFamily t b).raw i j l u k y =
      P.raw i j (P.frozenActiveOriginalLabel t b j l) u k y := rfl

@[simp] theorem frozenActiveFamily_alt_raw
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (i : Fin 3) (j : Fin N) (l : (P.frozenActiveFamily t b).labels j)
    (u : Item j l) (k : κ) (y : ℝ) :
    ((P.frozenActiveFamily t b).withProfile
      (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
      (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l))).raw i j l u k y =
      (P.withProfile alt hAlt).raw i j (P.frozenActiveOriginalLabel t b j l) u k y := rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceErrorSupported
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Error moments on a reference interval only use retained packet
lengths. Empty longer scales do not enlarge the interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LineErrorSources
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

/-- Remove the unused long sources without changing either source budget. -/
def restrictLength (P : LineErrorSources N) (H : ℝ) : LineErrorSources N where
  topLength := P.topLength
  topLength_pos := P.topLength_pos
  sourceBound := P.sourceBound
  sourceBound_nonneg := P.sourceBound_nonneg
  sumBound := P.sumBound
  sumBound_nonneg := P.sumBound_nonneg
  source := fun j x => if P.length j ≤ H then P.source j x else 0
  measurable_source := fun j => by
    by_cases h : P.length j ≤ H
    · simpa only [ite_eq_left h] using P.measurable_source j
    · simp only [ite_eq_right h]
      exact measurable_const
  source_nonneg := fun j x => by split_ifs; exact P.source_nonneg j x; exact le_rfl
  source_bound := fun j x => by split_ifs; exact P.source_bound j x; exact P.sourceBound_nonneg
  source_sum := fun x => (Finset.sum_le_sum (fun j _ => by
    split_ifs; exact le_rfl; exact P.source_nonneg j x)).trans (P.source_sum x)

end LipschitzHilbert.LineErrorSources

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceErrorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial thresholds for the actual positive convolution error.
Only the source bound and its logarithmic scale sum enter the constants. -/

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace LipschitzHilbert.LineErrorSources

variable {N : ℕ}

def momentBase (P : LineErrorSources N) (grid : FiniteLineGrid) : ℝ :=
  16*((((grid.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/
    Real.log (3/2)+P.meanConstant+1)

end LipschitzHilbert.LineErrorSources

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodQuantities
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability of the actual reference quantities is needed
before weighted bad-path sets are integrated over the physical plane. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalMainSquareOnPlane (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  P.physicalMainSquare t a b v g (z.2-t*z.1) z.1

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

def physicalReferenceEvent (i : Fin 3) : Set (ℝ×ℝ) :=
  if i = 0 then {z | L^e ≤ P.physicalAngularError t a b v g z}
  else if i = 1 then {z | L^s ≤ P.physicalMainSquareOnPlane t a b v g z}
  else {z | L^r ≤ P.physicalMaskedVariation alt hAlt t b v g T L A (z.2-t*z.1) z.1}

def physicalReferenceBad : Set (ℝ×ℝ) :=
  ⋃ i : Fin 3, P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalGoodPath
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted good-path construction for actual physical reference
packets. A reference bundle only packages the original formulas; it has
no probabilistic or path estimate as a field. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert

structure PhysicalReferenceData (N : ℕ) (κ : Type) (Label : Fin N → Type)
    (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)] where
  family : SourceLabeledLattice N κ Label Item
  alternate : ∀ j (l : family.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ
  alternate_bound : ∀ j l u k,
    planarProfileConstant (alternate j l u k) (2*family.order) ≤ family.profileBound
  slope : ℝ
  angle : ℝ
  selector : ∀ j, family.labels j → κ → ℝ → ℂ
  direction : ℝ×ℝ → ℝ
  test : ℝ×ℝ → EuclideanSpace ℂ κ
  packetTop : ∀ j (l : family.labels j), Item j l → SlopeBox

namespace PhysicalReferenceData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

def bad (L A e s r : ℝ) : Set (ℝ×ℝ) :=
  P.family.physicalReferenceBad P.alternate P.alternate_bound P.slope P.angle P.selector
    P.direction P.test P.packetTop L A e s r

end PhysicalReferenceData

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedReferenceData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected reference family retains the original physical packets,
coefficients and top masks. Its spatial item type depends on the selected
finite subset, while its good event directly controls the original
selected stopping prefixes and all unary runs. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert
namespace PhysicalReferenceData

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

def restrictPackets (Q : Finset P.family.PacketIndex) :
    PhysicalReferenceData N κ Label (P.family.RestrictedPacketItem Q) where
  family := P.family.restrictPackets Q
  alternate := P.family.restrictedAlternate P.alternate Q
  alternate_bound := P.family.restrictedAlternate_bound P.alternate P.alternate_bound Q
  slope := P.slope
  angle := P.angle
  selector := P.selector
  direction := P.direction
  test := P.test
  packetTop := fun j l u => P.packetTop j l u.val

end PhysicalReferenceData

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentReference
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual data at a selected reference uses only its local cone. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (packetTop : ∀ j (l : P.labels j), Item j l → SlopeBox)

/-- Literal recentering of original physical reference data. -/
abbrev recenteredReferenceData : PhysicalReferenceData N κ Label Item where
  family := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
  alternate := fun j l => alt j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)
  alternate_bound := fun j l => hAlt j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)
  slope := newSlope
  angle := w/P.topLength
  selector := fun j l => b j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)
  direction := v
  test := f
  packetTop := fun j l => packetTop j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)

/-- Original packet indices are selected through the exact reference-label map. -/
def recenteredReferenceSelection (S : Finset P.PacketIndex) :
    Finset (P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency).PacketIndex :=
  Finset.univ.filter (fun u =>
    (⟨u.1,⟨P.referenceOriginalLabel oldSlope newSlope R cone w u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)

@[simp] theorem recenteredReferenceData_slope :
    (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).slope = newSlope := rfl

@[simp] theorem recenteredReferenceData_angle :
    (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).angle = w/P.topLength := rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nested line grid with the rounded manuscript step. A single
refinement has mesh H/G, small enough to retain the G^(-1/16) error when
the carrier spread times H is at most G^(15/16). -/

noncomputable section
namespace LipschitzHilbert

def sourceLineGrid (L origin width : ℝ) (depth : ℕ) (hwidth : 0 < width) : FiniteLineGrid where
  branching := 2^SourceParameters.stepExponent L
  branching_pos := pow_pos (by norm_num) _
  origin := origin
  width := width
  width_pos := hwidth
  depth := depth

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source line scales for a whole angular block. Refinement from the
child scale to the parent scale cancels the angular branching exactly. -/

noncomputable section
namespace LipschitzHilbert

/-- The manuscript line-window length at one angular generation. -/
def sourceLineScale (g : AngularGrid) (L w : ℝ) (level : ℕ) : ℝ :=
  w / (g.width level * SourceParameters.step L ^ (1/2 : ℝ))

theorem sourceLineScale_pos (g : AngularGrid) (L : ℝ) {w : ℝ}
    (hw : 0 < w) (level : ℕ) : 0 < sourceLineScale g L w level := by
  unfold sourceLineScale
  exact div_pos hw (mul_pos (g.width_pos level)
    (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseBlocks
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source line windows grow along the angular path. Reading those
windows in reverse gives increasing levels in one finite line grid. Only
the factors are reordered: the stopping budget retains its forward mass
path, including the possibility of a zero terminal mass. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

def reverseLevel (σ : Fin K) (count k : ℕ) : ℕ :=
  endpoint σ count - endpoint σ (count-k)

def reverseIndex (count j : ℕ) : ℕ := count-1-j

@[simp] theorem reverseLevel_zero (σ : Fin K) (count : ℕ) :
    reverseLevel σ count 0 = 0 := by
  simp [reverseLevel]

@[simp] theorem reverseLevel_last (σ : Fin K) (count : ℕ) :
    reverseLevel σ count count = endpoint σ count := by
  simp [reverseLevel]

end LipschitzHilbert.ShiftedBlocks

namespace LipschitzHilbert

/-- A single root line grid contains every source block window, in reverse
angular order. Its depth includes the shorter initial source block exactly. -/
def sourceReverseLineGrid {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (count : ℕ) : FiniteLineGrid :=
  sourceLineGrid L origin (sourceLineScale g L w (ShiftedBlocks.endpoint σ count))
    (ShiftedBlocks.endpoint σ count)
    (sourceLineScale_pos g L hw (ShiftedBlocks.endpoint σ count))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier spread and Fourier separation at the actual source block windows. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace AngularGrid

/-- The neighbor radius at the final transition, in child-width units. -/
def sourceGap (g : AngularGrid) (L : ℝ) (child : ℕ) : ℝ :=
  SourceParameters.step L^(3/4:ℝ)*g.width child

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTerminalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least ineligible shifted endpoint provides a finite terminal
generation without enlarging the source root line window past its top.
This includes exactly one final block after the last eligible endpoint. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def firstIneligibleShiftedBlock {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) : ℕ :=
  Nat.find (g.exists_shifted_terminal cutoff precision hp hK σ)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedTopFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def AssignedTopItem (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (j : Fin N) (l : τ×P.labels j) :=
  {u : Item j l.2 // (⟨j,⟨l.2,u⟩⟩ : P.PacketIndex) ∈ packets ∧
    assigned ⟨j,⟨l.2,u⟩⟩ = l.1}

instance assignedTopItemFintype (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (j : Fin N) (l : τ×P.labels j) : Fintype (P.AssignedTopItem packets assigned j l) := by
  unfold AssignedTopItem
  infer_instance

def assignedTopFamily (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ) :
    SourceLabeledLattice N κ (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := fun j => {top} ×ˢ (Finset.univ : Finset (P.labels j))
  originX := fun j l => P.originX j l.val.2
  originZ := fun j l => P.originZ j l.val.2
  rowSlope := fun j l => P.rowSlope j l.val.2
  frequency := P.frequency
  site := fun j l u => P.site j l.val.2 u.val
  site_injective := fun j l => (P.site_injective j l.val.2).comp Subtype.val_injective
  profile := fun j l u k => P.profile j l.val.2 u.val k
  profile_bound := fun j l u k => P.profile_bound j l.val.2 u.val k
  shear_bound := fun j l => P.shear_bound j l.val.2
  carrier_bound := fun j l k => P.carrier_bound j l.val.2 k

@[simp] theorem assignedTopFamily_length (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).length j = P.length j := rfl

@[simp] theorem assignedTopFamily_constant (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) :
    (P.assignedTopFamily packets assigned top).constant = P.constant := rfl

@[simp] theorem assignedTopFamily_label_count (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (j : Fin N) :
    ((P.assignedTopFamily packets assigned top).labels j).card = (P.labels j).card := by
  simp [assignedTopFamily]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketRegroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of original packet amplitudes by assigned top and
length. This connects the individual-packet residual estimates to the
same top-band amplitudes appearing in the physical path integrals. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable Classical.decEq

namespace AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The scalar factor at one node is constant on every top/length fiber. -/
def sourceGroupedCoefficient {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (stop : ι → Fin N → ℕ) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ) (cell : ℤ) (p : ι×Fin N) : ℂ :=
  if g.index level (slope p.1) = cell ∧ level ≤ stop p.1 p.2 then
    g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      level (stop p.1 p.2) (slope p.1)*
      ((g.mass tops slope precision cutoff weight (stop p.1 p.2)
        (g.index (stop p.1 p.2) (slope p.1)) x^(-a):ℝ):ℂ)
  else 0

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual angular annulus bins

The positive and negative dyadic annuli about a reference slope are each
partitioned into `M` equal half-open bins, as in §6 of the manuscript.
Enlargement is concentric. No choice of a significant list enters these
definitions.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.AngularBins

abbrev Bin (M : ℕ) := Bool × ℤ × Fin M

def radialCoordinate (s : ℝ) (positive : Bool) (a : ℝ) : ℝ :=
  if positive then a - s else s - a

def width (M : ℕ) (h : ℤ) : ℝ := DyadicLineGrid.scale h / M

def radialStart (M : ℕ) (h : ℤ) (j : Fin M) : ℝ :=
  DyadicLineGrid.scale h + (j : ℝ) * width M h

def radialMidpoint (M : ℕ) (h : ℤ) (j : Fin M) : ℝ :=
  radialStart M h j + width M h / 2

def baseBin (s : ℝ) {M : ℕ} (b : Bin M) : Set ℝ :=
  {a | radialStart M b.2.1 b.2.2 ≤ radialCoordinate s b.1 a ∧
    radialCoordinate s b.1 a < radialStart M b.2.1 b.2.2 + width M b.2.1}

def enlargedBin (s c : ℝ) {M : ℕ} (b : Bin M) : Set ℝ :=
  {a | |radialCoordinate s b.1 a - radialMidpoint M b.2.1 b.2.2| ≤
    c * width M b.2.1 / 2}

end LipschitzHilbert.AngularBins

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBinOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed overlap of the enlarged angular annulus bins from §6. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.AngularBins

attribute [local instance] Classical.propDecidable

def binFunction {X : Type*} (s c : ℝ) {M : ℕ} (u : X → ℝ) (b : Bin M) : X → ℝ :=
  fun x => (enlargedBin s c b).indicator (1 : ℝ → ℝ) (u x)

end LipschitzHilbert.AngularBins

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the original source node ratios and the finite active
path product. These are the integrands used for line-to-plane gluing,
independently of any selected snapshot predictors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {X : Type*} {ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]

/-- Inactive indices have factor one, exactly as in the source path
expansion. The threshold is tested against the original forward masses. -/
def sourceActiveProduct (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ) (x : X) : ℝ :=
  ∏ j ∈ Finset.range count, if M < n x j then beta x j else 1

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite hierarchy path integrand, expressed only through
packet amplitudes, top weights and the stopping threshold. Its spatial
measurability does not involve the auxiliary snapshot choices. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

def sourceBlockNodeRatio (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) : ℝ :=
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  sourceNodeRatio (g.mass tops slope precision cutoff weight lower parent x)
    (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
    (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x upper i.val) α p
    (g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x lower parent)

def sourceShiftedPathRatio {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) : ℝ :=
  g.sourceBlockNodeRatio tops slope precision cutoff weight K gap packets assigned stop value
    phase a α p (ShiftedBlocks.endpoint tag j) (ShiftedBlocks.endpoint tag (j+1))
    (g.index (ShiftedBlocks.endpoint tag j) (slope top)) x

def sourceActivePathValue {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) : X → ℝ :=
  sourceActiveProduct (g.shiftedPathMass tops slope precision cutoff weight tag top)
    (g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p tag top) M count

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePathPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-free predictor on the actual packet path. Its child
family and coefficients are the same ones used by the physical estimate. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

def sourceBlockPrediction (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) : ℝ :=
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  sourcePredictionValue p μ (g.mass tops slope precision cutoff weight lower parent x)
    (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
    (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x upper i.val)
    (fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper
      (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)))

def sourceShiftedPathPrediction {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) : ℝ :=
  g.sourceBlockPrediction tops slope precision cutoff weight K gap packets assigned stop value
    phase a p μ (ShiftedBlocks.endpoint tag j) (ShiftedBlocks.endpoint tag (j+1))
    (g.index (ShiftedBlocks.endpoint tag j) (slope top)) x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The amplitude on a distinguished top path stops when that top becomes
ineligible. Other surviving children remain in the original denominator. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

namespace AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

def sourceShiftedPathAmplitude {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) :
    EuclideanSpace ℂ κ :=
  if g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j) then
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) phase a x (ShiftedBlocks.endpoint tag j)
      (g.index (ShiftedBlocks.endpoint tag j) (slope top)) else 0

def sourceShiftedPathDenominator {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) : ℝ :=
  let lower := ShiftedBlocks.endpoint tag j
  let upper := ShiftedBlocks.endpoint tag (j+1)
  let parent := g.index lower (slope top)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  sourceNodeDenominator (g.mass tops slope precision cutoff weight lower parent x)
    (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
    (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked predictors are patched cellwise, then integrated in reverse
geometric order. Their logarithmic errors are summed in the original
forward angular order and paid by the actual first mass crossing. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def reverseMarkedValue (g : FiniteLineGrid) (level : ℕ → ℕ) (count : ℕ)
    (marked : ℕ → ℕ → Prop) (value : ℕ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  g.markedValue (level (ShiftedBlocks.reverseIndex count j)) (marked j) (value j)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's boundary radius is G^(-1/4) times the parent width.
At a last transition this is exactly G^(3/4) times the child width. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

def sourceBoundaryGap (g : AngularGrid) (L : ℝ) (level : ℕ) : ℝ :=
  SourceParameters.step L^(-(1/4:ℝ))*g.width level

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualEnvelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed reference packet collection from §§8 and 10 contains
every short residual packet. Positive per-length reference envelopes
therefore dominate the actual block envelopes by subset summation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

def sourceReferencePackets {σ : Type*} (packets : Finset σ)
    (length angle : σ → ℝ) (referenceLength referenceSlope cone w : ℝ) : Finset σ :=
  packets.filter (fun q => length q ≤ referenceLength ∧
    |angle q-referenceSlope| ≤ cone*(w/length q))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotWindow
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The predictor uses displacement from a chosen good snapshot. Translate
its exact probability law and line-grid indices back to physical coordinates. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

namespace FiniteLineGrid

def atSnapshot (g : FiniteLineGrid) (x₀ : ℝ) : FiniteLineGrid :=
  {g with origin := g.origin-x₀}

end FiniteLineGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedCellMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute path drops are sums over the actual lost tops. This gives
the cellwise relative motion needed by the source's infimum/supremum
marking rule, including a terminal block with no continuing path child. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def shiftedPathLossTops {ι : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (σ : Fin K) (top : ι) (j : ℕ) : Finset ι :=
  let parent := g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
    (g.index (ShiftedBlocks.endpoint σ j) (slope top))
  if g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1)) then
    parent \ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top))
  else parent

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceInhabitedLabels
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing labels with no items preserves every packet and every
source band. Only genuinely populated assigned fibers enter label counts. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def inhabitedLabels (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => Nonempty (Item j l))

def inhabitedOriginalLabel (j : Fin N) (l : P.inhabitedLabels j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

def inhabitedFamily : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.inhabitedLabels
  originX := fun j l => P.originX j (P.inhabitedOriginalLabel j l)
  originZ := fun j l => P.originZ j (P.inhabitedOriginalLabel j l)
  rowSlope := fun j l => P.rowSlope j (P.inhabitedOriginalLabel j l)
  frequency := P.frequency
  site := fun j l => P.site j (P.inhabitedOriginalLabel j l)
  site_injective := fun j l => P.site_injective j (P.inhabitedOriginalLabel j l)
  profile := fun j l => P.profile j (P.inhabitedOriginalLabel j l)
  profile_bound := fun j l => P.profile_bound j (P.inhabitedOriginalLabel j l)
  shear_bound := fun j l => P.shear_bound j (P.inhabitedOriginalLabel j l)
  carrier_bound := fun j l => P.carrier_bound j (P.inhabitedOriginalLabel j l)

@[simp] theorem inhabitedFamily_length (j : Fin N) : P.inhabitedFamily.length j = P.length j := rfl
@[simp] theorem inhabitedFamily_actualX (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) :
    P.inhabitedFamily.actualX j l u = P.actualX j (P.inhabitedOriginalLabel j l) u := rfl
@[simp] theorem inhabitedFamily_actualZ (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) :
    P.inhabitedFamily.actualZ j l u = P.actualZ j (P.inhabitedOriginalLabel j l) u := rfl
@[simp] theorem inhabitedFamily_rowSlope (j : Fin N) (l : P.inhabitedLabels j) :
    P.inhabitedFamily.rowSlope j l = P.rowSlope j (P.inhabitedOriginalLabel j l) := rfl
@[simp] theorem inhabitedFamily_constant : P.inhabitedFamily.constant = P.constant := rfl
@[simp] theorem inhabitedFamily_absoluteConstant : P.inhabitedFamily.absoluteConstant = P.absoluteConstant := rfl
@[simp] theorem inhabitedFamily_label_card (j : Fin N) :
    (P.inhabitedFamily.labels j).card = ((P.labels j).filter (fun l => Nonempty (Item j l))).card := rfl

@[simp] theorem inhabitedFamily_raw (jet : Fin 3) (j : Fin N)
    (l : P.inhabitedLabels j) (u : Item j l) (k : κ) (y : ℝ) :
    P.inhabitedFamily.raw jet j l u k y = P.raw jet j (P.inhabitedOriginalLabel j l) u k y := rfl

@[simp] theorem inhabitedFamily_physicalPacket (t : ℝ) (j : Fin N)
    (l : P.inhabitedLabels j) (u : Item j l) (k : κ) :
    P.inhabitedFamily.physicalPacket t j l u k =
      P.physicalPacket t j (P.inhabitedOriginalLabel j l) u k := rfl

def inhabitedAlternate (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  alt j (P.inhabitedOriginalLabel j l) u k

theorem inhabitedAlternate_bound
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : P.inhabitedLabels j) (u : Item j l) (k : κ) :
    planarProfileConstant (P.inhabitedAlternate alt j l u k) (2*P.inhabitedFamily.order) ≤
      P.inhabitedFamily.profileBound := hAlt j (P.inhabitedOriginalLabel j l) u k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSharedGoodPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original per-top plane bounds descend to one common good set and
one terminal count. The latter is the supremum of the actual first
ineligible shifted endpoints, without an additional stopping premise. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

namespace AngularGrid
variable {τ σ : Type*} {κ : Type} [Fintype κ]

def sourceTopTerminalCount {Kb : ℕ} (g : AngularGrid) (T : τ → SlopeBox)
    (cutoff w : ℝ) (hw : 0 < w) (hKb : 0 < Kb) (shift : Fin Kb) (top : τ) : ℕ :=
  g.firstIneligibleShiftedBlock cutoff (w/(T top).length)
    (div_pos hw (T top).length_pos) hKb shift

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite conservation for the actual angular partitions. Stopping
at a small-mass cell retains its normalized vertex amount; ineligible tops
retain their original weight. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

section Tree
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
  (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ → ℕ)
  (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p : ℝ) (x : X)

def sourceTreeAmount (j : ℕ) (cell : ℤ) : ℝ :=
  vertexAmount (g.mass tops slope precision cutoff weight (level j) cell x) (A j cell) α p

def sourceTreeDenominator (j : ℕ) (cell : ℤ) : ℝ :=
  sourceNodeDenominator (g.mass tops slope precision cutoff weight (level j) cell x)
    (fun c : g.sourceBlockCells tops slope precision cutoff (level j) (level (j+1)) cell =>
      g.mass tops slope precision cutoff weight (level (j+1)) c.val x)
    (fun c => A (j+1) c.val) α p

def sourceTreeExit (j : ℕ) (top : τ) : ℝ :=
  if g.eligible cutoff (precision top) (level j) then
    g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top))/
      g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x
  else 1

def sourceTreeTail (M : ℝ) : ℕ → ℕ → τ → ℝ
  | 0,j,t => g.sourceTreeExit tops slope precision cutoff weight level A α p x j t
  | n+1,j,t =>
    if g.eligible cutoff (precision t) (level j) ∧
        M < g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope t)) x then
      (g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
        (g.index (level j) (slope t))/
       g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
        (g.index (level j) (slope t)))*
      sourceTreeTail M n (j+1) t
    else g.sourceTreeExit tops slope precision cutoff weight level A α p x j t

end Tree
end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite angular-tree conservation law is exactly the stopped
product used in the analytic path estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

section Path
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
  (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ → ℕ)
  (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p : ℝ) (x : X)

def sourceTreePathMass (top : τ) (j : ℕ) : ℝ :=
  if g.eligible cutoff (precision top) (level j) then
    g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x
  else 0

def sourceTreePathRatio (top : τ) (j : ℕ) : ℝ :=
  g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top))/
    g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top))

end Path
end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source packet path is a single exponential of the sum of
its logarithmic transition ratios. This exact formula is used to integrate
an affine phase slice on sets where those finitely many logs are bounded. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def pathLogCombination (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (slope : ℝ) : ℂ :=
  ∑ j ∈ Finset.Ico lower upper,
    phase j*(Real.log (mass (j+1) (g.index (j+1) slope)/
      boundary j (g.index (j+1) slope)):ℂ)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated affine slices of the original source packet amplitude
are entire on bounded logarithmic-coefficient exhaustions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

def sourcePathLog (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (phase : ℕ → ℂ) (lower upper : ℕ) (s : ℝ) (x : X) : ℂ :=
  g.pathLogCombination (fun j c => g.mass tops slope precision cutoff weight j c x)
    (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
    phase lower upper s

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAmplitudeExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single exhaustion, independent of the complex phase, bounds all
original packet bases and the absolute logarithms along their paths. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

def pathLogSize (g : AngularGrid) (mass boundary : ℕ → ℤ → ℝ)
    (lower upper : ℕ) (slope : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico lower upper,
    |Real.log (mass (j+1) (g.index (j+1) slope)/boundary j (g.index (j+1) slope))|

def sourceAmplitudeRadius (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ) (x : X) : ℝ :=
  ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
    (‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ +
      g.pathLogSize (fun j c => g.mass tops slope precision cutoff weight j c x)
        (fun j c => g.sourceBoundaryMass tops slope precision cutoff weight K gap j c x)
        level (stop s) (slope (assigned s)))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAmplitudeInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original source family satisfies the analytic simplex estimate.
Only its vertex moments remain as input; measurability, analytic slices,
bounded exhaustion, and the full-set limiting argument are proved here. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ ι : Type*} [MeasurableSpace X] [Fintype κ] [Fintype ι]

def sourceShiftFamily (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phaseIndex : ℕ → ι)
    (a : ℝ) (level : ℕ) (cell : ℤ) (z : ι → ℂ) (x : X) : EuclideanSpace ℂ κ :=
  g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
    (value x) (fun j => z (phaseIndex j)) a x level cell

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRootCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty eligible root cells of the actual translated grid.
They split the central packet sum exactly. A slope interval no wider
than one root contains at most two roots, including its endpoints. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def sourceRootCells (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) : Finset ℤ :=
  (tops.filter (fun t => g.eligible cutoff (precision t) 0)).image
    (fun t => g.index 0 (slope t))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataActualReferenceEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent-square and continuing-path reference events of the
source packet family. The union is independent of every complex phase. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (L oldSlope C w F : ℝ) (hw : 0 < w) (hC : 0 ≤ C) (hF : 0 ≤ F)
  (hwide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (hKb : 0 < SourceParameters.blockCount L)

def actualReferenceData (top : τ) (i : Option (Fin (SourceParameters.blockCount L))) :
    PhysicalReferenceData N κ Label Item :=
  P.recenteredReferenceData alt hAlt oldSlope (T top).slope (T top).length
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2)) w F hw
    (add_nonneg hC (pow_nonneg (SourceParameters.branching_pos L).le _)) hF
    (hwide i) hfrequency b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩))

def actualReferencePacketSet (top : τ) :
    Option (Fin (SourceParameters.blockCount L)) → Finset P.PacketIndex
  | none => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (T top).length (T top).slope
      (C+(SourceParameters.branching L)^3) w
  | some shift =>
      let cut := g.rootWidth/(SourceParameters.branching L)^2
      let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
      g.fixedPathResidualPackets tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut packets assigned (fun u => stop u.1) (ShiftedBlocks.endpoint shift)
        (g.sourceTopTerminalCount T cut w hw hKb shift top-1) (T top).slope

def actualReferenceSelection (top : τ) (i : Option (Fin (SourceParameters.blockCount L))) :
    Finset (P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).family.PacketIndex :=
  P.recenteredReferenceSelection oldSlope (T top).slope (T top).length
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2)) w F hw
    (add_nonneg hC (pow_nonneg (SourceParameters.branching_pos L).le _)) hF
    (hwide i) hfrequency
    (P.actualReferencePacketSet L oldSlope C w hw g tops T packets assigned hKb top i)

def actualReferenceBad (maskExponent q : ℝ) (top : τ) : Set (ℝ×ℝ) :=
  ⋃ i : Option (Fin (SourceParameters.blockCount L)),
    ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).restrictPackets
      (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb top i)).bad
          L maskExponent (q+8) (2*q+9) (2*q+11)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite adjoint duality for the ordinary masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def ordinaryForwardSum (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q∈S, WithLp.toLp 2 (fun k => P.ordinaryCoefficient f q.1 q.2.1 q.2.2 k*
    b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)

def ordinaryAdjointSum (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q∈S, P.packetVector (P.physicalMultiplierCoefficient 0 b u g) q z

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinct-profile, masked analyzing packet sum. No auxiliary
jet is needed for the physical bilinear operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

def crossPacketValue (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation-independent radial masses and the literal distance to the
nearest angular boundary. Eligibility is retained in every radial set. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

def boundaryDistance (g : AngularGrid) (level : ℕ) (s : ℝ) : ℝ :=
  min (s-g.left level (g.index level s))
    (g.left level (g.index level s)+g.width level-s)

def nearbyEligibleTops (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (level : ℕ) (radius s : ℝ) : Finset τ :=
  tops.filter fun t => g.eligible cutoff (precision t) level ∧ |slope t-s| < radius

def nearbyEligibleMass (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ) (radius s : ℝ) (x : X) : ℝ :=
  ∑ t ∈ g.nearbyEligibleTops tops slope precision cutoff level radius s, weight t x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularCommonTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One uniform translation modulo the root width induces the correct
boundary-distance average at every level of the nested angular grid. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.AngularGrid

def withOrigin (g : AngularGrid) (origin : ℝ) : AngularGrid := {g with origin := origin}

@[simp] theorem width_withOrigin (g : AngularGrid) (origin : ℝ) (i : ℕ) :
    (g.withOrigin origin).width i = g.width i := rfl

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularTranslationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual path and boundary masses as the common
angular-grid origin varies. The top weights are held fixed here. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

@[fun_prop] theorem measurable_index_withOrigin (g : AngularGrid) (i : ℕ) (s : ℝ) :
    Measurable (fun origin => (g.withOrigin origin).index i s) := by
  unfold index withOrigin
  fun_prop

@[fun_prop] theorem measurable_center_withOrigin (g : AngularGrid) (i : ℕ) (s : ℝ) :
    Measurable (fun origin => (g.withOrigin origin).center i ((g.withOrigin origin).index i s)) := by
  change Measurable (fun origin => origin+g.width i*((g.withOrigin origin).index i s)+g.width i/2)
  fun_prop

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact central coefficient loses at most the sum of the logarithmic
parent-to-boundary losses. Its deficit grows with the packet stopping level. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

def sourceBoundaryLogLoss (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (N : ℕ) (top : τ) (x : X) : ℝ :=
  ∑ j ∈ Finset.range N, Real.log
    (g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope top)) x /
      g.mass tops slope precision cutoff weight j (g.index j (slope top)) x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialMassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive self mass and the fixed total mass bound every radial eligible
mass along a top's eligible path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

def radialPathLogMass (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (epsilon : ℝ) (N : ℕ) (top : τ) (x : X) (i : ℕ) : ℝ :=
  if i < N then Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      weight top x) else 0

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A radial one-level loss is cut off to the near-boundary region.
It is measurable and uniformly bounded by the fixed total/self log ratio. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

def radialBoundaryLoss (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (epsilon : ℝ) (i : ℕ) (top : τ) (x : X) : ℝ → ℝ :=
  (Ioo 0 epsilon).indicator (fun b => Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedMaskSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact regrouping of the unmasked original packets and of their
assigned top masks. The analyzing coefficient and alternate synthesis
profile are retained in both sums. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

@[simp] theorem SlopeBox.mask_zero (T : SlopeBox) (A : ℝ) (z : ℝ×ℝ) :
    T.mask 0 A z = 1 := by
  simp [SlopeBox.mask,topSincMask,sincProductMask]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal physical top masks for unrestricted packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
variable (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

def physicalMaskedValue (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2 k*
    ((T q.1 q.2.1 q.2.2).mask L A z:ℂ)*
    (P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k z)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPhysical
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact assignment and length regrouping of the physical packet sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)

def assignedPhysicalBands (z : ℝ×ℝ) (p : τ×Fin N) : EuclideanSpace ℂ κ :=
  ∑ q∈packets.filter (fun q => (assigned q,q.1)=p),
    P.physicalMaskedValue alt hAlt t b v f T L A z q

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

def AssignedTopItem (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (j : Fin N) (l : τ×P.labels j) :=
  {u : Item j l.2 // (⟨j,⟨l.2,u⟩⟩ : P.PacketIndex) ∈ packets ∧
    assigned ⟨j,⟨l.2,u⟩⟩ = l.1}

instance assignedTopItemFintype (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (j : Fin N) (l : τ×P.labels j) : Fintype (P.AssignedTopItem packets assigned j l) := by
  unfold AssignedTopItem
  infer_instance

def assignedTopFamily (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ) :
    PacketLatticeData N κ (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned) where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  labels := fun j => {top} ×ˢ (Finset.univ : Finset (P.labels j))
  originX := fun j l => P.originX j l.val.2
  originZ := fun j l => P.originZ j l.val.2
  rowSlope := fun j l => P.rowSlope j l.val.2
  frequency := P.frequency
  site := fun j l u => P.site j l.val.2 u.val
  site_injective := fun j l => (P.site_injective j l.val.2).comp Subtype.val_injective
  profile := fun j l u k => P.profile j l.val.2 u.val k
  profile_bound := fun j l u k => P.profile_bound j l.val.2 u.val k

@[simp] theorem assignedTopFamily_length (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).length j = P.length j := rfl

@[simp] theorem assignedTopFamily_label_count (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ) (top : τ) (j : Fin N) :
    ((P.assignedTopFamily packets assigned top).labels j).card = (P.labels j).card := by
  simp [assignedTopFamily]

/-- No packet is copied to a second top, and no empty fiber adds a packet. -/
def assignedTopPacketEquiv (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (top : τ) : (P.assignedTopFamily packets assigned top).PacketIndex ≃
      packets.filter (fun q => assigned q = top) where
  toFun := fun q => ⟨⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩,by
    apply Finset.mem_filter.mpr
    refine ⟨q.2.2.property.1,?_⟩
    have ht : q.2.1.val.1 = top :=
      Finset.mem_singleton.mp (Finset.mem_product.mp q.2.1.property).1
    exact q.2.2.property.2.trans ht⟩
  invFun := fun q => ⟨q.val.1,⟨⟨(top,q.val.2.1),by
    simp only [assignedTopFamily,Finset.mem_product,Finset.mem_singleton,
      Finset.mem_univ,and_self]⟩,
    ⟨q.val.2.2,(Finset.mem_filter.mp q.property).1,(Finset.mem_filter.mp q.property).2⟩⟩⟩
  left_inv := by
    rintro ⟨j,⟨⟨⟨s,l⟩,hl⟩,⟨u,hu⟩⟩⟩
    have hs : s = top := Finset.mem_singleton.mp (Finset.mem_product.mp hl).1
    subst s
    rfl
  right_inv := by
    intro q
    rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopAlternate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-type assigned top families have exactly the original
physical bands, including original selector coefficients and top masks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

def assignedTopAlternate (top : τ) (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  alt j l.val.2 u.val k

include hAlt in
theorem assignedTopAlternate_bound (top : τ) (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    planarProfileConstant (P.assignedTopAlternate packets assigned alt top j l u k)
      (2*(P.assignedTopFamily packets assigned top).order) ≤
        (P.assignedTopFamily packets assigned top).profileBound := hAlt j l.val.2 u.val k

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

def assignedTopLabel (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : P.labels j := l.val.2

def assignedTopSelector (b : ∀ j, P.labels j → κ → ℝ → ℂ) :
    ∀ j, (P.assignedTopFamily packets assigned top).labels j → κ → ℝ → ℂ :=
  fun j l => b j l.val.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedReference
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each assigned top receives its exact local bounded reference family. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

/-- The selected reference family has derived shear and carrier bounds. -/
def assignedReferenceFamily (top : τ) :
    SourceLabeledLattice N κ (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned) :=
  (P.assignedTopFamily packets assigned top).referenceFamily oldSlope (T top).slope
    (R top) cone w F hw hcone hF hwide hfrequency

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

def assignedReferenceOriginalLabel (top : τ) (j : Fin N) (l : (Q top).labels j) : P.labels j :=
  ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
    oldSlope (T top).slope (R top) cone w j l).val.2

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

def assignedReferenceAlternate (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  alt j (orig top j l) u.val k

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

include hAlt in
theorem assignedReferenceAlternate_bound (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    planarProfileConstant (alts top j l u k) (2*(Q top).order) ≤ (Q top).profileBound :=
  hAlt j (orig top j l) u.val k

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

def assignedReferenceSelector (top : τ) (j : Fin N) (l : (Q top).labels j) : κ → ℝ → ℂ :=
  b j (orig top j l)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataOriginalParentMarkedPath
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source cell marks and local original-packet estimates
supply the remaining hypotheses of the stopped-path theorem. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

def originalParentMarkedPathBoundAt (q D Cmass qoff A_M L : ℝ) (Klocal Hlocal : ℕ) : Prop :=
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ Klocal) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) Hlocal) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type) (grid : AngularGrid) (tops : Finset τ)
      (T : τ → SlopeBox) (A s w R C F : ℝ) (hw : 0 < w) (hR : 0 < R),
    let slope : τ → ℝ := fun top => (T top).slope;
    let precision : τ → ℝ := fun top => w/(T top).length;
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    ∀ (top : τ), top ∈ tops → R = (T top).length →
    ∀ (hcone : 0 ≤ C+(SourceParameters.branching L)^2) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (hparentCone : 0 ≤ C+(SourceParameters.branching L)^3)
      (hparentWide : (C+(SourceParameters.branching L)^3)*w ≤ P.width),
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hK shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (Z Nmass α μ : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 →
      (∀ k, ‖phase k‖ ≤ Z) → 0 < Nmass → Real.log Nmass ≤ 2*L →
      1 ≤ α → α ≤ 3 → (α-1)/Real.sqrt L ≤ 1/12 → Real.sqrt L*μ = α-1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let squarePackets := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R (slope top) (C+(SourceParameters.branching L)^3) w
    let Qsquare := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^3) w F
      hw hparentCone hF hparentWide hfrequency
    let origSquare := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^3) w
    let squareSelected := (Finset.univ : Finset Qsquare.PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets)
    let S := grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Q := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^2) w F
      hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Qsquare.restrictPackets squareSelected).physicalReferenceBad
      (Qsquare.restrictedAlternate (fun j l => alt j (origSquare j l)) squareSelected)
      (Qsquare.restrictedAlternate_bound (fun j l => alt j (origSquare j l))
        (fun j l => hAlt j (origSquare j l)) squareSelected)
      (slope top) (w/P.topLength) (fun j l => b j (origSquare j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      (slope top) (w/P.topLength) (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) (2*q+11) →
    let n := grid.shiftedPathMass tops slope precision cut weight shift top z
    let _finish := firstMassStop n count (L^A_M)
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let level := ShiftedBlocks.endpoint shift
    let transition := grid.sourceTransition tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) phase z
    let base := grid.sourcePacketBase tops slope precision cut weight assigned
      (fun u => stop u.1) (value z) a z
    let _W := fun j => grid.packetAmplitude
      (packets.filter fun u => assigned u ∉ grid.cellTops tops slope precision cut
        (level (j+1)) (grid.index (level (j+1)) (slope top)))
      (fun u => slope (assigned u)) (fun u => stop u.1) base transition
      (level j) (grid.index (level j) (slope top))
    let _amp := grid.sourceShiftedPathAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) value phase a shift top z
    ∀ (origin y x : ℝ), z = (x,y+slope top*x) →
    let line := sourceReverseLineGrid grid L origin hw shift count
    let mass := fun xx => grid.shiftedPathMass tops slope precision cut weight
      shift top (xx,y+slope top*xx)
    let marked := fun j i => sourceMarkedCell
      (line.cell (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) i)
      (fun xx => mass xx j) (fun xx => mass xx j-mass xx (j+1)) (L^A_M)
    x ∈ line.root → 1 ≤ L^(A+2) →
    (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (Cex : ℝ), 0 ≤ Cex → Real.log (n 0) ≤ 3*L →
      grid.mass tops slope precision cut weight 0 (grid.index 0 (slope top)) z ≤ L^Cmass*Nmass →
      (∀ level cell, ‖grid.sourcePacketAmplitude tops slope precision cut weight
        (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
        (fun u => stop u.1) (value z) phase a z level cell‖ ≤
          Cex*grid.mass tops slope precision cut weight level cell z) →
      (∀ lower upper, lower ≤ upper → ∀ sr,
        grid.mass tops slope precision cut weight lower (grid.index lower sr) z-
          grid.mass tops slope precision cut weight upper (grid.index upper sr) z < 1 →
        ‖grid.sourcePacketAmplitude tops slope precision cut weight
          (SourceParameters.blockCount L) (grid.sourceBoundaryGap L)
          (packets.filter (fun u => assigned u ∉ grid.cellTops tops slope precision cut
            upper (grid.index upper sr))) assigned (fun u => stop u.1) (value z)
          phase a z lower (grid.index lower sr)‖ ≤
          (L^qoff*Real.exp (-L*Real.log L))*(
            grid.mass tops slope precision cut weight lower (grid.index lower sr) z-
            grid.mass tops slope precision cut weight upper (grid.index upper sr) z)) →
    grid.sourceActivePathValue tops slope precision cut weight (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) packets assigned (fun u => stop u.1) value phase a α
      (Real.sqrt L) (L^A_M) shift top count z ≤
      (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, reverseMarkedValue line (ShiftedBlocks.reverseLevel shift count)
          count marked (fun j xx => grid.sourceShiftedPathPrediction tops slope precision cut weight
            (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
            (fun u => stop u.1) value phase a (Real.sqrt L) μ shift top (xx,y+slope top*xx) j) j x

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedParentMarkedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned-reference interval concentration supplies every local
amplitude bound in the actual marked path theorem. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

def assignedParentMarkedPathBoundAt (q qEnv D Cmass A_M Cweight L : ℝ) (Klocal Hlocal : ℕ) : Prop :=

    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ Klocal) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) Hlocal) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type) (grid : AngularGrid) (tops : Finset τ)
      (T : τ → SlopeBox) (A s w R C F : ℝ) (hw : 0 < w) (hR : 0 < R),
    let slope : τ → ℝ := fun top => (T top).slope;
    let precision : τ → ℝ := fun top => w/(T top).length;
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    ∀ (top : τ), top ∈ tops → R = (T top).length →
    ∀ (hcone : 0 ≤ C+(SourceParameters.branching L)^2) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (hparentCone : 0 ≤ C+(SourceParameters.branching L)^3)
      (hparentWide : (C+(SourceParameters.branching L)^3)*w ≤ P.width),
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hK shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (Z Nmass α μ : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 →
      (∀ k, ‖phase k‖ ≤ Z) → 0 < Nmass → Real.log Nmass ≤ 2*L →
      1 ≤ α → α ≤ 3 → (α-1)/Real.sqrt L ≤ 1/12 → Real.sqrt L*μ = α-1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let squarePackets := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R (slope top) (C+(SourceParameters.branching L)^3) w
    let Qsquare := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^3) w F
      hw hparentCone hF hparentWide hfrequency
    let origSquare := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^3) w
    let squareSelected := (Finset.univ : Finset Qsquare.PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets)
    let S := grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Q := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^2) w F
      hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Qsquare.restrictPackets squareSelected).physicalReferenceBad
      (Qsquare.restrictedAlternate (fun j l => alt j (origSquare j l)) squareSelected)
      (Qsquare.restrictedAlternate_bound (fun j l => alt j (origSquare j l))
        (fun j l => hAlt j (origSquare j l)) squareSelected)
      (slope top) (w/P.topLength) (fun j l => b j (origSquare j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      (slope top) (w/P.topLength) (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) (2*q+11) →
    let n := grid.shiftedPathMass tops slope precision cut weight shift top z
    let _finish := firstMassStop n count (L^A_M)
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let level := ShiftedBlocks.endpoint shift
    let transition := grid.sourceTransition tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) phase z
    let base := grid.sourcePacketBase tops slope precision cut weight assigned
      (fun u => stop u.1) (value z) a z
    let _W := fun j => grid.packetAmplitude
      (packets.filter fun u => assigned u ∉ grid.cellTops tops slope precision cut
        (level (j+1)) (grid.index (level (j+1)) (slope top)))
      (fun u => slope (assigned u)) (fun u => stop u.1) base transition
      (level j) (grid.index (level j) (slope top))
    let _amp := grid.sourceShiftedPathAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) value phase a shift top z
    ∀ (origin y x : ℝ), z = (x,y+slope top*x) →
    let line := sourceReverseLineGrid grid L origin hw shift count
    let mass := fun xx => grid.shiftedPathMass tops slope precision cut weight
      shift top (xx,y+slope top*xx)
    let marked := fun j i => sourceMarkedCell
      (line.cell (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) i)
      (fun xx => mass xx j) (fun xx => mass xx j-mass xx (j+1)) (L^A_M)
    x ∈ line.root → 1 ≤ L^(A+2) →
    (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (A0 : ℝ), 0 ≤ A0 → A0 ≤ L^qEnv → ∀ (hC0 : 0 ≤ C),
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ tops, grid.eligible cut (precision u) 0) →
      (∀ u ∈ tops, weight u z ≤ Cweight) →
      Real.log (max 1 (∑ u ∈ tops, weight u z)) ≤ 3*L →
      Real.log (n 0) ≤ 3*L →
      grid.mass tops slope precision cut weight 0 (grid.index 0 (slope top)) z ≤ L^Cmass*Nmass →
    let hwideLocal : C*w ≤ P.width := by
      have hb : 0 ≤ ((SourceParameters.branching L:ℝ)^2)*w := mul_nonneg (sq_nonneg _) hw.le
      nlinarith only [hwide,hb]
    let Qtop := P.assignedReferenceFamily packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency
    let origTop := P.assignedReferenceOriginalLabel packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency
    let altTop := P.assignedReferenceAlternate packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency alt
    let altTopBound := P.assignedReferenceAlternate_bound packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency alt hAlt;
      (∀ u ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Qtop u).withProfile (altTop u) (altTopBound u)).rawInterval
          (fun j l item => P.physicalMultiplierCoefficient t b v f j (origTop u j l) item.val)
          0 lower upper z.1 (z.2-(T u).slope*z.1)‖ ≤ A0*(weight u z)^8) →
    grid.sourceActivePathValue tops slope precision cut weight (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) packets assigned (fun u => stop u.1) value phase a α
      (Real.sqrt L) (L^A_M) shift top count z ≤
      (Real.exp 3*(1+(L^(qEnv+6))^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, reverseMarkedValue line (ShiftedBlocks.reverseLevel shift count)
          count marked (fun j xx => grid.sourceShiftedPathPrediction tops slope precision cut weight
            (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
            (fun u => stop u.1) value phase a (Real.sqrt L) μ shift top (xx,y+slope top*xx) j) j x

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPathIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inhabited reference adapters preserve every actual coefficient
and masked path amplitude from the unrestricted data. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency
local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

def assignedInhabitedReference (top : τ) := (Q top).inhabitedFamily

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

/-- This is the value supplied to the supported plane theorem. -/
def assignedInhabitedBand (L A : ℝ) (z : ℝ×ℝ) (p : τ×Fin N) : EuclideanSpace ℂ κ :=
  ((Q p.1).inhabitedFamily.withProfile ((Q p.1).inhabitedAlternate (alts alt p.1))
    ((Q p.1).inhabitedAlternate_bound (alts alt p.1) (halt alt hAlt p.1))).rawBand
    (fun j l u => (T p.1).mask L A z •
      (Q p.1).inhabitedFamily.physicalMultiplierCoefficient (T p.1).slope
        (fun j l => selector b p.1 j ((Q p.1).inhabitedOriginalLabel j l)) v f j l u)
    0 p.2 z.1 (z.2-(T p.1).slope*z.1)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataDensityForest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density produces the literal top assignment and witnesses
needed for packet concentration. No disjoint-witness premise is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure PacketDensityForest (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (oldSlope L a cone w tau : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) where
  keepers : Finset packets
  top : keepers → SlopeBox
  assigned : P.PacketIndex → keepers
  witness : keepers → Set (ℝ×ℝ)
  measurable : ∀ i, MeasurableSet (witness i)
  disjoint : Pairwise fun i j => Disjoint (witness i) (witness j)
  subset : ∀ i, witness i ⊆ E
  finite : ∀ i, (volume.prod volume) (witness i) ≠ ∞
  mass : ∀ i, ENNReal.ofReal (L^(-(a+2))*(top i).length*(top i).width) ≤
    (volume.prod volume) (witness i)
  radius : ∀ i z, z ∈ witness i → (top i).radius z ≤ L^(a+2)
  precision : ∀ i z, z ∈ witness i → |u z-(top i).slope| ≤ w/(top i).length
  close : ∀ i z, z ∈ witness i →
    |u z-(top i).slope| ≤ (top i).width/(12*(top i).length)
  width : ∀ i, (top i).width = P.width
  short : ∀ i, (top i).length ≤ tau
  seed_short : ∀ i, P.length i.val.val.1 ≤ (top i).length
  area : (∑ i, (top i).area) ≤ 2*L^a*(volume.prod volume).real E
  area_pos : 0 < ∑ i, (top i).area
  reference : ∀ q ∈ packets,
    P.referenceCondition oldSlope (top (assigned q)).slope
      (top (assigned q)).length cone w q.1 q.2.1
  horizontal : ∀ q ∈ packets,
    |P.actualX q.1 q.2.1 q.2.2-(top (assigned q)).x|+P.length q.1 ≤
      L^(a+3)*(top (assigned q)).length
  transverse : ∀ q ∈ packets,
    |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(top (assigned q)).slope)*
      P.actualX q.1 q.2.1 q.2.2-
      ((top (assigned q)).y-(top (assigned q)).slope*(top (assigned q)).x)|+P.width ≤
        L^(a+3)*(top (assigned q)).width

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataJetControl
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary derivative normalization leaves all physical packet values
and masked analyzing coefficients unchanged. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

abbrev withJetControl (P : PacketLatticeData N κ Label Item) (scale ratio : ℝ)
    (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio) : PacketLatticeData N κ Label Item :=
  { P with scale := scale, ratioBound := ratio, ratioBound_ge_one := hratio, scale_bound := hscale }

@[simp] theorem withJetControl_crossPacketValue (P : PacketLatticeData N κ Label Item)
    (scale ratio : ℝ) (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) (q : P.PacketIndex) :
    (P.withJetControl scale ratio hratio hscale).crossPacketValue alt hAlt t b u g z q=
      P.crossPacketValue alt hAlt t b u g z q := rfl

namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def withJetControl (d : OrdinaryModelConfig P initial) (scale ratio : ℝ)
    (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio) :
    OrdinaryModelConfig (P.withJetControl scale ratio hratio hscale) initial where
  cStar := d.cStar
  cEta := d.cEta
  CEta := d.CEta
  cb := d.cb
  Cv := d.Cv
  w := d.w
  tau := d.tau
  epsilon := d.epsilon
  A := d.A
  margin := d.margin
  F := d.F
  radius := d.radius
  Lip := d.Lip
  M := d.M
  Q := d.Q
  gap := d.gap
  packGap := d.packGap
  R := d.R
  K := d.K
  D0 := d.D0
  cell := d.cell
  grid := d.grid
  selector := d.selector
  hcStar := d.hcStar
  hcEta := d.hcEta
  hCEta := d.hCEta
  hCv := d.hCv
  hcb := d.hcb
  hcbQuarter := d.hcbQuarter
  hspectral := d.hspectral
  hepsilon := d.hepsilon
  hw := d.hw
  hW := d.hW
  hF := d.hF
  hfreq := d.hfreq
  hgap := d.hgap
  hpack := d.hpack
  hmargin := d.hmargin
  hA := d.hA
  hQ := d.hQ
  hQnear := d.hQnear
  hR := d.hR
  horder := d.horder
  hD0 := d.hD0
  htime := d.htime
  hwide := d.hwide
  hK := d.hK
  hLip := d.hLip
  hlocal := d.hlocal
  hrow := d.hrow
  hlength := d.hlength
  heps := d.heps
  spectrum := d.spectrum
  margin_spectrum := d.margin_spectrum
  bin := d.bin
  measurable := d.measurable
  bounded := d.bounded
  away := d.away
  support := d.support
  radius_bound := d.radius_bound
  near := d.near

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction keeps the same geometric constants and selector. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

def restrict (d : OrdinaryModelConfig P initial) (S : Finset P.PacketIndex) (hS : S⊆initial) :
    OrdinaryModelConfig P S where
  cStar := d.cStar
  cEta := d.cEta
  CEta := d.CEta
  cb := d.cb
  Cv := d.Cv
  w := d.w
  tau := d.tau
  epsilon := d.epsilon
  A := d.A
  margin := d.margin
  F := d.F
  radius := d.radius
  Lip := d.Lip
  M := d.M
  Q := d.Q
  gap := d.gap
  packGap := d.packGap
  R := d.R
  K := d.K
  D0 := d.D0
  cell := d.cell
  grid := d.grid
  selector := d.selector
  hcStar := d.hcStar
  hcEta := d.hcEta
  hCEta := d.hCEta
  hCv := d.hCv
  hcb := d.hcb
  hcbQuarter := d.hcbQuarter
  hspectral := d.hspectral
  hepsilon := d.hepsilon
  hw := d.hw
  hW := d.hW
  hF := d.hF
  hfreq := d.hfreq
  hgap := d.hgap
  hpack := d.hpack
  hmargin := d.hmargin
  hA := d.hA
  hQ := d.hQ
  hQnear := d.hQnear
  hR := d.hR
  horder := d.horder
  hD0 := d.hD0
  htime := d.htime
  hwide := d.hwide
  hK := d.hK
  hLip := d.hLip
  hlocal := d.hlocal
  hrow := fun q hq => d.hrow q (hS hq)
  hlength := fun q hq => d.hlength q (hS hq)
  heps := fun q hq => d.heps q (hS hq)
  spectrum := d.spectrum
  margin_spectrum := fun q hq => d.margin_spectrum q (hS hq)
  bin := fun q hq => d.bin q (hS hq)
  measurable := d.measurable
  bounded := d.bounded
  away := d.away
  support := d.support
  radius_bound := d.radius_bound
  near := d.near

end LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPolarization
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four-phase profile combinations on the original labeled geometry,
including transport of the exact ordinary-model hypotheses. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

abbrev polarize (c : ℂ) (hc : ‖c‖=1) : PacketLatticeData N κ Label Item :=
  { P with
    profileBound := 2*P.profileBound
    profileBound_pos := mul_pos (by norm_num) P.profileBound_pos
    profile := fun j l a k => P.profile j l a k+c • alt j l a k
    profile_bound := fun j l a k => planarProfileConstant_polarization_bound
      (P.profile j l a k) (alt j l a k) c hc (2*P.order) P.profileBound
      (P.profile_bound j l a k) (hAlt j l a k) }

theorem polarize_physicalPacket (c : ℂ) (hc : ‖c‖=1)
    (t : ℝ) (j : Fin N) (l : P.labels j) (a : Item j l) (k : κ) :
    (P.polarize alt hAlt c hc).physicalPacket t j l a k=
      P.physicalPacket t j l a k+c • (P.withProfile alt hAlt).physicalPacket t j l a k := by
  apply physicalPlanarPacket_add_smul

theorem polarize_fourier_nonzero (c : ℂ) (hc : ‖c‖=1)
    (t : ℝ) (j : Fin N) (l : P.labels j) (a : Item j l) (k : κ) (xi eta : ℝ)
    (hn : planarAngularFourier ((P.polarize alt hAlt c hc).physicalPacket t j l a k) (xi,eta)≠0) :
    planarAngularFourier (P.physicalPacket t j l a k) (xi,eta)≠0 ∨
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket t j l a k) (xi,eta)≠0 := by
  by_cases h : planarAngularFourier (P.physicalPacket t j l a k) (xi,eta)=0
  · right
    intro h'
    apply hn
    rw [P.polarize_physicalPacket alt hAlt c hc,planarAngularFourier_add_smul,h,h',mul_zero,add_zero]
  · exact Or.inl h

namespace OrdinaryModelConfig
variable {P} {initial : Finset P.PacketIndex}

def polarize (d : OrdinaryModelConfig P initial)
    (c : ℂ) (hc : ‖c‖=1)
    (hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width) :
    OrdinaryModelConfig (P.polarize alt hAlt c hc) initial where
  cStar := d.cStar
  cEta := d.cEta
  CEta := d.CEta
  cb := d.cb
  Cv := d.Cv
  w := d.w
  tau := d.tau
  epsilon := d.epsilon
  A := d.A
  margin := d.margin
  F := d.F
  radius := d.radius
  Lip := d.Lip
  M := d.M
  Q := d.Q
  gap := d.gap
  packGap := d.packGap
  R := d.R
  K := d.K
  D0 := d.D0
  cell := d.cell
  grid := d.grid
  selector := d.selector
  hcStar := d.hcStar
  hcEta := d.hcEta
  hCEta := d.hCEta
  hCv := d.hCv
  hcb := d.hcb
  hcbQuarter := d.hcbQuarter
  hspectral := d.hspectral
  hepsilon := d.hepsilon
  hw := d.hw
  hW := d.hW
  hF := d.hF
  hfreq := d.hfreq
  hgap := d.hgap
  hpack := d.hpack
  hmargin := d.hmargin
  hA := d.hA
  hQ := d.hQ
  hQnear := d.hQnear
  hR := d.hR
  horder := d.horder
  hD0 := d.hD0
  htime := d.htime
  hwide := d.hwide
  hK := d.hK
  hLip := d.hLip
  hlocal := d.hlocal
  hrow := d.hrow
  hlength := d.hlength
  heps := d.heps
  measurable := d.measurable
  bounded := d.bounded
  away := d.away
  support := d.support
  radius_bound := d.radius_bound
  near := d.near
  spectrum := fun j l a k xi et hn => by
    rcases P.polarize_fourier_nonzero alt hAlt c hc 0 j l a k xi et hn with h | h
    · exact d.spectrum j l a k xi et h
    · exact hSpectrum j l a k xi et h
  margin_spectrum := fun q hq k xi et hn => by
    rcases P.polarize_fourier_nonzero alt hAlt c hc 0 q.1 q.2.1 q.2.2 k xi et hn with h | h
    · exact d.margin_spectrum q hq k xi et h
    · exact hMargin q hq k xi et h
  bin := fun q hq k xi et hn => by
    rcases P.polarize_fourier_nonzero alt hAlt c hc 0 q.1 q.2.1 q.2.2 k xi et hn with h | h
    · exact d.bin q hq k xi et h
    · exact hBin q hq k xi et h

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularModel
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Build the three actual ordinary models from one angular assignment.
The assignment is common to all carrier components. It only partitions
the original packet indices; every physical wave and site is preserved. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def angularPackets (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
    (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice) (g : DyadicLineGrid.GridChoice) :
    Finset P.PacketIndex := initial.filter (fun a => tag a.1 a.2.1=g)

def angularSelector (P : PacketLatticeData N κ Label Item)
    (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice) (g : DyadicLineGrid.GridChoice)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (j : Fin N) (l : P.labels j) (k : κ) (s : ℝ) : ℂ :=
  if tag j l=g then b j l k s else 0

def angularModelConfig (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex)
    (cStar cEta CEta cb Cv w F radius : ℝ) (M : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4)
    (num : OrdinaryModelNumerics cStar cEta cb radius)
    (hw : 0<w) (hW : w≤P.width) (hF : 0≤F) (hr : 0 ≤ radius)
    (horder : 207≤P.order) (hfreq : ∀ k, |P.frequency k|≤F/w)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice) (cell : ∀ j, P.labels j → ℤ)
    (hcover : ∀ j l,
      (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
        s∈scaledAngularCell (w/P.topLength) (tag j l).val j.val (cell j l)) ∧
      (∀ xi eta, cEta≤w*eta → |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
        Icc (-xi/eta-cb*(w/P.length j)) (-xi/eta+cb*(w/P.length j))⊆
          scaledAngularCell (w/P.topLength) (tag j l).val j.val (cell j l)))
    (spectrum : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta)
    (bin : ∀ j l a k xi et,
      planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (measurable : ∀ j l k, Measurable (b j l k))
    (bounded : ∀ j l k s, ‖b j l k s‖≤1)
    (away : ∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|)
    (radius_bound : ∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j))
    (near : ∀ j l k s t, |s-t|≤w/P.length j →
      ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j))
    (g : DyadicLineGrid.GridChoice) : OrdinaryModelConfig P (P.angularPackets initial tag g) := by
  refine ordinaryModelOfGeometry P (P.angularPackets initial tag g)
    cStar cEta CEta cb Cv w F radius M hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num
    hw hW hF hr horder hfreq hlocal cell g.val ?_ spectrum ?_ bin
    (P.angularSelector tag g b) ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq
    have heq := (Finset.mem_filter.mp hq).2
    have h := (hcover q.1 q.2.1).1 (P.rowSlope q.1 q.2.1) (by
      simpa only [sub_self,abs_zero] using mul_nonneg hr (div_pos hw (P.length_pos q.1)).le)
    simpa only [heq] using h
  · intro q hq k xi et hs
    have heq := (Finset.mem_filter.mp hq).2
    have hspec := spectrum q.1 q.2.1 q.2.2 k xi et hs
    simpa only [heq] using (hcover q.1 q.2.1).2 xi et hspec.2.1 hspec.1
  · intro j l k
    change Measurable (fun s : ℝ => if tag j l=g then b j l k s else 0)
    by_cases h : tag j l=g
    · simpa [angularSelector,h] using measurable j l k
    · simp [h]
  · intro j l k s
    by_cases h : tag j l=g
    · simpa [angularSelector,h] using bounded j l k s
    · simp [angularSelector,h]
  · intro j l k s hs
    by_cases h : tag j l=g
    · exact away j l k s (by simpa [angularSelector,h] using hs)
    · simp [angularSelector,h] at hs
  · intro j l k s hs
    by_cases h : tag j l=g
    · simpa only [h] using (hcover j l).1 s (radius_bound j l k s (by
        simpa [angularSelector,h] using hs))
    · simp [angularSelector,h] at hs
  · intro j l k s hs
    by_cases h : tag j l=g
    · exact radius_bound j l k s (by simpa [angularSelector,h] using hs)
    · simp [angularSelector,h] at hs
  · intro j l k s t hst
    by_cases h : tag j l=g
    · simpa [angularSelector,h] using near j l k s t hst
    · simp only [angularSelector,h,ite_false, if_false,sub_self,norm_zero]
      exact div_nonneg (abs_nonneg _) (div_pos hw (P.length_pos j)).le

end LipschitzHilbert.PacketLatticeData

end

end OAI
end


