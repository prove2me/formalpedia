-- Prove2me | Definitions.Def_OAIQ252P017
-- name    : OAIQ252P017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:52:43.568636+00:00
-- url     : https://prove2.me/theorems/f508f85b-583a-42e6-9e26-b86274f73a95
-- title:
--   Definitions bundle OAIQ252P017 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 518 declarations of OpenAI's Lean: 412 definitions, 5 instances, 100 theorems and 1 other declaration. The definitions and types are `OAI.PerfectCompleteness.FixedStoppedDecoderLaw.familySampleFintype`, `OAI.PerfectCompleteness.FixedStoppedNativeLaw.sourceSampleEquiv`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.RowValid`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.answerFintype`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.decodeTable`, `OAI.PerfectCompleteness.HierarchicalAllDecoderTables.upperTableLaw`, `OAI.PerfectCompleteness.HierarchicalDecoderTables.Valid`, `OAI.PerfectCompleteness.HierarchicalDecoderTables.decode`, `OAI.PerfectCompleteness.HierarchicalLowerInverse.Answer`, `OAI.PerfectCompleteness.HierarchicalLowerInverse.answerFintype`, `OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable`, `OAI.PerfectCompleteness.HierarchicalProjectedAverage.RawSample`, `OAI.PerfectCompleteness.HierarchicalProjectedAverage.expectedMeeting`, `OAI.PerfectCompleteness.HierarchicalProjectedAverage.meetingProbability`, `OAI.PerfectCompleteness.HierarchicalProjectedAverage.predictionDifference`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.RawSample`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.Sample`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.arrays`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.experiment`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.originalLaw`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.rawLaw`, `OAI.PerfectCompleteness.HierarchicalProjectedExperiment.rawRead`, `OAI.PerfectCompleteness.HierarchicalProjectedOuterAverage.expectedMeeting`, `OAI.PerfectCompleteness.HierarchicalProjectedOuterAverage.experiment`, `OAI.PerfectCompleteness.HierarchicalProjectedOuterAverage.predictionDifference`, `OAI.PerfectCompleteness.HierarchicalProjectedPrediction.rawJ`, `OAI.PerfectCompleteness.HierarchicalProjectedPrediction.rawPrediction`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.J`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.Raw`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.Visible`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.goodEvent`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.goodRecord`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.law`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.meetingProbability`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.prediction`, `OAI.PerfectCompleteness.HierarchicalProjectedRawMeeting.meetingProbability`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.Raw`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.VisibleGood`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.columnSpace` and 372 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Construction_OriginalCutBucketReplacement`, `PerfectCompleteness_Construction_OriginalHiddenChild`, `PerfectCompleteness_Construction_OriginalOwnBucketSplit`, `PerfectCompleteness_Construction_SourceChildKernelLemmas`, `PerfectCompleteness_Construction_SourceQuestionPairPullback`, `PerfectCompleteness_Construction_SourceQuestionPhysicalHigh`, `PerfectCompleteness_Construction_SourceQuestionRawSwap`, `PerfectCompleteness_Construction_SourceQuestionUnmarkedRange`, `PerfectCompleteness_Construction_StoppedProjectedBucketIndex`, `PerfectCompleteness_Construction_StoppedProjectedBuckets`, `PerfectCompleteness_Decoding_CutGroupedProjectionLemmas`, `PerfectCompleteness_Decoding_FixedStoppedDecoderLaw`, `PerfectCompleteness_Decoding_HierarchicalAllDecoderTables`, `PerfectCompleteness_Decoding_HierarchicalDecoderTables`, `PerfectCompleteness_Decoding_HierarchicalLowerInverseLemmas`, `PerfectCompleteness_Decoding_LowerCutBucketLocality`, `PerfectCompleteness_Decoding_LowerCutFiberDisintegrationLemmas`, `PerfectCompleteness_Decoding_LowerCutFormCollision`, `PerfectCompleteness_Decoding_LowerCutNodeCoordinates`, `PerfectCompleteness_Decoding_LowerCutPairBackground`, `PerfectCompleteness_Decoding_LowerCutPairLemmas`, `PerfectCompleteness_Decoding_LowerCutScalarProjectionLemmas`, `PerfectCompleteness_Decoding_LowerCutUniformCoordinatesLemmas`, `PerfectCompleteness_Decoding_LowerProjectedFiberAverage`, `PerfectCompleteness_Decoding_LowerProjectedOriginalSuccessLemmas`, `PerfectCompleteness_Decoding_ProjectedLowerFiber`, `PerfectCompleteness_Decoding_SourceQuestionCollisionTransportLemmas`, `PerfectCompleteness_Decoding_SourceQuestionPhysicalCollision`, `PerfectCompleteness_Decoding_UpperScalarCutCalls`, `PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas`, `PerfectCompleteness_Foundations_HierarchicalProjectedExperimentLemmas`, `PerfectCompleteness_Foundations_HierarchicalProjectedPredictionLemmas`, `PerfectCompleteness_Foundations_HierarchicalProjectedRawAverage`, `PerfectCompleteness_Foundations_HierarchicalProjectedRawMeeting`, `PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas`, `PerfectCompleteness_Foundations_NormalizationLemmas`, `PerfectCompleteness_Foundations_OriginalPrefixContinuation`, `PerfectCompleteness_Foundations_OriginalWholeCut`, `PerfectCompleteness_Foundations_OriginalWholeCutBridge`, `PerfectCompleteness_Foundations_PCPSource`, `PerfectCompleteness_Foundations_ProjectedFiberSquare`, `PerfectCompleteness_Foundations_ProjectedMeetingTransport`, `PerfectCompleteness_Foundations_SlotProjectedExperiment`, `PerfectCompleteness_Foundations_SourcePhysicalExteriorSwap`, `PerfectCompleteness_Foundations_SourcePhysicalSourceSwapLemmas`, `PerfectCompleteness_Foundations_SourceProjectedChoices`, `PerfectCompleteness_Foundations_SourceProjectedTag`, `PerfectCompleteness_Foundations_StoppedPathHead`, `PerfectCompleteness_Foundations_StoppedProjectedArrays`, `PerfectCompleteness_Foundations_StoppedProjectedContext`, `PerfectCompleteness_Foundations_StoppedProjectedExperiment`, `PerfectCompleteness_Foundations_StoppedProjectedOldRecord`, `PerfectCompleteness_Foundations_StoppedProjectedPhysicalAdvice`, `PerfectCompleteness_Foundations_StoppedProjectedUsefulEvent`, `PerfectCompleteness_Foundations_StoppedSharedEvents`, `PerfectCompleteness_Foundations_WholeCutReplayGroupingTransport`, `PerfectCompleteness_Foundations_WholeCutReplayLemmas`, `PerfectCompleteness_Machines_LowerCutInstalledInput`, `PerfectCompleteness_Machines_NormalizedTargetMachine`, `PerfectCompleteness_Machines_NormalizedTargetTapeBound`, `PerfectCompleteness_Machines_OriginalWholeCutTape`, `PerfectCompleteness_Machines_OwnInputAffineSliceLemmas`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Machines_PreprocessingMachineLemmas`, `PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas`, `PerfectCompleteness_Machines_SourceOccurrenceLoopMachine`, `PerfectCompleteness_Machines_SourceOccurrenceMachine`, `PerfectCompleteness_Machines_SourceOccurrenceProducerLemmas`, `PerfectCompleteness_Machines_SourcePhysicalTapeLaw`, `PerfectCompleteness_Machines_StoppedOwnInputGeometry`, `PerfectCompleteness_Machines_WholeArrayInteriorOwnInputLaw`, `PerfectCompleteness_Reduction_FixedTargetValue`, `PerfectCompleteness_Reduction_HierarchicalFixedAdviceFamilyLemmas`, `PerfectCompleteness_Reduction_NormalizedTarget`, `PerfectCompleteness_Reduction_NormalizedTargetInitialization`, `PerfectCompleteness_Reduction_PreliminaryLevelPair`, `PerfectCompleteness_Repetition_StoppedCleanGeometry`, `PerfectCompleteness_Sampling_FixedStoppedPhysicalLawLemmas`, `PerfectCompleteness_Sampling_OriginalWholeCutLaw`, `PerfectCompleteness_Sampling_SamplerComposition`, `PerfectCompleteness_Sampling_SourceChildKernelLaw`, `PerfectCompleteness_Sampling_SourceChildKernelMarginalLemmas`, `PerfectCompleteness_Sampling_SourceChildMarkedLaw`, `PerfectCompleteness_Sampling_SourceChildQuestionLaw`, `PerfectCompleteness_Sampling_SourcePhysicalWholeLaw`, `PerfectCompleteness_Sampling_StoppedProjectedGlobalLawLemmas`, `PerfectCompleteness_Sampling_StoppedProjectedMeetingLaw`, `PerfectCompleteness_Sampling_StoppedSharedSampler`, `PerfectCompleteness_Sampling_WholeCutSampler`, `UniqueGames_Machines_FinalCNFOutputLemmas`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PreprocessingTableSpectral`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_TableGapReductionLemmas`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P012`, `OAIQ252P013`, `OAIQ252P014` and `OAIQ252P015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P018` and `OAIQ252P019`; the statements `OAI.PerfectCompleteness.CleanNativeReplay.leftReplay_heq`, `OAI.PerfectCompleteness.CleanNativeReplay.rightReplay_heq`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.physical_probability_eq_observed`, `OAI.PerfectCompleteness.FixedLowerUniformCollision.supported_collision_lt`, `OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable_agreement_lt`, `OAI.PerfectCompleteness.HierarchicalProjectedPrediction.J_probability`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.given_eq_jointEvent`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rawPrediction_eq`, `OAI.PerfectCompleteness.LowerCutFiberDisintegration.pair_coordinates`, `OAI.PerfectCompleteness.LowerCutPairBackground.arraysPair_law`, `OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.reconstruct_eq_arraysAt`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.meanSuccess_square_le`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision_eq_mean`, `OAI.PerfectCompleteness.LowerProjectedOriginalSuccess.fiberSuccess_eq`, `OAI.PerfectCompleteness.LowerProjectedOriginalSuccess.rawSuccess_eq_meanSuccess`, `OAI.PerfectCompleteness.OriginalHiddenChild.rawMap_law`, `OAI.PerfectCompleteness.OriginalHiddenConditional.observed_variation`, `OAI.PerfectCompleteness.OriginalPrefixContinuation.raw_observed_variation`, `OAI.PerfectCompleteness.ProjectedFiberSquare.success_square_le`, `OAI.PerfectCompleteness.SourceChildMarkedLaw.original_extended_marked_law`, `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.expectation_swap`, `OAI.PerfectCompleteness.SourcePhysicalStoppedComparison.conditional_variation`, `OAI.PerfectCompleteness.SourceQuestionPhysicalCollision.rawEvent_observe`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.physicalFiber_probability` and `OAI.PerfectCompleteness.WholeArrayInteriorOwnInputLaw.exposedRead_law`; the proofs of `OAI.PerfectCompleteness.CleanDecoderRate.bound`, `OAI.PerfectCompleteness.CleanNativeReplay.leftReplay_heq`, `OAI.PerfectCompleteness.CleanNativeReplay.rightArrays_heq`, `OAI.PerfectCompleteness.CleanNativeReplay.rightReplay_heq`, `OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.rightKernel_heq`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.physical_probability_eq_observed`, `OAI.PerfectCompleteness.CleanPhysicalHighEvent.mean_probability_eq`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible`, `OAI.PerfectCompleteness.CleanPhysicalReplayLaw.evaluate_physicalTape_law`, `OAI.PerfectCompleteness.FixedLowerUniformCollision.supported_collision_lt`, `OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable_agreement_lt`, `OAI.PerfectCompleteness.HierarchicalProjectedPrediction.J_probability`, `OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.given_eq_jointEvent`, `OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rawPrediction_eq`, `OAI.PerfectCompleteness.LowerCutFiberDisintegration.pair_coordinates`, `OAI.PerfectCompleteness.LowerCutPairBackground.arraysPair_law`, `OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.reconstruct_eq_arraysAt`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.meanSuccess_square_le`, `OAI.PerfectCompleteness.LowerProjectedFiberAverage.rawCollision_eq_mean`, `OAI.PerfectCompleteness.LowerProjectedOriginalSuccess.fiberSuccess_eq`, `OAI.PerfectCompleteness.LowerProjectedOriginalSuccess.rawSuccess_eq_meanSuccess`, `OAI.PerfectCompleteness.OriginalHiddenChild.rawMap_law`, `OAI.PerfectCompleteness.OriginalHiddenConditional.observed_variation`, `OAI.PerfectCompleteness.OriginalPrefixContinuation.raw_observed_variation`, `OAI.PerfectCompleteness.ProjectedFiberSquare.success_square_le`, `OAI.PerfectCompleteness.SourceChildMarkedLaw.original_extended_marked_law`, `OAI.PerfectCompleteness.SourcePhysicalSourceSwap.expectation_swap`, `OAI.PerfectCompleteness.SourcePhysicalStoppedComparison.conditional_variation`, `OAI.PerfectCompleteness.SourcePhysicalTapeFiber.collapse_physicalTape_law`, `OAI.PerfectCompleteness.SourceQuestionPhysicalCollision.rawEvent_observe`, `OAI.PerfectCompleteness.StoppedProjectedExperiment.physicalFiber_probability` and `OAI.PerfectCompleteness.WholeArrayInteriorOwnInputLaw.exposedRead_law`.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_PerfectCompleteness
import Definitions.Def_OAIQ252P012
import Definitions.Def_OAIQ252P013
import Definitions.Def_OAIQ252P014
import Definitions.Def_OAIQ252P015

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SamplerComposition
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SamplerComposition

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

def collapseSuffix (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :
    RecursiveSampler.Tape 𝕜 repeats (p.append q) A → RecursiveSampler.Tape 𝕜 repeats p A :=
  collapseExpanded 𝕜 repeats p q A ∘ expandEquiv 𝕜 repeats p q A

end
end PerfectCompleteness.SamplerComposition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeCutSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutSampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def rootLaw (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (RootTape rows repeats p slots) :=
  FiniteProduct.law (fun _ : BucketSampler.Direction (rows n) =>
    CutSamplerRefinement.tapeLaw F2 repeats p (LeafDomain slots))

def tapeLaw (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n m) →
      (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) →
        FiniteDistribution (Tape rows repeats p slots)
  | 0, _, .refl _, slots => FiniteDistribution.uniform (Arrays slots rows)
  | n + 1, _, .refl _, slots =>
      CutChildGrouping.rawLaw (C := Fin (rows (n + 1))) slots rows
  | _, _, .step i p, slots =>
      (rootLaw rows repeats (.step i p) slots).product
        ((tapeLaw rows repeats p (childSlots slots i)).product
          (FiniteProduct.law (fun j : RecursiveSampler.OffPath i =>
            FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows))))

def law (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Arrays slots rows) :=
  (tapeLaw rows repeats p slots).pushforward (evaluate rows repeats p slots)

end

end PerfectCompleteness.WholeCutSampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OriginalWholeCutTape
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutTape

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

instance exteriorFintype (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Exterior rows repeats p slots) := exteriorFintypeAux rows repeats p slots

def exteriorZero (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) → Exterior rows repeats p slots
  | _, _, .refl _, _ => ()
  | _, _, .step i p, slots =>
      ((fun _ j => RecursiveSampler.zeroDraw F2 repeats (.step i p) (LeafDomain slots) j.val),
        (exteriorZero rows repeats p (childSlots slots i), fun _ _ _ => 0))

instance exteriorNonempty (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nonempty (Exterior rows repeats p slots) := ⟨exteriorZero rows repeats p slots⟩

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Exterior rows repeats p slots) := FiniteDistribution.uniform _

def callsLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Calls rows repeats p chosen q slots) :=
  FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p =>
    RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))

def belowLaw (rows repeats : Nat → Nat) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (BelowTape rows repeats chosen q slots) :=
  (WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).product
    (FiniteProduct.law (fun j : RecursiveSampler.OffPath chosen =>
      FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)))

end

end PerfectCompleteness.OriginalWholeCutTape

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

def belowEvaluate (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (ω : BelowTape rows repeats chosen q slots) : ChildArrays rows slots :=
  WholeArraySampler.childrenAt slots rows chosen
    (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) ω.1) ω.2

def reconstructBuckets (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : BucketSampler.Direction (rows n) →
      OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain slots))
    (exterior : BucketSampler.Direction (rows n) →
      OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots)) :
    Fin (rows n) → H slots :=
  BucketSampler.evaluate (rows n) id (fun direction =>
    OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain slots)
      (values direction) (exterior direction))

def reconstruct (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Exterior rows repeats p slots → Values rows repeats p slots →
          BelowArrays rows p slots → Arrays slots rows
  | _, m, .refl _, slots, _, values, below =>
      WholeArraySampler.assemble slots rows
        (BucketSampler.evaluate (rows (m + 1)) (id : H slots → H slots) values) below
  | _, _, .step i p, slots, exterior, values, below =>
      WholeArraySampler.assemble slots rows
        (reconstructBuckets rows repeats (.step i p) slots
          (fun direction terminal => values (.inl (direction, terminal))) exterior.1)
        (WholeArraySampler.childrenAt slots rows i
          (reconstruct rows repeats p (childSlots slots i) exterior.2.1
            (fun call => values (.inr call)) below) exterior.2.2)

end
end PerfectCompleteness.OriginalWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalCutBucketReplacement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketReplacement

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def ownValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : Values rows repeats p slots) :
    BucketSampler.Direction (rows (m + 1)) → H (cutSlots p slots) :=
  fun a => values (OriginalCutCalls.ownBucket rows repeats p a)

def replaceValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : Values rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    Values rows repeats p slots :=
  Function.update values (OriginalCutCalls.ownBucket rows repeats p a) fresh

end
end PerfectCompleteness.OriginalCutBucketReplacement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.Normalization

open UniqueGamesTheorem.Foundations
open Target
open SourceClause

theorem main_eval_of_copies_match (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool)
    (hcopy : ∀ i : Fin 3,
      B (copyVariable F c i) = B (oldVariable F (PCP.clauseAt F c)[i].variableIndex)) :
    (mainClause F c).clause.eval B = (PCP.clauseAt F c).eval (restrictAssignment F B) := by
  simp [mainClause, normalizedTriple, tripleClause, Clause.eval, Literal.eval,
    restrictAssignment, hcopy]

theorem equalityClauses_failures (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) (B : Fin (outputVariables F) → Bool) :
    PCP.VerifierToCNF.clauseFailures
      ((equalityClauses F c i).map NormalizedClause.clause) B =
      if B (copyVariable F c i) = B (oldVariable F (PCP.clauseAt F c)[i].variableIndex)
        then 0 else 1 := by
  cases hx : B (copyVariable F c i) <;>
    cases hv : B (oldVariable F (PCP.clauseAt F c)[i].variableIndex) <;>
    cases hz : B (paddingVariable F c) <;>
    simp only [Fin.getElem_fin] at hv <;>
    simp [PCP.VerifierToCNF.clauseFailures, equalityClauses, normalizedTriple,
      tripleClause, Clause.eval, Literal.eval, hx, hv, hz]

theorem gadget_failures (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool) :
    PCP.VerifierToCNF.clauseFailures (gadgetClauses F c) B =
      (if (mainClause F c).clause.eval B then 0 else 1) +
      (if B (copyVariable F c 0) = B (oldVariable F (PCP.clauseAt F c)[0].variableIndex)
        then 0 else 1) +
      (if B (copyVariable F c 1) = B (oldVariable F (PCP.clauseAt F c)[1].variableIndex)
        then 0 else 1) +
      (if B (copyVariable F c 2) = B (oldVariable F (PCP.clauseAt F c)[2].variableIndex)
        then 0 else 1) := by
  simp only [gadgetClauses, gadget, List.map_append,
    PCP.VerifierToCNF.clauseFailures_append, equalityClauses_failures]
  cases hmain : (mainClause F c).clause.eval B <;>
    simp [PCP.VerifierToCNF.clauseFailures, hmain]

theorem clauseFailures_zero_iff {n : Nat} (cs : List (Clause n)) (B : Fin n → Bool) :
    PCP.VerifierToCNF.clauseFailures cs B = 0 ↔ ∀ c ∈ cs, c.eval B = true := by
  rw [PCP.VerifierToCNF.clauseFailures, PCP.VerifierToCNF.zero_false_count_iff_all]
  simp only [List.all_map, Function.comp_def, id_eq, List.all_eq_true]

theorem gadget_complete_of_copies_match (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool)
    (hcopy : ∀ i : Fin 3,
      B (copyVariable F c i) = B (oldVariable F (PCP.clauseAt F c)[i].variableIndex))
    (hsat : (PCP.clauseAt F c).eval (restrictAssignment F B) = true) :
    ∀ d ∈ gadgetClauses F c, d.eval B = true := by
  apply (clauseFailures_zero_iff _ B).1
  rw [gadget_failures, main_eval_of_copies_match F c B hcopy, hsat]
  simp [hcopy]

theorem gadget_failure_domination (F : Formula) (c : Fin F.clauses.length)
    (B : Fin (outputVariables F) → Bool) :
    (if (PCP.clauseAt F c).eval (restrictAssignment F B) then 0 else 1) ≤
      PCP.VerifierToCNF.clauseFailures (gadgetClauses F c) B := by
  rw [gadget_failures]
  by_cases h0 : B (copyVariable F c 0) =
      B (oldVariable F (PCP.clauseAt F c)[0].variableIndex)
  · by_cases h1 : B (copyVariable F c 1) =
        B (oldVariable F (PCP.clauseAt F c)[1].variableIndex)
    · by_cases h2 : B (copyVariable F c 2) =
          B (oldVariable F (PCP.clauseAt F c)[2].variableIndex)
      · have hcopy : ∀ i : Fin 3,
            B (copyVariable F c i) =
              B (oldVariable F (PCP.clauseAt F c)[i].variableIndex) := by
          intro i
          have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi with rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h2
        rw [main_eval_of_copies_match F c B hcopy]
        simp [h0, h1, h2]
      · cases (PCP.clauseAt F c).eval (restrictAssignment F B) <;>
          simp [h0, h1, h2]
    · cases (PCP.clauseAt F c).eval (restrictAssignment F B) <;>
        simp [h0, h1]
      omega
  · cases (PCP.clauseAt F c).eval (restrictAssignment F B) <;>
      simp [h0]
    omega

theorem normalize_completeness (F : Formula) (hs : F.Satisfiable) :
    (normalize F).Satisfiable := by
  obtain ⟨A, hA⟩ := hs
  refine ⟨extendAssignment F A, ?_⟩
  intro d hd
  obtain ⟨c, _, hd⟩ := List.mem_flatMap.mp hd
  apply gadget_complete_of_copies_match F c (extendAssignment F A) ?_ ?_ d hd
  · intro i
    simp
  · rw [restrict_extend]
    exact hA _ (List.getElem_mem c.isLt)

theorem failedCount_domination (F : Formula) (B : Fin (normalize F).variables → Bool) :
    PCP.NameCompaction.failedCount F (restrictAssignment F B) ≤
      PCP.NameCompaction.failedCount (normalize F) B := by
  change Fin (outputVariables F) → Bool at B
  change (PCP.NameCompaction.evaluationList F (restrictAssignment F B)).count false ≤
    PCP.VerifierToCNF.clauseFailures ((PCP.allIndices F).flatMap (gadgetClauses F)) B
  rw [← PCP.NameCompaction.evaluations_allIndices F (restrictAssignment F B),
    PCP.VerifierToCNF.count_false_map_sum, PCP.VerifierToCNF.clauseFailures_flatMap]
  exact PCP.VerifierToCNF.nat_sum_map_le _ _ _
    (fun c _ => gadget_failure_domination F c B)

theorem normalize_reflects (F : Formula) (hs : (normalize F).Satisfiable) :
    F.Satisfiable := by
  obtain ⟨B, hB⟩ := hs
  have hout : PCP.NameCompaction.failedCount (normalize F) B = 0 :=
    (clauseFailures_zero_iff (normalize F).clauses B).2 hB
  have hin : PCP.NameCompaction.failedCount F (restrictAssignment F B) = 0 := by
    have h := failedCount_domination F B
    rw [hout] at h
    omega
  exact ⟨restrictAssignment F B, (clauseFailures_zero_iff F.clauses _).1 hin⟩

theorem normalize_satisfiable_iff (F : Formula) :
    (normalize F).Satisfiable ↔ F.Satisfiable :=
  ⟨normalize_reflects F, normalize_completeness F⟩

end PerfectCompleteness.Normalization



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTableSpectral
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

open PoweringWalks SpectralReturn

/-- The stored overlaid graph is the actual semantic overlay in numbered
port coordinates. This is equality of reversible port graphs. -/
theorem overlay_portGraph {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.portGraph (PreprocessingOverlayTables.overlay G H) =
      GraphTransport.reindex
        (Overlay.portGraph (PortTables.portGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (PreprocessingOverlayTables.overlayPorts d e) := by
  unfold PreprocessingOverlayTables.overlay
  rw [materialize_portGraph]
  rfl

/-- An actual half-spectral expander overlay gives a `7/8` certificate for
the stored table. The original table needs no spectral certificate.
The degree hypothesis supplies nonempty old and expander port types. -/
theorem overlay_certificate_seven_eighths {n d e : Nat}
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (hn : 0 < n) (hdegree : d = e + 1) (he : 8 ≤ e)
    (hH : SpectralCertificate (ExpanderTables.graph H) (1 / 2 : ℝ)) :
    SpectralCertificate (PortTables.portGraph (PreprocessingOverlayTables.overlay G H))
      (7 / 8 : ℝ) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [overlay_portGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply Overlay.spectralCertificate_seven_eighths
    (PortTables.portGraph G) (ExpanderTables.graph H)
  · simpa only [Fintype.card_fin] using hdegree
  · simp only [Fintype.card_fin]
    omega
  · exact hH

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTableSpectral

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringPortReindexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

variable (accepts : Edge V E → A → A → Bool)

omit rotation in
/-- The same exact table bound with a separately stored walk parameter. Its
proved equality may be used without evaluating a huge closed alphabet size. -/
theorem lazy_table_uniform_count_gap_at {vertices d : Nat}
    (input : PortTables.Table vertices d) (hv : 0 < vertices) (hd : 0 < d)
    (lambda : ℝ)
    (certificate : SpectralCertificate (lazyGraph (PortTables.portGraph input)) lambda)
    (M : Nat) (hM : 1 ≤ M) (n : Nat) (hn : n = 2*center 64 M)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hgap : ∀ assignment : Fin vertices → Fin 64,
      epsilon * (Fintype.card (Fin vertices × Fin (2*d)) : ℝ) ≤
        ((PortTables.baseGraph (PreprocessingOverlayTables.lazy input)).rejectionCount
          assignment : ℝ)) :
    ∀ labels : PoweringTableSemantics.EncodedLabeling vertices (2*d) n,
    (gain 64 M lambda * min epsilon (1 / ((n+1 : Nat) : ℝ))) *
      ((PoweringTables.table (PreprocessingOverlayTables.lazy input) n).darts : ℝ) ≤
      ((GenericGraphTables.semantics
        (PoweringTables.table (PreprocessingOverlayTables.lazy input) n)).rejectionCount
          labels : ℝ) := by
  subst n
  exact lazy_table_uniform_count_gap input hv hd lambda certificate M hM
    epsilon hepsilon hgap

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

theorem overlay_certificate (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) :
    SpectralCertificate (PortTables.portGraph
      (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))) (7 / 8 : ℝ) :=
  PreprocessingTableSpectral.overlay_certificate_seven_eighths _ _
    (vertices_positive t) rfl PreprocessingRegularSoundness.internalDegree_ge_eight
    (overlayFamily_certificate H certificate t)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingGuarantees

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFOutputLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


theorem emittedBytes_eq_formulaBits (table : GraphTables.Table) :
    emittedBytes rowPlan table = formulaBits (FinalTableFormula.output table) :=
  header_append_outputStream table

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCanonicalOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTableGap

open RoundTables
open PoweringWalks SpectralReturn

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem powered_count_gap (input : Input)
    (labeling : Fin (powered H input.val).vertices → Fin alphabet) :
    RoundGap.poweredLower (gap input) * ((powered H input.val).darts : ℝ) ≤
      ((GenericGraphTables.semantics (powered H input.val)).rejectionCount labeling : ℝ) := by
  let old := PreprocessingOverlayTables.overlay
    (PreprocessingTables.padded H input.val) (PreprocessingTables.overlayFamily H input.val)
  have hd : 0 < (PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree := by omega
  let : Nonempty (Fin ((PreprocessingRegularTables.internalDegree + 1) +
      PreprocessingRegularTables.internalDegree)) := ⟨⟨0, hd⟩⟩
  have spectral : SpectralCertificate (lazyGraph (PortTables.portGraph old)) (31 / 32 : ℝ) :=
    LazySpectral.lazy_certificate_31_32 (PortTables.portGraph old)
      (PreprocessingGuarantees.overlay_certificate H certificate input.val)
  have lower := PreprocessingGuarantees.gap_transfer_real H certificate input.val input.property
    (gap input) (gap_nonnegative input)
    (by simpa only [Fintype.card_fin] using
      ((GraphTables.semantics input.val).le_gap_iff (gap input)).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := Nat.cast_pos.mpr Preprocessing.sizeFactor_positive
  have hn : walkParameter = 2 * PoweringSoundness.center 64 FinalConstants.windowHalf :=
    walkParameter_eq
  have bound := PoweringPortReindex.lazy_table_uniform_count_gap_at old
    (PreprocessingTables.vertices_positive input.val) hd (31 / 32) spectral
    FinalConstants.windowHalf FinalConstants.windowHalf_positive walkParameter hn
    (gap input / Preprocessing.sizeFactor) (div_nonneg (gap_nonnegative input) hs.le)
    lower labeling
  have hw : walkParameter + 1 = FinalConstants.walkLength := by
    rw [walkParameter_eq]
    rfl
  simpa only [RoundGap.poweredLower, PoweringFinalConstants.card_alphabet,
    hw, FinalConstants.cap, powered, PreprocessingTables.preprocess, old] using! bound

theorem build_count_gap (input : Input)
    (labeling : Fin (build H input.val).vertices → GraphTables.Label) :
    min (2 * gap input) FinalConstants.cap * ((build H input.val).darts : ℝ) ≤
      ((GraphTables.semantics (build H input.val)).rejectionCount labeling : ℝ) := by
  have h := AlphabetTableBounds.gap_transfer_real alphabet_positive (powered H input.val)
    (RoundGap.poweredLower (gap input))
    (RoundGap.poweredLower_nonnegative (gap input) (gap_nonnegative input))
    (powered_count_gap H certificate input) labeling
  have scalar : min (2 * gap input) FinalConstants.cap ≤
      RoundGap.poweredLower (gap input) / 12288 := by
    simpa only [RoundGap.poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap (gap input) (gap_nonnegative input)
  exact (mul_le_mul_of_nonneg_right scalar (Nat.cast_nonneg _)).trans h

theorem step_gap (input : Input) :
    min (2 * gap input) FinalConstants.cap ≤ gap (step H input) := by
  apply ((GraphTables.semantics (step H input).val).le_gap_iff _).mpr
  simp only [step]
  intro labeling
  erw [Fintype.card_fin]
  exact build_count_gap H certificate input labeling

end UniqueGamesTheorem.Foundations.PCP.RoundTableGap

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

instance instFintypeTape : Fintype Tape := MachineRegularOwnerCleanup.tapeFintype

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_TableGapReductionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map admits a polynomial-time machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_satisfiable_iff (F : Formula) :
    Satisfiable (TableIteration.output H F) ↔ F.Satisfiable := by
  constructor
  · intro sat
    by_contra unsat
    have bound := output_gap H certificate F unsat
    rw [(gap_eq_zero_iff (TableIteration.output H F)).mpr sat] at bound
    exact (not_le_of_gt FinalConstants.cap_positive) bound
  · exact TableIteration.output_completeness H F

theorem gapMap_satisfiable_iff (F : Formula) : (gapMap H F).Satisfiable ↔ F.Satisfiable := by
  rw [gapMap, FinalTableFormula.satisfiable_iff, ← output_val]
  exact output_satisfiable_iff H certificate F

end UniqueGamesTheorem.Foundations.PCP.TableGapReduction



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PCPSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PCPSource

open UniqueGamesTheorem.Foundations Target PCP SourceClause
open scoped BigOperators

noncomputable section

theorem normalizedFormula_satisfiable_iff (F : Formula) :
    (normalizedFormula F).Satisfiable ↔ F.Satisfiable := by
  exact (Normalization.normalize_satisfiable_iff (rawFormula F)).trans
    (TableGapReduction.gapMap_satisfiable_iff baseTable baseTable_certificate F)

end
end PerfectCompleteness.PCPSource

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_PreprocessingMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.PCPSourceMachine

open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

theorem rawSource_satisfiable_iff (input : List Bool) :
    (rawSource input).Satisfiable ↔ BinaryLanguage.language input :=
  (PCPSource.normalizedFormula_satisfiable_iff (BinaryLanguage.totalRename input)).trans
    (BinaryLanguage.totalRename_satisfiable_iff input)

end
end PerfectCompleteness.PCPSourceMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalHiddenChild
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalHiddenChild

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

def sourceLaw (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < n + 1, 0 < branch k) :
    FiniteDistribution (Tape calls rows repeats slots) :=
  CompletionSoundness.sigmaLaw (GeometricPath.law (n + 1) hbranch)
    (fun leaf => OriginalChildBlocks.sourceLaw calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots)

def observed (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Tape calls rows repeats slots) : CutChildGrouping.Assembled (C := Fin calls) slots rows :=
  OriginalChildBlocks.observed calls rows repeats ω.1.1
    (GeometricPath.leafPath ω.1.2) slots ω.2

end
end PerfectCompleteness.OriginalHiddenChild

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalWholeCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance 2000] valuesBelowFintype

def belowArraysLaw (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution ((child : Fin (branch m)) → Arrays (childSlots slots child) rows) :=
  FiniteProduct.law (ChildBlockMixture.component
    (fun child => WholeArraySampler.law rows repeats q (childSlots slots child)) chosen)

def valuesLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (OriginalWholeCut.Values rows repeats p slots) :=
  FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p =>
    RecursiveSampler.law F2 repeats (.step chosen q)
      (LeafDomain (OriginalWholeCutTape.cutSlots p slots)))

end
end PerfectCompleteness.OriginalWholeCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalOwnBucketSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalOwnBucketSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays TerminalCalls
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

@[instance_reducible] def valuesChildrenFintype (C : Type*) [Fintype C]
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    Fintype ((C → H slots) × ChildArrays rows slots) :=
  @instFintypeProd (C → H slots) (ChildArrays rows slots) inferInstance inferInstance

attribute [local instance 2000] valuesChildrenFintype

def OtherIndex (rows repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | _, _, .refl _ => Empty
  | n + 1, _, .step i p =>
      (BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
        OtherIndex rows repeats p

instance otherIndexFintype (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (OtherIndex rows repeats p) := by
  induction p with
  | refl m => exact inferInstanceAs (Fintype Empty)
  | @step n m i p ih =>
      letI : Fintype (OtherIndex rows repeats p) := ih
      exact inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
          OtherIndex rows repeats p))

def indexEquiv (rows repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    OriginalCutCalls.Index rows repeats p ≃
      BucketSampler.Direction (rows m) ⊕ OtherIndex rows repeats p
  | _, _, .refl _ => sumEmpty _
  | n + 1, _, .step i p =>
      (Equiv.sumCongr
        (Equiv.refl (BucketSampler.Direction (rows (n + 1)) ×
          TerminalIndex repeats (.step i p)))
        (indexEquiv rows repeats p)).trans (swapFirstSum _ _ _)

@[simp] theorem indexEquiv_ownBucket (rows repeats : Nat → Nat)
    (p : Path branch n m) (a : BucketSampler.Direction (rows m)) :
    indexEquiv rows repeats p (OriginalCutCalls.ownBucket rows repeats p a) = .inl a := by
  revert a
  induction p with
  | refl m => intro a; rfl
  | @step n m i p ih =>
      intro a
      change swapFirstSum _ _ _
        (.inr (indexEquiv rows repeats p (OriginalCutCalls.ownBucket rows repeats p a))) = _
      rw [ih a]
      rfl

@[simp] theorem indexEquiv_symm_inl (rows repeats : Nat → Nat)
    (p : Path branch n m) (a : BucketSampler.Direction (rows m)) :
    (indexEquiv rows repeats p).symm (.inl a) =
      OriginalCutCalls.ownBucket rows repeats p a := by
  apply (indexEquiv rows repeats p).injective
  rw [Equiv.apply_symm_apply, indexEquiv_ownBucket]

def otherCall (rows repeats : Nat → Nat) (p : Path branch n m)
    (call : OtherIndex rows repeats p) : OriginalCutCalls.Index rows repeats p :=
  (indexEquiv rows repeats p).symm (.inr call)

@[simp] theorem indexEquiv_otherCall (rows repeats : Nat → Nat)
    (p : Path branch n m) (call : OtherIndex rows repeats p) :
    indexEquiv rows repeats p (otherCall rows repeats p call) = .inr call :=
  (indexEquiv rows repeats p).apply_symm_apply (.inr call)

def valuesEquiv (rows repeats : Nat → Nat) (p : Path branch n m) (A : Type*) :
    (OriginalCutCalls.Index rows repeats p → A) ≃
      (BucketSampler.Direction (rows m) → A) × (OtherIndex rows repeats p → A) :=
  (Equiv.arrowCongr (indexEquiv rows repeats p) (Equiv.refl A)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem valuesEquiv_own (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (values : OriginalCutCalls.Index rows repeats p → A)
    (a : BucketSampler.Direction (rows m)) :
    (valuesEquiv rows repeats p A values).1 a =
      values (OriginalCutCalls.ownBucket rows repeats p a) := by
  change values ((indexEquiv rows repeats p).symm (.inl a)) = _
  rw [indexEquiv_symm_inl]

@[simp] theorem valuesEquiv_other (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (values : OriginalCutCalls.Index rows repeats p → A)
    (call : OtherIndex rows repeats p) :
    (valuesEquiv rows repeats p A values).2 call =
      values (otherCall rows repeats p call) := rfl

@[simp] theorem valuesEquiv_symm_own (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (own : BucketSampler.Direction (rows m) → A)
    (other : OtherIndex rows repeats p → A) (a : BucketSampler.Direction (rows m)) :
    (valuesEquiv rows repeats p A).symm (own, other)
        (OriginalCutCalls.ownBucket rows repeats p a) = own a := by
  have h := congrArg (fun z => z.1 a)
    ((valuesEquiv rows repeats p A).apply_symm_apply (own, other))
  simpa only [valuesEquiv_own] using h

@[simp] theorem valuesEquiv_symm_other (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (own : BucketSampler.Direction (rows m) → A)
    (other : OtherIndex rows repeats p → A) (call : OtherIndex rows repeats p) :
    (valuesEquiv rows repeats p A).symm (own, other)
        (otherCall rows repeats p call) = other call := by
  have h := congrArg (fun z => z.2 call)
    ((valuesEquiv rows repeats p A).apply_symm_apply (own, other))
  simpa only [valuesEquiv_other] using h

abbrev BucketTape (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots))

abbrev OtherValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OtherIndex rows repeats p → H (cutSlots p slots)

abbrev Complement (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots × (OtherValues rows repeats p slots × BelowArrays rows p slots)

end
end PerfectCompleteness.OriginalOwnBucketSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceChildKernelLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernelRate

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces ProjectedCardinality

variable {branch : Nat → Nat} {height t v m : Nat} [NeZero m]
  {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)

abbrev Record := UniformCleanSoundness.FullRecord
  (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
  (Factors (C := C) (t := t) rows clauses designated)
abbrev CleanChildren (record : Record (C := C) (t := t) rows clauses designated) :=
  UniformCleanSources.CleanIndices (Factors (C := C) (t := t) rows clauses designated) record

end
end PerfectCompleteness.SourceChildKernelRate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildKernelLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernelLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def physicalLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Physical (C := C) (t := t) rows clauses designated i s) :=
  (flag i).mixture (fun b =>
    (FiniteDistribution.uniform (Block C rows (mixedSlots clauses designated i s b))).pushforward
      (fun block => (⟨b, block⟩ : Physical (C := C) (t := t) rows clauses designated i s)))

end
end PerfectCompleteness.SourceChildKernelLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def erase (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → WholeCutSampler.Tape rows repeats p slots →
        Tape rows repeats p slots clean
  | _, _, .refl _, _, _, tape => fun i => tape i.val
  | _, _, .step i p, slots, clean, tape =>
      (fun bucket => CutSamplerReplay.erase F2 repeats (.step i p)
        (LeafDomain slots) clean (tape.1 bucket),
        erase rows repeats p (childSlots slots i) clean tape.2.1, tape.2.2)

def evaluate (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (clean : Fin (branch m) → Prop) → Tape rows repeats p slots clean →
        Domain slots → (node : Nodes branch n) → Block rows node
  | _, m, .refl _, slots, clean, tape, x, .inl _, row =>
      ∑ i : {i : Fin (branch m) // ¬ clean i},
        ((tape i).1 row).val (restrictChild slots i.val x)
  | _, _, .refl _, slots, clean, tape, x, .inr (i, node), row =>
      if hi : ¬ clean i then
        ((tape ⟨i, hi⟩).2 node row).val
          (restrictNode (childSlots slots i) node (restrictChild slots i x))
      else 0
  | n + 1, _, .step i p, slots, clean, tape, x, .inl _, row =>
      ∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
        CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots)
          clean (tape.1 bucket) x
  | _, _, .step i p, slots, clean, tape, x, .inr (j, node), row =>
      if hji : j = i then
        evaluate rows repeats p (childSlots slots i) clean tape.2.1
          (restrictChild slots i x) node row
      else
        ((tape.2.2 ⟨j, hji⟩) node row).val
          (restrictNode (childSlots slots j) node (restrictChild slots j x))

end
end PerfectCompleteness.WholeCutReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutNodeCoordinates
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutNodeCoordinates

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def rowEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (Fin (rows (m + 1)) → H (subtreeSlots p slots)) ≃ₗ[F2]
        (Fin (rows (Nodes.height (upperNode p))) → H (nodeSlots slots (upperNode p)))
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => rowEquiv rows p (childSlots slots i)

end
end PerfectCompleteness.LowerCutNodeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

local instance rowSpaceFintype_r2d0309_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_r2d0309_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype_r2d0309_1 :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
local instance adviceFintype_r2d0309_1 (r : Nat) :
    Fintype (Advice slots upper lowerLevel background r) := by
  letI : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background)) :=
    LeftDecoder.dualFintype
  infer_instance
local instance answerFintype_r2d0309_1 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype (V := squareSpace (LowerH slots upper lowerLevel d))
def decode (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    Option (Answer slots upper lowerLevel d) :=
  let z := HierarchicalLeftDecoder.output slots upper lowerLevel hbranch d q
  if fullRank slots upper lowerLevel d z ≤ s then none else some z

def Valid (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (z : Answer slots upper lowerLevel d) : Prop :=
  z (HierarchicalLeftDecoder.lowerOne slots upper lowerLevel hbranch d) = 1 ∧
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm (LowerH slots upper lowerLevel d)
        (OddListExtraction.multiplicationForm (LowerH slots upper lowerLevel d) z))
      (HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel background d)).rank ≤ 1 ∧
    s < fullRank slots upper lowerLevel d z

end
end PerfectCompleteness.HierarchicalDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalAllDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAllDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAllDecoderTables.rowSpaceFintype
local instance nodeSpaceFintype_r2d0309_2 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAllDecoderTables.upperDualFintype
local instance answerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype
    (V := squareSpace (HierarchicalDecoderTables.LowerH slots upper lowerLevel d))

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (background : Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

def upperTableLaw (r : Nat) (ρ : ℝ) :
    FiniteDistribution (Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper) :=
  FiniteDistribution.table (upperKernel slots upper lowerLevel σ useful r ρ)

def decodeTable (r : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (table : Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper) :
    Input (rows := rows) slots upper lowerLevel r →
      Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  fun input => HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d s (table input)

def RowValid (r : Nat) (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (input : Input (rows := rows) slots upper lowerLevel r)
    (z : HierarchicalDecoderTables.Answer slots upper lowerLevel d) : Prop :=
  HierarchicalDecoderTables.Valid slots upper lowerLevel input.1 hbranch d s z

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputReference

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

instance rawSampleFintype (repeats : Nat → Nat) (cut : Cut upper lower) :
    Fintype (RawSample slots rows upper lower W repeats cut) := by
  change Fintype
    ((HiddenBucketBias.HiddenDirection W → ScalarSample slots upper lower repeats cut) ×
      ((HiddenBucketBias.VisibleDirection W → ScalarSample slots upper lower repeats cut) ×
        Exterior slots rows upper lower))
  infer_instance

def rawLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower)) :
    FiniteDistribution (RawSample slots rows upper lower W repeats cut) :=
  HiddenBucketBias.exposedLaw W
    (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) externalLaw

end
end PerfectCompleteness.OwnInputReference



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutPair

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev NativeMatrix := Module.Dual F2 (H (cutSlots p slots)) →ₗ[F2] (Fin (rows (m + 1)) → F2)

def arraysPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    Arrays slots rows × Arrays slots rows :=
  (first rows repeats p slots exterior raw, second rows repeats p slots exterior a raw)

def selectedPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    NativeRows rows p slots × NativeRows rows p slots :=
  (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw),
    SelectedArrayReplacement.selectedRows rows p slots (second rows repeats p slots exterior a raw))

def matrixPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    NativeMatrix rows p slots × NativeMatrix rows p slots :=
  let z := selectedPair rows repeats p slots exterior a raw
  (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.1,
    EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2)

end
end PerfectCompleteness.LowerCutPair

end

section

namespace PerfectCompleteness.LowerCutDecoderForm

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping

variable {branch rows repeats : Nat → Nat} {n height t : Nat}
  (path : Path branch n (height + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

variable (hbranch : ∀ k < n, 0 < branch k) {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (table : HierarchicalAllDecoderTables.Input (rows := rows)
    slots upper lowerLevel adviceRows → HierarchicalAllDecoderTables.UpperAnswer slots upper)
  (cutoff : Nat)

def answer (arrays : Arrays slots rows) :
    Option (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d cutoff
    (table (LowerCutDecoderInput.actualInput slots upper lowerLevel arrays A))

def readForm (arrays : Arrays slots rows) :
    Option (ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots)) :=
  (answer slots upper lowerLevel d hbranch A table cutoff arrays).map
    (form path slots upper lowerLevel d hnode)

def first (exterior : Exterior rows repeats path slots)
    (raw : LowerCutPair.Raw rows repeats path slots) :
    Option (ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots)) :=
  readForm path slots upper lowerLevel d hnode hbranch A table cutoff
    (LowerCutPair.first rows repeats path slots exterior raw)

def second (exterior : Exterior rows repeats path slots)
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : LowerCutPair.Raw rows repeats path slots) :
    Option (ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots)) :=
  readForm path slots upper lowerLevel d hnode hbranch A table cutoff
    (LowerCutPair.second rows repeats path slots exterior direction raw)

end
end PerfectCompleteness.LowerCutDecoderForm

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayGroupingTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayGroupingTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

export CutSamplerReplayGroupingTransport (outside_kept outside_eq retainedChildSlots_eq)

def castChildren (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean) :
    WholeCutReplayGrouping.RetainedChildren rows repeats p target clean :=
  fun child => cast
    (congrArg (ChildBlock (WholeCutCalls.Index rows repeats p) rows)
      (retainedChildSlots_eq p slots target clean hs child)) (children child)

end
end PerfectCompleteness.WholeCutReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildKernelMarginalLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildNativeLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def leftLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Native (C := C) (t := t) rows clauses designated i s) :=
  (flag i).mixture (fun b => if b then
    (FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s)).pushforward
      (pullback rows clauses designated i s true)
    else FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s))

end
end PerfectCompleteness.SourceChildNativeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildQuestionLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildQuestionLaw

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays SourceQuestionReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t v : Nat}

def sourceLaw (m t : Nat) [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    FiniteDistribution (SourceChildKernel.Sources (m := m) (t := t) designated) :=
  FiniteProduct.law (fun i => (SourceOddLists.tupleLaw m t).product
    (FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
      SourceOddLists.tupleLaw m t)))

end
end PerfectCompleteness.SourceChildQuestionLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildMarkedLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildMarkedLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays SourceChildKernel
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def projectedLaw (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    FiniteDistribution (Native (C := C) (t := t) rows clauses designated i s) :=
  (FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s)).pushforward
    (SourceChildNativeLaw.pullback rows clauses designated i s true)

def markedChild (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Bool × Native (C := C) (t := t) rows clauses designated i s :=
  (rawProjected rows clauses designated i raw,
    SourceChildNativeLaw.decodeLeft rows clauses designated i s raw)

def projectedSlots (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  mixedSlots clauses designated i (childSource designated q i z) true

def questionProjection
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    ∀ leaf k, MixedSupport.Projection (childSlots (questionSlots clauses q) i leaf k)
      (projectedSlots clauses designated q i z leaf k) :=
  cast (congrArg
    (fun slots : Slots branch n → Fin t → MixedSupport.Slot =>
      ∀ leaf k, MixedSupport.Projection (slots leaf k)
        (projectedSlots clauses designated q i z leaf k))
    (nativeSlots_childSource clauses designated q i z))
      (projection clauses designated i (childSource designated q i z) true)

def replacementAt (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    FiniteDistribution (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) :=
  (projectedLaw (C := C) (t := t) rows clauses designated i (childSource designated q i z)).pushforward
    (nativeEquiv rows clauses designated q i z)

def replacementLaws (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) :
    FiniteDistribution (CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i) :=
  (FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))).mixture
    (replacementAt rows clauses designated q i)

end
end PerfectCompleteness.SourceChildMarkedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutScalarProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutScalarProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def nodeEquiv (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {a b : Nodes branch n} (hab : a = b) :
    H (nodeSlots slots a) ≃ₗ[F2] H (nodeSlots slots b) := by
  rw [hab]

end
end PerfectCompleteness.LowerCutScalarProjection

end

section

namespace PerfectCompleteness.SourceQuestionLowerForms

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section Casts

variable {branch : Nat → Nat} {height t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat)
  {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}

def rawCast (h : source = target) :
    CutChildGrouping.Raw (C := C) source rows ≃ CutChildGrouping.Raw (C := C) target rows := by
  cases h
  exact Equiv.refl _

end Casts

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)

abbrev Questions := SourceChildMarkedLaw.Questions
  (branch := branch) (n := height) (t := t) (m := m)
abbrev Calls := Option (WholeCutCalls.Index rows repeats path)

def slots (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill path outside (SourceChildMarkedLaw.questionSlots clauses q)

abbrev Raw (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :=
  CutChildGrouping.Raw (C := Calls (rows := rows) (repeats := repeats) path)
    (SourceChildMarkedLaw.questionSlots clauses q) rows

abbrev Form (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :=
  ChildBilinearCollisionTransfer.ParentForm (SourceChildMarkedLaw.questionSlots clauses q)

theorem cutSlots_eq (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    WholeCutGrouping.cutSlots path (slots path outside clauses q) =
      SourceChildMarkedLaw.questionSlots clauses q :=
  CleanPhysicalReplay.cutSlots_fill path outside _

def rawAtCut (q : Questions (branch := branch) (height := height) (t := t) (m := m))
    (raw : Raw (rows := rows) (repeats := repeats) path clauses q) :
    LowerCutPair.Raw rows repeats path (slots path outside clauses q) :=
  rawCast rows (cutSlots_eq path outside clauses q).symm raw

variable (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)

abbrev UpperTable (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :=
  HierarchicalAllDecoderTables.Input (rows := rows)
    (slots path outside clauses q) upper level adviceRows →
      HierarchicalAllDecoderTables.UpperAnswer (slots path outside clauses q) upper

variable (tables : (q : Questions (branch := branch) (height := height) (t := t) (m := m)) →
  UpperTable (rows := rows) path outside clauses upper level (adviceRows := adviceRows) q)
  (cutoff : Nat)

def first (q : Questions (branch := branch) (height := height) (t := t) (m := m))
    (raw : Raw (rows := rows) (repeats := repeats) path clauses q) : Option (Form clauses q) :=
  (LowerCutDecoderForm.first path (slots path outside clauses q) upper level d hnode hbranch A
    (tables q) cutoff
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
      (SourceChildMarkedLaw.questionSlots clauses q) exterior)
    (rawAtCut path outside clauses q raw)).map
      (CutNativeForms.formCast (cutSlots_eq path outside clauses q))

def second (direction : BucketSampler.Direction (rows (height + 1)))
    (q : Questions (branch := branch) (height := height) (t := t) (m := m))
    (raw : Raw (rows := rows) (repeats := repeats) path clauses q) : Option (Form clauses q) :=
  (LowerCutDecoderForm.second path (slots path outside clauses q) upper level d hnode hbranch A
    (tables q) cutoff
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
      (SourceChildMarkedLaw.questionSlots clauses q) exterior)
    direction (rawAtCut path outside clauses q raw)).map
      (CutNativeForms.formCast (cutSlots_eq path outside clauses q))

end
end PerfectCompleteness.SourceQuestionLowerForms

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_WholeArrayInteriorOwnInputLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayInteriorOwnInputLaw

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {N t : Nat}

def ownInput (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper)) (a : Block rows lower)
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputReference.Input slots rows upper lower W a :=
  OwnInputReference.readInput slots rows upper lower W a
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
    (exposedRead rows repeats slots upper lower cut W ω).2

end
end PerfectCompleteness.WholeArrayInteriorOwnInputLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutBucketLocality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutBucketLocality

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping WholeArraySubtreeSplit

variable {branch : Nat → Nat} {n k m t : Nat}

def rootBuckets (rows repeats : Nat → Nat) :
    {k m : Nat} → (pDown : Path branch k (m + 1)) → m + 1 < k →
      (slots : Slots branch k → Fin t → MixedSupport.Slot) →
      Exterior rows repeats pDown slots →
      LowerCutCallSplit.Assembled rows repeats pDown slots →
        BucketSampler.Direction (rows k) → H slots
  | _, _, .refl _, hproper, _, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step i pDown, _, slots, exterior, assembled, direction =>
      LowerCutScalar.reconstruct F2 repeats (.step i pDown) (LeafDomain slots)
        (fun terminal => assembled.1 (.inl (direction, terminal))) (exterior.1 direction)

def buckets (rows repeats : Nat → Nat) :
    {n k m : Nat} → (pUp : Path branch n k) → (pDown : Path branch k (m + 1)) →
      m + 1 < k → (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      Exterior rows repeats (pUp.append pDown) slots →
      LowerCutCallSplit.Assembled rows repeats (pUp.append pDown) slots →
        BucketSampler.Direction (rows k) → H (subtreeSlots pUp slots)
  | _, _, _, .refl _, pDown, hproper, slots, exterior, assembled =>
      rootBuckets rows repeats pDown hproper slots exterior assembled
  | _, _, _, .step i pUp, pDown, hproper, slots, exterior, assembled =>
      buckets rows repeats pUp pDown hproper (childSlots slots i) exterior.2.1
        (fun call => assembled.1 (.inr call), assembled.2)

def knownBuckets (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (assembled : LowerCutCallSplit.Assembled rows repeats ((Nodes.path upper).append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  fun v => buckets rows repeats (Nodes.path upper) pDown hproper slots exterior assembled v.val

def knownBucketsOfComplement (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (hproper : m + 1 < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (exterior : Exterior rows repeats ((Nodes.path upper).append pDown) slots)
    (complement : LowerCutCallSplit.Complement rows repeats ((Nodes.path upper).append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  knownBuckets rows repeats slots upper pDown hproper W exterior
    (LowerCutCallSplit.merge rows repeats ((Nodes.path upper).append pDown) slots complement 0)

end
end PerfectCompleteness.LowerCutBucketLocality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutPairBackground

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev NativeMatrix := LowerCutPair.NativeMatrix rows p slots

def rowPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    Complement rows repeats p slots × (NativeRows rows p slots × NativeRows rows p slots) :=
  ((observe rows repeats p slots raw).1,
    LowerCutPair.selectedPair rows repeats p slots exterior a raw)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

def matrixPair (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    Complement rows repeats p slots × (NativeMatrix rows p slots × NativeMatrix rows p slots) :=
  ((observe rows repeats p slots raw).1,
    LowerCutPair.matrixPair rows repeats p slots exterior a raw)

def backgroundArrays (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) : Arrays slots rows :=
  LowerCutAssembled.reconstruct rows repeats p slots exterior
    (LowerCutCallSplit.merge rows repeats p slots c 0)

def installRows (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (S : NativeRows rows p slots) : Arrays slots rows :=
  SelectedArrayReplacement.replace rows p slots
    (backgroundArrays rows repeats p slots exterior c) S

def installMatrix (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots) : Arrays slots rows :=
  installRows rows repeats p slots exterior c (EvaluationMatrix.rows (H (cutSlots p slots)) X)

end
end PerfectCompleteness.LowerCutPairBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutFiberDisintegrationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutFiberDisintegration

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (a : BucketSampler.Direction (rows (m + 1)))

def coordinates (raw : LowerCutPair.Raw rows repeats path slots) :
    Coordinates rows repeats path slots a :=
  coordinateEquiv rows repeats path slots a
    (LowerCutPairBackground.observe rows repeats path slots raw)

def law : FiniteDistribution (Coordinates rows repeats path slots a) :=
  ((FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats path slots)).product
    (FiniteDistribution.uniform (Quotient rows path slots a))).product
      ((FiniteDistribution.uniform (Scalar path slots)).product
        (FiniteDistribution.uniform (Scalar path slots)))

def arraysAt (exterior : Exterior rows repeats path slots)
    (background : Background rows repeats path slots a) (fresh : Scalar path slots) :
    Arrays slots rows :=
  LowerCutPairBackground.installRows rows repeats path slots exterior background.1
    (LowerDirectionFiber.restore a background.2 fresh)

def pair (exterior : Exterior rows repeats path slots)
    (z : Coordinates rows repeats path slots a) : Arrays slots rows × Arrays slots rows :=
  (arraysAt rows repeats path slots a exterior z.1 z.2.1,
    arraysAt rows repeats path slots a exterior z.1 z.2.2)

end
end PerfectCompleteness.LowerCutFiberDisintegration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedLowerFiber
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedLowerFiber

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

def arraysAt (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    Arrays projected rows :=
  Function.update arrays (lower upper level d)
    (LowerDirectionFiber.replace a (arrays (lower upper level d)) fresh)

def originalArraysAt (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    Arrays slots rows :=
  ChildBlockProjection.arraysPullback rows projection
    (arraysAt projected upper level d a arrays fresh)

def inputAt {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    HierarchicalAllDecoderTables.Input (rows := rows) slots upper level r :=
  LowerCutDecoderInput.actualInput slots upper level
    (originalArraysAt slots projected projection upper level d a arrays fresh) A

abbrev UpperTable (r : Nat) :=
  HierarchicalAllDecoderTables.Input (rows := rows) slots upper level r →
    HierarchicalAllDecoderTables.UpperAnswer slots upper

def upperAt {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)
    (table : UpperTable (rows := rows) slots upper level r)
    (fresh : Scalar projected upper level d) :
    HierarchicalAllDecoderTables.UpperAnswer slots upper :=
  table (inputAt slots projected projection upper level d A a arrays fresh)

end
end PerfectCompleteness.ProjectedLowerFiber

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedFiberSquare
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberSquare

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open ProjectedLowerFiber

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

local instance rowSpaceFintype_r2d0309_2 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r2d0309_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def form (s : Nat) (q : HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  (HierarchicalDecoderTables.decode slots upper level hbranch d s q).map
    (OddListExtraction.multiplicationForm
      (HierarchicalDecoderTables.LowerH slots upper level d))

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)

def restrictedPair (s : Nat) (table : UpperTable (rows := rows) slots upper level r)
    (pair : Scalar projected upper level d × Scalar projected upper level d) : Bool :=
  BilinearCollisionTransfer.restrictedCollision
    (form slots upper level hbranch d s
      (upperAt slots projected projection upper level d A a arrays table pair.1))
    (form slots upper level hbranch d s
      (upperAt slots projected projection upper level d A a arrays table pair.2))
    (LinearMap.range (HPullback
      (ChildBlockProjection.nodeProjection projection (lower upper level d))))

variable
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def rightLaw :=
  RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
    repeats cut σ
    (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
      (LinearMap.ker A) a.val known arrays) threshold

def seedLaw :=
  (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).product
    (rightLaw projected upper level d A a arrays known repeats cut σ threshold)

def success (s : Nat) (ν : FiniteDistribution (Scalar projected upper level d)) : ℝ :=
  ν.expectation (fun fresh =>
    ((HierarchicalAllDecoderTables.upperKernel slots upper level σ useful r ρ
      (inputAt slots projected projection upper level d A a arrays fresh)).product
      (RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
        repeats cut σ
        (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
          (LinearMap.ker A) a.val known (arraysAt projected upper level d a arrays fresh))
        threshold)).probability
      (fun pair => highMeeting slots projected projection upper level hbranch d s pair.1 pair.2))

end
end PerfectCompleteness.ProjectedFiberSquare

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerProjectedFiberAverage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerProjectedFiberAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (path : Path branch n (m + 1))
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats path projected)

local instance rowSpaceFintype_r2d0309_3 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r2d0309_2 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
abbrev Background := LowerCutFiberDisintegration.Background rows repeats path projected a

def backgroundLaw : FiniteDistribution (Background (repeats := repeats) path projected a) :=
  (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats path projected)).product
    (FiniteDistribution.uniform (LowerCutFiberDisintegration.Quotient rows path projected a))

def baseline (bg : Background (repeats := repeats) path projected a) : Arrays projected rows :=
  LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior bg 0

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)

def readForm (s : Nat) (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
    (arrays : Arrays projected rows) :=
  (LowerCutDecoderForm.answer slots upper level d hbranch A table s
    (ChildBlockProjection.arraysPullback rows projection arrays)).map
    (OddListExtraction.multiplicationForm
      (HierarchicalDecoderTables.LowerH slots upper level d))

def collision (s : Nat) (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
    (pair : Arrays projected rows × Arrays projected rows) : Bool :=
  BilinearCollisionTransfer.restrictedCollision
    (readForm slots projected projection upper level hbranch d A s table pair.1)
    (readForm slots projected projection upper level hbranch d A s table pair.2)
    (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection projection
      (HierarchicalLeftDecoder.LowerNode upper level d))))

def rawCollision (s : Nat)
    (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r) : ℝ :=
  (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats path))
    (cutSlots path projected) rows).probability
      (fun raw => collision slots projected projection upper level hbranch d A s table
        (LowerCutPair.arraysPair rows repeats path projected exterior a raw))

variable
  (known : Background path projected a → HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def meanSuccess (s : Nat) : ℝ :=
  (backgroundLaw path projected a).expectation (fun bg =>
    ProjectedFiberSquare.success slots projected projection upper level hbranch d A
      (ProjectedFiberRawPair.direction path upper level d hnode a)
      (baseline path projected a exterior bg) (known bg) repeats cut σ useful ρ threshold s
      (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)))

end
end PerfectCompleteness.LowerProjectedFiberAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerProjectedOriginalSuccessLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerProjectedOriginalSuccess

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (path : Path branch n (m + 1))
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats path projected)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

variable
  (known : LowerProjectedFiberAverage.Background path projected a →
    HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)

local instance rowSpaceFintype_r2d0309_4 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r2d0309_3 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def rawSuccess (s : Nat) : ℝ :=
  (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
    (cutSlots path projected) rows).expectation (fun raw =>
      kernelSuccess (repeats := repeats) path slots projected projection upper level hbranch d hnode a A cut σ useful
        ρ threshold s
        (known (LowerCutSingleFiberDisintegration.coordinates rows repeats path projected a raw).1)
        (LowerCutRows.reconstruct rows repeats path projected exterior raw))

end
end PerfectCompleteness.LowerProjectedOriginalSuccess

end

section

namespace PerfectCompleteness.LowerPhysicalFiberSuccess

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n)
  (pDown : Path branch (Nodes.height upper) (m + 1))
  (hproper : m + 1 < Nodes.height upper)
  (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

abbrev path := (Nodes.path upper).append pDown

variable
  (hnode : WholeArrayInteriorExterior.upperNode (path upper pDown) =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats (path upper pDown) projected)

local instance rowSpaceFintype_r2d0309_5 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r2d0309_4 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
abbrev Raw := CutChildGrouping.Raw (C := LowerCutPair.Calls rows repeats (path upper pDown))
  (cutSlots (path upper pDown) projected) rows

def tape (raw : Raw (rows := rows) (repeats := repeats) projected upper pDown) :
    WholeCutSampler.Tape rows repeats (path upper pDown) projected :=
  (splitTape rows repeats (path upper pDown) projected).symm (exterior, raw)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)

def knownRaw (raw : Raw (rows := rows) (repeats := repeats) projected upper pDown) :
    HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper :=
  WholeCutSubtree.knownBucketsAtNode rows repeats projected upper pDown hproper (LinearMap.ker A)
    (tape projected upper pDown exterior raw)

def knownBackground
    (bg : LowerProjectedFiberAverage.Background (repeats := repeats) (path upper pDown) projected a) :
    HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper :=
  LowerCutBucketLocality.knownBucketsOfComplement rows repeats projected upper pDown hproper
    (LinearMap.ker A) exterior bg.1

variable
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def physicalSuccess (s : Nat) : ℝ :=
  (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats (path upper pDown))
    (cutSlots (path upper pDown) projected) rows).expectation (fun raw =>
      LowerProjectedOriginalSuccess.kernelSuccess (repeats := repeats) (path upper pDown) slots projected projection upper level
        hbranch d hnode a A cut σ useful ρ threshold s
        (knownRaw projected upper pDown hproper exterior A raw)
        (WholeCutSampler.evaluate rows repeats (path upper pDown) projected
          (tape projected upper pDown exterior raw)))

end
end PerfectCompleteness.LowerPhysicalFiberSuccess

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedTag
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedTag

noncomputable section

open scoped Classical
open RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m v : Nat}

def positionLaw : FiniteDistribution
    (SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) :=
  FiniteProduct.law (fun _ : Fin (branch n) =>
    FiniteDistribution.uniform
      (SourceQuestionPositionSplit.ChildPositions (branch := branch) (n := n) (t := t)))

def law (flag : Fin (branch n) → FiniteDistribution Bool) :
    FiniteDistribution (Tag (branch := branch) (n := n) (t := t)) :=
  (positionLaw (branch := branch) (n := n) (t := t)).product (flagLaw flag)

end
end PerfectCompleteness.SourceProjectedTag

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPhysicalHigh
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPhysicalHigh

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple
    (branch := branch) (n := height) (t := t))
  (flags : SourceProjectedTag.Flags (branch := branch) (n := height))

abbrev originalSlots := SourceQuestionLowerForms.slots path outside clauses q

def projectedSlots : Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill path outside
    (SourceProjectedTag.mixedInside clauses designated q choices flags)

def projection : ∀ leaf j, MixedSupport.Projection
    (originalSlots path outside clauses q leaf j)
    (projectedSlots path outside clauses designated q choices flags leaf j) :=
  CutProjectionAssembly.fillProjection path outside
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceProjectedTag.mixedInside clauses designated q choices flags)
    (SourceProjectedTag.projection clauses designated q choices flags)

def exteriorAt
    (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder) :
    WholeCutGrouping.Exterior rows repeats path
      (projectedSlots path outside clauses designated q choices flags) :=
  CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
    (SourceProjectedTag.mixedInside clauses designated q choices flags) exterior

section Collision

variable (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)
  (table : SourceQuestionLowerForms.UpperTable (rows := rows)
    path outside clauses upper level (adviceRows := adviceRows) q)

def collision : ℝ :=
  LowerProjectedFiberAverage.rawCollision path
    (originalSlots path outside clauses q)
    (projectedSlots path outside clauses designated q choices flags)
    (projection path outside clauses designated q choices flags)
    upper level hbranch d direction
    (exteriorAt path outside placeholder clauses designated q choices flags exterior)
    A cutoff table

end Collision

section Success

variable (upper : Nodes branch n)
  (pDown : Path branch (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper level d)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows)
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper level bg → Prop)
  (ρ threshold : ℝ)
  (exterior : CleanPhysicalReplay.Exterior rows repeats
    ((Nodes.path upper).append pDown) outside placeholder)
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)

local instance rowSpaceFintype_r2d0309_6 :
    Fintype (NodeEmbedding.RowSpace
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r2d0309_5 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace
    (originalSlots ((Nodes.path upper).append pDown) outside clauses q) upper)
def success : ℝ :=
  LowerPhysicalFiberSuccess.physicalSuccess
    (originalSlots ((Nodes.path upper).append pDown) outside clauses q)
    (projectedSlots ((Nodes.path upper).append pDown) outside clauses designated q choices flags)
    (projection ((Nodes.path upper).append pDown) outside clauses designated q choices flags)
    upper pDown hproper level hbranch d hnode direction
    (exteriorAt ((Nodes.path upper).append pDown) outside placeholder clauses designated
      q choices flags exterior) A cut σ useful ρ threshold cutoff

end Success
end
end PerfectCompleteness.SourceQuestionPhysicalHigh

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutGroupedProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalScalarProjection

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def terminalPullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (values : OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain right)) :
    OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain left) :=
  fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call)

end
end PerfectCompleteness.OriginalScalarProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPairPullback
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPairPullback

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior

variable {branch : Nat → Nat} {n height t : Nat}

def rawAtCut (rows repeats : Nat → Nat) (path : Path branch n (height + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (inside : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) inside rows) :
    LowerCutPair.Raw rows repeats path (CutSlotAssembly.fill path outside inside) :=
  SourceQuestionLowerForms.rawCast rows
    (CleanPhysicalReplay.cutSlots_fill path outside inside).symm raw

end
end PerfectCompleteness.SourceQuestionPairPullback

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionRawSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionRawSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h n t v m : Nat}

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def insideQuestions
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    PreliminarySampler.Questions branch (n + 1) t m :=
  (SourceQuestionKernelJoint.groupEquiv rows clauses designated sample).1.1

def positions
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) :=
  (SourceQuestionKernelJoint.groupEquiv rows clauses designated sample).1.2

def kernelLaw (flag : Fin (branch n) → FiniteDistribution Bool)
    (inside : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) :
    FiniteDistribution (SourceChildKernelJoint.RawTuple (C := C) (t := t)
      rows clauses designated) :=
  FiniteProduct.law (fun child =>
    SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag child
      (SourceQuestionKernelJoint.sources designated inside choices child))

end
end PerfectCompleteness.SourceQuestionRawSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionUnmarkedRange
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionUnmarkedRange

open scoped Classical
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {height t v m : Nat}

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceChildMarkedLaw.Questions (branch := branch) (n := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := height) (t := t))

theorem leftSlots_eq :
    parentLeftSlots clauses designated (SourceQuestionKernelJoint.sources designated q choices) =
      SourceChildMarkedLaw.questionSlots clauses q :=
  SourceQuestionPositionSplit.parentLeftSlots_join clauses designated q _

variable {C : Type*} [Fintype C]
  (raw : (i : Fin (branch height)) → Raw (C := C) (t := t) rows clauses designated i)

def projection : ∀ s k, MixedSupport.Projection
    (SourceChildMarkedLaw.questionSlots clauses q s k)
    (parentRightSlots rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw s k) :=
  CutNativeForms.projectionCast (leftSlots_eq clauses designated q choices) rfl
    (parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)

end
end PerfectCompleteness.SourceQuestionUnmarkedRange

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputAffineSlice

noncomputable section

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))

def visibleLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower)) :
    FiniteDistribution (VisibleSample slots rows upper lower W repeats cut) :=
  (HiddenBucketBias.visibleTapeLaw W
    (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))).product
      externalLaw

def hiddenOutput (repeats : Nat → Nat) (cut : Cut upper lower)
    (sample : RawSample slots rows upper lower W repeats cut) :
    W ⊗[F2] UpperSpace slots upper :=
  HiddenBucketBias.hiddenSum W
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) sample.1

def jointEvent (repeats : Nat → Nat) (cut : Cut upper lower)
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (sample : RawSample slots rows upper lower W repeats cut) : Bool :=
  tensorSlice W Q target (hiddenOutput slots rows upper lower W repeats cut sample) &&
    visible sample.2

theorem slice_probability_pos (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target)) :
    0 < (referenceLaw slots rows upper lower W repeats cut).probability (tensorSlice W Q target) := by
  exact product_slice_positive
    (HiddenBucketBias.hiddenTapeLaw W
      (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (visibleLaw slots rows upper lower W repeats cut externalLaw)
    (HiddenBucketBias.hiddenSum W
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (tensorSlice W Q target) visible positive

end
end PerfectCompleteness.OwnInputAffineSlice


namespace PerfectCompleteness.OwnInputRawAssembly

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open OwnInputReference (RawSample ScalarSample UpperSpace UpperVector Cut)

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (UpperVector rows upper))
  (repeats : Nat → Nat) (cut : Cut upper lower)

def mergedTape (sample : RawSample slots rows upper lower W repeats cut) :
    BucketSampler.Tape (rows (Nodes.height upper)) (ScalarSample slots upper lower repeats cut) :=
  (HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)).symm
    (sample.1, sample.2.1)

def arrays (sample : RawSample slots rows upper lower W repeats cut) : Arrays slots rows :=
  OwnInputCanonicalQuery.assemble slots rows upper lower
    (BucketSampler.evaluate (rows (Nodes.height upper)) (scalarEval slots upper lower repeats cut)
      (mergedTape slots rows upper lower W repeats cut sample)) sample.2.2

def background (visible : OwnInputAffineSlice.VisibleSample slots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.Background (rows := rows) slots upper :=
  exteriorBackground slots rows upper lower visible.2

end
end PerfectCompleteness.OwnInputRawAssembly

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedSlice

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projectedSlots upper)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedSlice.rowSpaceFintype
local instance valueFintype_r2d0309_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
abbrev matrix (T : HiddenTensor projectedSlots upper A) :=
  TensorProjectedSlice.totalMatrix (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (visibleMatrix originalSlots projectedSlots projection upper A known) T

abbrev quotientMatrix (T : HiddenTensor projectedSlots upper A) :=
  MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (matrix originalSlots projectedSlots projection upper A known T)

abbrev VisibleGood : Prop :=
  ManyGoodRows.GoodRow (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
      (visibleMatrix originalSlots projectedSlots projection upper A known)))

def witness
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :=
  TensorSelectedSlice.witness
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

def columnSpace
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Submodule F2 (Module.Dual F2 (NodeEmbedding.NodeH projectedSlots upper)) :=
  TensorSelectedSlice.columnSpace (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

def J (T : HiddenTensor projectedSlots upper A) : Bool :=
  GoodAdviceEvents.J (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ (A, quotientMatrix originalSlots projectedSlots projection upper lowerLevel background A known T)

def target
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true) :
    columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood →ₗ[F2]
      LinearMap.ker A :=
  TensorSelectedSlice.target (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) le_rfl hgood hne

def nativeCorrection
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Module.Dual F2 (NodeEmbedding.NodeH projectedSlots upper) :=
  (correction originalSlots upper lowerLevel background
    (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value).comp
      (ProjectedNodeEmbedding.intoOriginal projection upper)

def visibleOffset
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Block rows upper :=
  visibleMatrix originalSlots projectedSlots projection upper A known
      (correction originalSlots upper lowerLevel background
        (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) +
    (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value.1

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.ProjectedRawAssembly

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (originalSlots s k) (projectedSlots s k))
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (Block rows upper))
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

def arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    Arrays originalSlots rows :=
  ChildBlockProjection.arraysPullback rows projection
    (OwnInputRawAssembly.arrays projectedSlots rows upper lower W repeats cut sample)

def visibleMatrix
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut) :
    Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper) →ₗ[F2] Block rows upper :=
  HierarchicalTensorMatrix.visibleMatrix originalSlots upper W
    (fun v => ProjectedNodeEmbedding.nativePullback projection upper
      (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v))

end
end PerfectCompleteness.ProjectedRawAssembly


namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rowSpaceFintype
local instance valueFintype_r2d0309_2 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
abbrev Raw := OwnInputReference.RawSample projectedSlots rows upper lower (LinearMap.ker A) repeats cut

abbrev rawArrays (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  ProjectedRawAssembly.arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample

abbrev rawBackground (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  HierarchicalMatrixTable.backgroundOf originalSlots upper
    (rawArrays originalSlots projectedSlots projection rows upper lower A repeats cut sample)

abbrev rawMatrix (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  NodeEmbedding.matrix (rawArrays originalSlots projectedSlots projection rows upper lower A repeats cut sample) upper

abbrev hidden (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower (LinearMap.ker A) repeats cut sample

def rawJ (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  GoodAdviceEvents.J
    (HierarchicalUsefulness.table originalSlots upper lowerLevel original originalArrays lowerEvent κ σ
      (rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample)) r ρ
    (A, HierarchicalPrediction.quotientMatrix originalSlots upper lowerLevel
      (rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample)
      (rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample))

def rawPrediction (a : Block rows lower)
    (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  HierarchicalPrediction.prediction originalSlots upper lowerLevel
    (rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample) σ lower cut.upper_ne_lower a
    original originalArrays lowerEvent κ r ρ A (rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample)

abbrev VisibleGood (v : Visible projectedSlots rows upper lower A repeats cut) : Prop :=
  HierarchicalProjectedSlice.VisibleGood originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)

abbrev tensorJ (v : Visible projectedSlots rows upper lower A repeats cut)
    (T : HierarchicalProjectedSlice.HiddenTensor projectedSlots upper A) : Bool :=
  HierarchicalProjectedSlice.J originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) T

abbrev columnSpace (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalProjectedSlice.columnSpace originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood

abbrev target (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true) :=
  HierarchicalProjectedSlice.target originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood hne

abbrev nativeCorrection (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalProjectedSlice.nativeCorrection originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood

abbrev visibleOffset (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalProjectedSlice.visibleOffset originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood

def responseMatch (a : Block rows lower) (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  decide (OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a σ
      (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
      (hidden projectedSlots rows upper lower A repeats cut sample) =
    visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v hgood +
      TensorBucketEvaluation.tensorOutputLinear (LinearMap.ker A)
        (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) (hidden projectedSlots rows upper lower A repeats cut sample))

def given (v : Visible projectedSlots rows upper lower A repeats cut)
    (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
    A repeats cut sample && decide (sample.2 = v)

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_HierarchicalFixedAdviceFamilyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.PreliminaryStrategy

open PreliminarySampler TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

def extend (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (strategy : Strategy clauses branch n t rows repeats) :
    KeyStrategy.Strategy (TreeCanonical.locationCount branch n t) :=
  CanonicalGameStrategy.extend
    (HierarchicalGame.toBlockFamily (family clauses branch n t rows repeats)) strategy

end
end PerfectCompleteness.PreliminaryStrategy

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryLevelPair
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PreliminaryLevelPair

open PreliminarySampler PreliminaryStrategy CandidateCoupling
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

def win (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : Strategy clauses branch n t rows repeats)
    (level : Fin n) (e : Shared clauses branch n t rows) : Bool :=
  observe clauses (extend clauses branch n t rows repeats strategy)
    e.1 e.2.1 ⟨level, e.2.2 level⟩

end
end PerfectCompleteness.PreliminaryLevelPair

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedExperimentLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows repeats : Nat → Nat} {n t : Nat} {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (lower : K → Nodes branch n)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block rows (lower k))

abbrev Sample := (k : K) × WholeArraySampler.Tape rows repeats
  (WholeArrayInteriorOwnInputLaw.fullPath upper (lower k) (cut k)) (projected k)

def originalLaw (outer : FiniteDistribution K) :
    FiniteDistribution (Sample (rows := rows) (repeats := repeats) projected upper lower cut) :=
  CompletionSoundness.sigmaLaw outer (fun k => WholeArraySampler.tapeLaw rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper (lower k) (cut k)) (projected k))

def arrays (x : Sample (rows := rows) (repeats := repeats) projected upper lower cut) :
    Arrays slots rows :=
  ChildBlockProjection.arraysPullback rows (projection x.1)
    (WholeArraySampler.evaluate rows repeats
      (WholeArrayInteriorOwnInputLaw.fullPath upper (lower x.1) (cut x.1)) (projected x.1) x.2)

def experiment (outer : FiniteDistribution K)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceExperiment.Experiment branch rows n t
      (Sample (rows := rows) (repeats := repeats) projected upper lower cut) where
  slots := slots
  upper := upper
  lowerLevel := lowerLevel
  arrays := arrays slots projected projection upper lower cut
  lowerNode x := lower x.1
  separate x := (cut x.1).upper_ne_lower
  direction x := direction x.1
  original := originalLaw projected upper lower cut outer
  strategy := σ

abbrev RawSample (r : Nat) :=
  (A : Advice (rows := rows) upper r) × (k : K) ×
    OwnInputReference.RawSample (projected k) rows upper (lower k) (LinearMap.ker A) repeats (cut k)

def rawLaw (outer : FiniteDistribution K) (r : Nat) :
    FiniteDistribution (RawSample (rows := rows) (repeats := repeats) projected upper lower cut r) :=
  CompletionSoundness.sigmaLaw (FiniteDistribution.uniform (Advice (rows := rows) upper r))
    (fun A => CompletionSoundness.sigmaLaw outer (fun k =>
      OwnInputReference.rawLaw (projected k) rows upper (lower k) (LinearMap.ker A) repeats (cut k)
        (WholeArrayInteriorOwnInputLaw.exteriorLaw rows repeats (projected k) upper (lower k) (cut k))))

def rawRead (r : Nat)
    (x : Sample (rows := rows) (repeats := repeats) projected upper lower cut ×
      Advice (rows := rows) upper r) :
    RawSample (rows := rows) (repeats := repeats) projected upper lower cut r :=
  ⟨x.2, x.1.1, WholeArrayInteriorOwnInputLaw.exposedRead rows repeats (projected x.1.1) upper
    (lower x.1.1) (cut x.1.1) (LinearMap.ker x.2) x.1.2⟩

end
end PerfectCompleteness.HierarchicalProjectedExperiment


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourcePhysicalWholeLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalWholeLaw

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Raw := CleanPhysicalReplay.Exterior rows repeats p outside placeholder ×
  ((i : Fin (branch h)) → SourceChildKernel.Raw
    (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated i)

def rawLaw (flag : Fin (branch h) → FiniteDistribution Bool)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    FiniteDistribution (Raw rows repeats p outside placeholder clauses designated) :=
  (FiniteDistribution.uniform (CleanPhysicalReplay.Exterior rows repeats p outside placeholder)).product
    (FiniteProduct.law (fun i => SourceChildKernel.kernel
      (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated flag i (sources i)))

def nativeBlockLaw (flag : Fin (branch h) → FiniteDistribution Bool)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    FiniteDistribution (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (SourceChildKernel.parentLeftSlots clauses designated sources) rows) :=
  FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw
    (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated flag i (sources i))

def observeLeft (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (sample : Raw rows repeats p outside placeholder clauses designated) :
    Arrays (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources)) rows :=
  WholeCutSampler.evaluate rows repeats p
    (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))
    (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
      (SourceChildKernel.parentLeftSlots clauses designated sources) sample.1
      (SourceChildKernel.leftChildren rows clauses designated sources sample.2))

end
end PerfectCompleteness.SourcePhysicalWholeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourcePhysicalTapeLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTapeLaw

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Tag := SourceChildKernel.Sources (m := m) (t := t) designated ×
  (Fin (branch h) → Bool)

def insideSlots (tag : Tag (m := m) (t := t) designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  SourcePhysicalTaggedChildren.slots clauses designated tag.1 tag.2

def nativeSlots (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources)

def projectedSlots (tag : Tag (m := m) (t := t) designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (insideSlots clauses designated tag)

def fullProjection (tag : Tag (m := m) (t := t) designated) :
    ∀ s k, MixedSupport.Projection
      (nativeSlots p outside clauses designated tag.1 s k)
      (projectedSlots p outside clauses designated tag s k) :=
  CutProjectionAssembly.fillProjection p outside _ _
    (fun leaf k => SourceChildKernel.projection clauses designated leaf.1
      (tag.1 leaf.1) (tag.2 leaf.1) leaf.2 k)

abbrev Sample := CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated

abbrev Exterior := CleanPhysicalReplay.Exterior rows repeats p outside placeholder

def rebuild (tag : Tag (m := m) (t := t) designated)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (insideSlots clauses designated tag) rows) :
    WholeArraySampler.Tape rows repeats p (projectedSlots p outside clauses designated tag) :=
  WholeCutSampler.collapse rows repeats p (projectedSlots p outside clauses designated tag)
    (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder
      (insideSlots clauses designated tag) external children)

def sourceTag (sample : Sample (t := t) rows repeats p clauses designated) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  (SourceChildKernelJoint.groupEquiv rows clauses designated sample).1

def tag (sample : Sample (t := t) rows repeats p clauses designated) :
    Tag (m := m) (t := t) designated :=
  (sourceTag rows repeats p clauses designated sample,
    fun i => SourceChildKernel.rawProjected rows clauses designated i (sample i).2.2)

def observeFiber (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (sample : SourcePhysicalWholeLaw.Raw rows repeats p outside placeholder clauses designated) :
    Σ flags : Fin (branch h) → Bool,
      WholeArraySampler.Tape rows repeats p
        (projectedSlots p outside clauses designated (sources, flags)) :=
  let decoded := SourcePhysicalTaggedChildren.observe rows clauses designated sources sample.2
  ⟨decoded.1, rebuild rows repeats p outside placeholder clauses designated
    (sources, decoded.1) sample.1 decoded.2⟩

end
end PerfectCompleteness.SourcePhysicalTapeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCutBridge
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutBridge

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

def scalarValuesLaw (calls : Nat) (repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Fin calls → H slots) :=
  FiniteProduct.law (fun _ : Fin calls =>
    RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain slots))

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.OriginalWholeCutBridge

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedSharedSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open PreliminarySampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

abbrev Record (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t cut : Nat) (rows : Nat → Nat) :=
  (context : Context branch n t m cut rows) ×
    Arrays (sourceSlots clauses (endpoints context.1)) rows

def contextLaw [NeZero m] (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Context branch n t m cut rows) :=
  questionsLaw.product ((GeometricCutSplit.prefixLaw hcut hbranch).product
    (CanonicalDirections.law rows n hrows))

def forgetSuffix (clauses : Fin m → SourceClause.NormalizedClause v)
    (hcut : cut + 1 ≤ n)
    (sample : CandidateCoupling.Shared clauses branch n t rows) :
    Record clauses branch n t cut rows :=
  ⟨(sample.1.1, ((GeometricCutSplit.splitEquiv hcut sample.1.2).1,
    (CanonicalDirections.tupleEquiv rows sample.1.2).symm sample.2.2)), sample.2.1⟩

def originalLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Record clauses branch n t cut rows) :=
  (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).pushforward
    (forgetSuffix clauses hcut)

def stoppedLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Record clauses branch n t cut rows) :=
  CompletionSoundness.sigmaLaw (contextLaw hcut hbranch hrows) (fun context =>
    WholeArraySampler.law rows repeats (GeometricCutSplit.prefixPath hcut context.2.1)
      (sourceSlots clauses (endpoints context.1)))

def averagedLaw [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Record clauses branch n t cut rows) :=
  CompletionSoundness.sigmaLaw (contextLaw hcut hbranch hrows) (fun context =>
    CutContinuationAveraging.originalArrayLaw rows repeats
      (GeometricCutSplit.prefixPath hcut context.2.1)
      (sourceSlots clauses (endpoints context.1))
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut)))

end
end PerfectCompleteness.StoppedSharedSampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedSharedEvents
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedEvents

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

def referenceSuffix (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k) :
    Slots branch (cut + 1) :=
  Classical.choice (GeometricPath.slots_nonempty (cut + 1)
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut)))

def representativeLeaf (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (context : Context branch n t m cut rows) : Slots branch n :=
  (GeometricCutSplit.prefixPath hcut context.2.1).slotEmbedding (referenceSuffix hcut hbranch)

def win (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (level : Fin n) (record : Record clauses branch n t cut rows) : Bool :=
  PreliminaryStrategy.observe clauses
    (PreliminaryStrategy.extend clauses branch n t rows repeats strategy)
    (record.1.1, representativeLeaf hcut hbranch record.1) record.2
    (PrefixTests.choiceAt rows (representativeLeaf hcut hbranch record.1) level
      (record.1.2.2 level))

def pair (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k) (i j : Fin n)
    (record : Record clauses branch n t cut rows) : Bool :=
  win clauses strategy hcut hbranch i record && win clauses strategy hcut hbranch j record

end
end PerfectCompleteness.StoppedSharedEvents

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_StoppedOwnInputGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedOwnInputGeometry

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RelativeDescendantProducts
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n : Nat}

theorem exists_relativePath {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    ∃ p : Path branch (Nodes.height upper) (Nodes.height lower),
      (Nodes.path upper).append p = Nodes.path lower := by
  induction h with
  | root i lower => exact ⟨.step i (Nodes.path lower), rfl⟩
  | child i h ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨p, congrArg (Path.step i) hp⟩

def cutOfBelow {upper lower : Nodes branch n} (h : Below branch upper lower) :
    OwnInputReference.Cut upper lower where
  proper := h.height_lt
  path := Classical.choose (exists_relativePath h)
  slots_agree := by
    intro s
    rw [← Path.slotEmbedding_append, Classical.choose_spec (exists_relativePath h)]

theorem fullPath_cutOfBelow {upper lower : Nodes branch n}
    (h : Below branch upper lower) :
    WholeArrayInteriorOwnInputLaw.fullPath upper lower (cutOfBelow h) =
      Nodes.path lower :=
  Classical.choose_spec (exists_relativePath h)

def pathTapeEquiv {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q) :
    WholeArraySampler.Tape rows repeats p.2 slots ≃
      WholeArraySampler.Tape rows repeats q.2 slots :=
  Equiv.cast (congrArg
    (fun path : Σ height, Path branch n height =>
      WholeArraySampler.Tape rows repeats path.2 slots) h)

end
end PerfectCompleteness.StoppedOwnInputGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedExperiment
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RelativeDescendantProducts
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

theorem below_append (hij : i < j) : {n : Nat} → (p : Path branch n (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) →
    Below branch (WholeArrayInteriorExterior.upperNode p)
      (WholeArrayInteriorExterior.upperNode (p.append q))
  | _, .refl _, q => by
      cases q with
      | refl => omega
      | step child q => exact Below.root child (WholeArrayInteriorExterior.upperNode q)
  | _, .step child p, q => Below.child child (below_append hij p q)

abbrev Outer := PreliminarySampler.Questions branch n t m ×
  GeometricCutSplit.Prefix branch n (j + 1)

abbrev Inner (rows : Nat → Nat) :=
  GeometricCutSplit.Prefix branch (j + 1) (i + 1) ×
    (SourceProjectedTag.Tag (branch := branch) (n := i) (t := t) ×
      CanonicalDirections.Tuple rows n)

def outerLaw [NeZero m] (hupper : j + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) :
    FiniteDistribution (Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  PreliminarySampler.questionsLaw.product (GeometricCutSplit.prefixLaw hupper hbranch)

def innerLaw (rows : Nat → Nat) (hij : i < j)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (flag : Fin (branch i) → FiniteDistribution Bool) :
    FiniteDistribution (Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).product
    ((SourceProjectedTag.law (t := t) flag).product (CanonicalDirections.law rows n hrows))

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev nativeSlots (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  sourceSlots clauses (PreliminarySampler.endpoints o.1)

def upperPath (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  GeometricCutSplit.prefixPath hupper o.2

def lowerPath (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) k.1

def stoppedPath (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (upperPath hupper o).append (lowerPath rows hij k)

def upper (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  WholeArrayInteriorExterior.upperNode (upperPath hupper o)

def lower (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  WholeArrayInteriorExterior.upperNode (stoppedPath rows hupper hij o k)

@[simp] theorem upper_height (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Nodes.height (upper hupper o) = j + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

@[simp] theorem lower_height (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Nodes.height (lower rows hupper hij o k) = i + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

def cut (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    OwnInputReference.Cut (upper hupper o) (lower rows hupper hij o k) :=
  StoppedOwnInputGeometry.cutOfBelow (below_append hij (upperPath hupper o) (lowerPath rows hij k))

theorem fullPath_spec (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    (⟨Nodes.height (lower rows hupper hij o k),
      WholeArrayInteriorOwnInputLaw.fullPath (upper hupper o) (lower rows hupper hij o k)
        (cut rows hupper hij o k)⟩ : Σ height, Path branch n height) =
      ⟨i + 1, stoppedPath rows hupper hij o k⟩ := by
  have hpath :
      WholeArrayInteriorOwnInputLaw.fullPath (upper hupper o) (lower rows hupper hij o k)
        (cut rows hupper hij o k) = Nodes.path (lower rows hupper hij o k) :=
    StoppedOwnInputGeometry.fullPath_cutOfBelow
      (below_append hij (upperPath hupper o) (lowerPath rows hij k))
  exact (congrArg (fun path : Path branch n (Nodes.height (lower rows hupper hij o k)) =>
    (⟨Nodes.height (lower rows hupper hij o k), path⟩ : Σ height, Path branch n height))
      hpath).trans
    (WholeArrayInteriorExterior.upperNode_spec (stoppedPath rows hupper hij o k))

def cutQuestions (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    PreliminarySampler.Questions branch (i + 1) t m :=
  fun leaf a => o.1 ((stoppedPath rows hupper hij o k).slotEmbedding leaf) a

def projectedSlots (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill (stoppedPath rows hupper hij o k) (nativeSlots clauses o)
    (SourceProjectedTag.mixedInside clauses designated (cutQuestions rows hupper hij o k)
      k.2.1.1 k.2.1.2)

theorem fill_native (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    CutSlotAssembly.fill (stoppedPath rows hupper hij o k) (nativeSlots clauses o)
      (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o k)) =
      nativeSlots clauses o :=
  CutSlotAssembly.fill_restrict (stoppedPath rows hupper hij o k) (nativeSlots clauses o)

def projection (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    ∀ leaf a, MixedSupport.Projection (nativeSlots clauses o leaf a)
      (projectedSlots clauses rows hupper hij designated o k leaf a) :=
  fun leaf a => CutProjectionAssembly.castProjection
    (congrFun (congrFun (fill_native clauses rows hupper hij o k) leaf) a) rfl
    (CutProjectionAssembly.fillProjection (stoppedPath rows hupper hij o k) (nativeSlots clauses o)
      (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o k))
      (SourceProjectedTag.mixedInside clauses designated (cutQuestions rows hupper hij o k)
        k.2.1.1 k.2.1.2)
      (SourceProjectedTag.projection clauses designated (cutQuestions rows hupper hij o k)
        k.2.1.1 k.2.1.2) leaf a)

def direction (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Block rows (lower rows hupper hij o k) :=
  let level : Fin n := ⟨i, Nat.lt_of_lt_of_le (Nat.lt_trans hij (Nat.lt_succ_self j)) hupper⟩
  (PrefixTests.nodeDirection rows level
    ⟨lower rows hupper hij o k, lower_height rows hupper hij o k⟩ (k.2.2 level)).val

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
    (nativeSlots clauses o) (projectedSlots clauses rows hupper hij designated o)
    (projection clauses rows hupper hij designated o) (upper hupper o) (i + 1)
    (lower rows hupper hij o) (cut rows hupper hij o) (direction rows hupper hij o)
    (innerLaw rows hij hbranch hrows flag) σ

abbrev TapeSample (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) ×
    WholeArraySampler.Tape rows repeats (stoppedPath rows hupper hij o k)
      (projectedSlots clauses rows hupper hij designated o k)

def tapeLaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    FiniteDistribution (TapeSample clauses rows repeats hupper hij designated o) :=
  CompletionSoundness.sigmaLaw (innerLaw rows hij hbranch hrows flag) (fun k =>
    WholeArraySampler.tapeLaw rows repeats (stoppedPath rows hupper hij o k)
      (projectedSlots clauses rows hupper hij designated o k))

def tapeRead (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : TapeSample clauses rows repeats hupper hij designated o) :
    HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (projectedSlots clauses rows hupper hij designated o) (upper hupper o)
      (lower rows hupper hij o) (cut rows hupper hij o) :=
  ⟨sample.1, StoppedOwnInputGeometry.pathTapeEquiv rows repeats
    (projectedSlots clauses rows hupper hij designated o sample.1)
    (fullPath_spec rows hupper hij o sample.1).symm sample.2⟩

section Physical

variable [NeZero m]

abbrev PhysicalBase :=
  GeometricCutSplit.Prefix branch (j + 1) (i + 1) ×
    (SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t) ×
      CanonicalDirections.Tuple rows n)

def withFlags (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i)) :
    Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows :=
  (base.1, ((base.2.1, flags), base.2.2))

def physicalBaseLaw :
    FiniteDistribution (PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).product
    ((SourceProjectedTag.positionLaw (branch := branch) (n := i) (t := t)).product
      (CanonicalDirections.law rows n hrows))

abbrev baseTag (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  withFlags rows base (fun _ => false)

def physicalSources (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  SourceQuestionKernelJoint.sources designated
    (cutQuestions rows hupper hij o (baseTag rows base)) base.2.1

abbrev PhysicalRaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  SourcePhysicalWholeLaw.Raw rows repeats (stoppedPath rows hupper hij o (baseTag rows base))
    (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows base)))
    clauses designated

abbrev PhysicalSample (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) ×
    PhysicalRaw clauses rows repeats hupper hij designated o base

def physicalFiberLaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : PhysicalBase (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    FiniteDistribution (PhysicalRaw clauses rows repeats hupper hij designated o base) :=
  SourcePhysicalWholeLaw.rawLaw rows repeats (stoppedPath rows hupper hij o (baseTag rows base))
    (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows base)))
    clauses designated flag (physicalSources rows hupper hij designated o base)

def physicalLaw (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    FiniteDistribution (PhysicalSample clauses rows repeats hupper hij designated o) :=
  CompletionSoundness.sigmaLaw (physicalBaseLaw rows hij hbranch hrows)
    (physicalFiberLaw clauses rows repeats hupper hij designated flag o)

def physicalRead (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : PhysicalSample clauses rows repeats hupper hij designated o) :
    TapeSample clauses rows repeats hupper hij designated o :=
  let observed := SourcePhysicalTapeLaw.observeFiber rows repeats
    (stoppedPath rows hupper hij o (baseTag rows sample.1)) (nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses (cutQuestions rows hupper hij o (baseTag rows sample.1)))
    clauses designated (physicalSources rows hupper hij designated o sample.1) sample.2
  ⟨withFlags rows sample.1 observed.1, observed.2⟩

def physicalExperimentRead
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : PhysicalSample clauses rows repeats hupper hij designated o) :=
  tapeRead clauses rows repeats hupper hij designated o
    (physicalRead clauses rows repeats hupper hij designated o sample)

end Physical

end
end PerfectCompleteness.StoppedProjectedExperiment

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_StoppedProjectedBucketIndex
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedBucketIndex

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

abbrev Base := GeometricCutSplit.Prefix branch (j + 1) (i + 1) ×
  SourceProjectedTag.Tag (branch := branch) (n := i) (t := t)

def baseOf (rows : Nat → Nat)
    (k : StoppedProjectedExperiment.Inner (branch := branch) (n := n)
      (i := i) (j := j) (t := t) rows) : Base (branch := branch) (i := i) (j := j) (t := t) :=
  (k.1, k.2.1)

def withDirections (rows : Nat → Nat)
    (base : Base (branch := branch) (i := i) (j := j) (t := t))
    (directions : CanonicalDirections.Tuple rows n) :
    StoppedProjectedExperiment.Inner (branch := branch) (n := n)
      (i := i) (j := j) (t := t) rows :=
  (base.1, (base.2, directions))

def defaultDirections (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) :
    CanonicalDirections.Tuple rows n :=
  fun level => Classical.choice
    (PreliminarySampler.directionNonempty (rows (level.val + 1)) (hrows level.val))

def baseLaw (hij : i < j) (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool) :
    FiniteDistribution (Base (branch := branch) (i := i) (j := j) (t := t)) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).product
    (SourceProjectedTag.law (t := t) flag)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

abbrev key (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  withDirections (n := n) rows base (defaultDirections rows hrows)

abbrev Tape (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  WholeArraySampler.Tape rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o (key rows hrows base))
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
      (key rows hrows base))

def tapeLaw (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    FiniteDistribution (Tape clauses rows repeats hupper hij designated hrows o base) :=
  WholeArraySampler.tapeLaw rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o (key rows hrows base))
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
      (key rows hrows base))

end
end PerfectCompleteness.StoppedProjectedBucketIndex

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedPathHead
attribute [-instance] _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedPathHead

open DescendantSpaces

variable {branch : Nat → Nat} {i j : Nat}

def headTail (hij : i < j) (p : Path branch (j + 1) (i + 1)) :
    Fin (branch j) × Path branch j (i + 1) := by
  cases p with
  | refl => omega
  | step a q => exact (a, q)

def child (hij : i < j) (p : Path branch (j + 1) (i + 1)) : Fin (branch j) :=
  (headTail hij p).1

def tail (hij : i < j) (p : Path branch (j + 1) (i + 1)) : Path branch j (i + 1) :=
  (headTail hij p).2

theorem step_eq (hij : i < j) (p : Path branch (j + 1) (i + 1)) :
    p = Path.step (child hij p) (tail hij p) := by
  cases p with
  | refl => omega
  | step a q => rfl

@[simp] theorem child_step (hij : i < j) (a : Fin (branch j))
    (q : Path branch j (i + 1)) : child hij (Path.step a q) = a := rfl

@[simp] theorem tail_step (hij : i < j) (a : Fin (branch j))
    (q : Path branch j (i + 1)) : tail hij (Path.step a q) = q := rfl

theorem lowerPath_step_eq {n t : Nat} (rows : Nat → Nat) (hij : i < j)
    (k : StoppedProjectedExperiment.Inner
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    StoppedProjectedExperiment.lowerPath rows hij k =
      Path.step (child hij (StoppedProjectedExperiment.lowerPath rows hij k))
        (tail hij (StoppedProjectedExperiment.lowerPath rows hij k)) :=
  step_eq hij _

end PerfectCompleteness.StoppedPathHead

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutCalls
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutCalls

open DescendantSpaces
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i depth : Nat}

theorem card_eq_count (rows repeats : Nat → Nat)
    (p : Path branch n j) (r : Path branch j i) :
    Fintype.card (Index rows repeats p r) = count rows repeats n j i := by
  simp only [Index, Fintype.card_sum, OriginalCutCalls.card_eq_count,
    TerminalCalls.card_eq_prod, count]

def numbering (rows repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i) :
    Index rows repeats p r ≃ Fin (count rows repeats n j i) :=
  Fintype.equivFinOfCardEq (card_eq_count rows repeats p r)

end
end PerfectCompleteness.UpperScalarCutCalls

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutReconstruction

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

theorem cutSlots_append (p : Path branch n j) (r : Path branch j i)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    cutSlots (p.append r) slots = cutSlots r (cutSlots p slots) := by
  funext s a
  exact congrArg (fun leaf => slots leaf a) (p.slotEmbedding_append r s)

def cutSpaceEquiv (p : Path branch n j) (r : Path branch j i)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    H (cutSlots (p.append r) slots) ≃ H (cutSlots r (cutSlots p slots)) :=
  Equiv.cast (congrArg (fun s : Slots branch i → Fin t → MixedSupport.Slot => ↥(H s))
    (cutSlots_append p r slots))

abbrev FreshExterior (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalTerminalSplit.ExteriorTape F2 repeats r (LeafDomain (cutSlots p slots))

abbrev FreshValues (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  TerminalCalls.TerminalIndex repeats r → H (cutSlots (p.append r) slots)

abbrev FreshRecord (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  FreshValues repeats p r slots × FreshExterior repeats p r slots

def readFresh (repeats : Nat → Nat) (p : Path branch n j) (r : Path branch j i)
    (suffix : Path branch i k) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : RecursiveSampler.Tape F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots))) :
    FreshRecord repeats p r slots :=
  let split := OriginalTerminalSplit.splitTape F2 repeats r suffix
    (LeafDomain (cutSlots p slots)) tape
  (fun call => (cutSpaceEquiv p r slots).symm
      (RecursiveSampler.evaluate F2 repeats suffix
        (r.family (LeafDomain (cutSlots p slots))) (split.1 call)), split.2)

def reconstructFresh (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : FreshRecord repeats p r slots) : H (cutSlots p slots) :=
  OriginalScalarReconstruction.reconstruct F2 repeats r (LeafDomain (cutSlots p slots))
    (fun call => cutSpaceEquiv p r slots (record.1 call)) record.2

abbrev Exterior (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalWholeCutTape.Exterior rows repeats (p.append r) slots ×
    FreshExterior repeats p r slots

abbrev Record (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p r slots ×
    CutChildGrouping.Assembled (C := UpperScalarCutCalls.Index rows repeats p r)
      (cutSlots (p.append r) slots) rows

def freshRecord (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p r slots) : FreshRecord repeats p r slots :=
  (fun call => record.2.1 (.inr call), record.1.2)

abbrev NumberedRecord (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p r slots ×
    CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)))
      (cutSlots (p.append r) slots) rows

def numberRecordEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Record rows repeats p r slots ≃ NumberedRecord rows repeats p r slots :=
  Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.arrowCongr (UpperScalarCutCalls.numbering rows repeats p r)
      (Equiv.refl _)) (Equiv.refl _))

end
end PerfectCompleteness.UpperScalarCutReconstruction

end

section

namespace PerfectCompleteness.UpperScalarCutBucket

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def descendTape (rows repeats : Nat → Nat) :
    {n j i k : Nat} → (p : Path branch n j) → (r : Path branch j (i + 1)) →
      (chosen : Fin (branch i)) → (q : Path branch i k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots →
          WholeArraySampler.Tape rows repeats (r.append (.step chosen q)) (cutSlots p slots)
  | _, _, _, _, .refl _, _, _, _, _, tape => tape
  | _, _, _, _, .step child p, r, chosen, q, slots, tape =>
      descendTape rows repeats p r chosen q (childSlots slots child)
        (tape (.inr (.inl ())))

def continuedRootTape (rows repeats : Nat → Nat) :
    {j i k : Nat} → (r : Path branch (j + 1) (i + 1)) →
      (chosen : Fin (branch i)) → (q : Path branch i k) →
      (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats (r.append (.step chosen q)) slots →
          WholeArraySampler.RootTape rows repeats (r.append (.step chosen q)) slots
  | _, _, _, .refl _, _, _, _, tape => tape (.inl ())
  | _, _, _, .step _ _, _, _, _, tape => tape (.inl ())

end
end PerfectCompleteness.UpperScalarCutBucket

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalPrefixContinuation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalPrefixContinuation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n k t : Nat} {K : Type*} [Fintype K]

def sourceLaw (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n) :
    FiniteDistribution (Tape calls rows repeats slots q) :=
  CompletionSoundness.sigmaLaw (tagLaw ν hbranch)
    (fun tag => OriginalChildBlocks.sourceLaw calls rows repeats tag.1 (q tag.2) slots)

def observed (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) (ω : Tape calls rows repeats slots q) : CutChildGrouping.Assembled (C := Fin calls) slots rows :=
  OriginalChildBlocks.observed calls rows repeats ω.1.1
    (q ω.1.2) slots ω.2

def assembledLaw (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    FiniteDistribution (CutChildGrouping.Assembled (C := Fin calls) slots rows) :=
  (sourceLaw calls rows repeats slots ν q hbranch).pushforward
    (observed calls rows repeats slots q)

end
end PerfectCompleteness.OriginalPrefixContinuation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_StoppedProjectedBuckets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedBuckets

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

abbrev Base := StoppedProjectedBucketIndex.Base (branch := branch) (i := i) (j := j) (t := t)

abbrev key (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedBucketIndex.key (n := n) rows hrows base

variable (hbranch : ∀ k < j + 1, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

local instance backgroundFintype_r2d0309_1 : Fintype (HierarchicalMatrixTable.Background (rows := rows)
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
local instance rowSpaceFintype_r2d0309_7 : Fintype (NodeEmbedding.RowSpace
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
include hrows in
theorem rows_positive : 0 < rows (Nodes.height (StoppedProjectedExperiment.upper hupper o)) := by
  rw [StoppedProjectedExperiment.upper_height]
  exact hrows j

end
end PerfectCompleteness.StoppedProjectedBuckets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_StoppedCleanGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanGeometry

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat}

def descendant : {N j i : Nat} → (p : Path branch N (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) → i < j →
    HierarchicalFrozenTables.LowerNodes (WholeArrayInteriorExterior.upperNode p) (i + 1)
  | _, _, _, .refl _, q, hij =>
      ⟨⟨WholeArrayInteriorExterior.upperNode q,
          (WholeArrayInteriorExterior.upperNode_height q).trans_lt (Nat.succ_lt_succ hij)⟩,
        WholeArrayInteriorExterior.upperNode_height q⟩
  | _, _, _, .step _ p, q, hij => descendant p q hij

theorem lowerNode_descendant : {N j i : Nat} → (p : Path branch N (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) → (hij : i < j) →
    HierarchicalLeftDecoder.LowerNode (WholeArrayInteriorExterior.upperNode p) (i + 1)
        (descendant p q hij) = WholeArrayInteriorExterior.upperNode (p.append q)
  | _, _, _, .refl _, _, _ => rfl
  | N + 1, _, _, .step child p, q, hij =>
      congrArg (fun node : Nodes branch N =>
        (Sum.inr (child, node) : Nodes branch (N + 1))) (lowerNode_descendant p q hij)

variable {N j i : Nat} (p : Path branch N (j + 1))
  (q : Path branch (j + 1) (i + 1)) (hij : i < j)

def cut : OwnInputReference.Cut (WholeArrayInteriorExterior.upperNode p)
    (HierarchicalLeftDecoder.LowerNode (WholeArrayInteriorExterior.upperNode p) (i + 1)
      (descendant p q hij)) :=
  DecoderSourcePullback.selectedCut (WholeArrayInteriorExterior.upperNode p) (i + 1)
    (descendant p q hij)

@[simp] theorem lowerHeight :
    Nodes.height (HierarchicalLeftDecoder.LowerNode
      (WholeArrayInteriorExterior.upperNode p) (i + 1) (descendant p q hij)) = i + 1 :=
  CleanDecoderContext.lowerHeight (WholeArrayInteriorExterior.upperNode p) (descendant p q hij)

theorem fullPath_spec : {N j i : Nat} → (p : Path branch N (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) → (hij : i < j) →
    (⟨Nodes.height (HierarchicalLeftDecoder.LowerNode
        (WholeArrayInteriorExterior.upperNode p) (i + 1) (descendant p q hij)),
      WholeArrayInteriorOwnInputLaw.fullPath (WholeArrayInteriorExterior.upperNode p)
        (HierarchicalLeftDecoder.LowerNode (WholeArrayInteriorExterior.upperNode p) (i + 1)
          (descendant p q hij)) (cut p q hij)⟩ : Σ height, Path branch N height) =
      ⟨i + 1, p.append q⟩
  | _, _, _, .refl _, q, _ => WholeArrayInteriorExterior.upperNode_spec q
  | N + 1, _, _, .step child p, q, hij =>
      congrArg (fun z : Σ height, Path branch N height =>
        (⟨z.1, Path.step child z.2⟩ : Σ height, Path branch (N + 1) height))
          (fullPath_spec p q hij)

theorem append_cast_heq {N a b c : Nat} (pref : Path branch N a)
    (suffix : Path branch a b) (h : b = c) :
    HEq (pref.append (h ▸ suffix)) (pref.append suffix) := by
  cases h
  rfl

theorem cleanPath_eq :
    CleanRecordDecoderInput.path (WholeArrayInteriorExterior.upperNode p)
      (descendant p q hij) (cut p q hij) = p.append q := by
  apply eq_of_heq
  exact (append_cast_heq (Nodes.path (WholeArrayInteriorExterior.upperNode p))
    (cut p q hij).path
    (CleanDecoderContext.lowerHeight (WholeArrayInteriorExterior.upperNode p)
      (descendant p q hij))).trans ((Sigma.mk.inj (fullPath_spec p q hij)).2)

def firstLeaf (hbranch : ∀ k, 0 < branch k) : (height : Nat) → Slots branch height
  | 0 => ()
  | height + 1 => (⟨0, hbranch height⟩, firstLeaf hbranch height)

end
end PerfectCompleteness.StoppedCleanGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SlotProjectedExperiment
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricPrefixSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPrefixSplit.split_join _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SlotProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

def selectSlot : MixedSupport.Slot → Fin 3 → MixedSupport.Slot
  | .clause _ ids _, position => .bit (ids position)
  | .bit id, _ => .bit id

def selectProjection (s : MixedSupport.Slot) (position : Fin 3) :
    MixedSupport.Projection s (selectSlot s position) := by
  cases s with
  | clause occurrence ids signs => exact .select occurrence ids signs position
  | bit id => exact .keep (.bit id)

def flaggedSlot (s : MixedSupport.Slot) (position : Fin 3) : Bool → MixedSupport.Slot
  | false => s
  | true => selectSlot s position

def flaggedProjection (s : MixedSupport.Slot) (position : Fin 3) :
    (b : Bool) → MixedSupport.Projection s (flaggedSlot s position b)
  | false => .keep s
  | true => selectProjection s position

variable {branch : Nat → Nat} {n i j t v m : Nat}

def mixedInside (slots : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i)) :
    Slots branch (i + 1) → Fin t → MixedSupport.Slot :=
  fun leaf a => flaggedSlot (slots leaf a) (choices leaf.1 leaf.2 a) (flags leaf.1)

def insideProjection (slots : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i)) :
    ∀ leaf a, MixedSupport.Projection (slots leaf a) (mixedInside slots choices flags leaf a) :=
  fun leaf a => flaggedProjection (slots leaf a) (choices leaf.1 leaf.2 a) (flags leaf.1)

abbrev Inner (rows : Nat → Nat) :=
  StoppedProjectedExperiment.Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows

abbrev innerLaw (rows : Nat → Nat) (hij : i < j)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (flag : Fin (branch i) → FiniteDistribution Bool) :=
  StoppedProjectedExperiment.innerLaw (n := n) (t := t) rows hij hbranch hrows flag

variable (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (pref : GeometricCutSplit.Prefix branch n (j + 1))

def upperPath := GeometricCutSplit.prefixPath hupper pref

abbrev lowerPath (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  StoppedProjectedExperiment.lowerPath rows hij k

def stoppedPath (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (upperPath hupper pref).append (lowerPath rows hij k)

def upper := WholeArrayInteriorExterior.upperNode (upperPath hupper pref)

def lower (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  WholeArrayInteriorExterior.upperNode (stoppedPath rows hupper hij pref k)

@[simp] theorem upper_height : Nodes.height (upper hupper pref) = j + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

@[simp] theorem lower_height
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Nodes.height (lower rows hupper hij pref k) = i + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

def cut (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    OwnInputReference.Cut (upper hupper pref) (lower rows hupper hij pref k) :=
  StoppedOwnInputGeometry.cutOfBelow
    (StoppedProjectedExperiment.below_append hij (upperPath hupper pref) (lowerPath rows hij k))

def direction (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Block rows (lower rows hupper hij pref k) :=
  let level : Fin n := ⟨i, Nat.lt_of_lt_of_le (Nat.lt_trans hij (Nat.lt_succ_self j)) hupper⟩
  (PrefixTests.nodeDirection rows level
    ⟨lower rows hupper hij pref k, lower_height rows hupper hij pref k⟩ (k.2.2 level)).val

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

def inside (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Slots branch (i + 1) → Fin t → MixedSupport.Slot :=
  fun leaf a => slots ((stoppedPath rows hupper hij pref k).slotEmbedding leaf) a

def projectedSlots (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill (stoppedPath rows hupper hij pref k) slots
    (mixedInside (inside rows hupper hij pref slots k) k.2.1.1 k.2.1.2)

theorem fill_inside (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    CutSlotAssembly.fill (stoppedPath rows hupper hij pref k) slots
      (inside rows hupper hij pref slots k) = slots :=
  CutSlotAssembly.fill_restrict (stoppedPath rows hupper hij pref k) slots

def projection (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    ∀ leaf a, MixedSupport.Projection (slots leaf a)
      (projectedSlots rows hupper hij pref slots k leaf a) :=
  fun leaf a => CutProjectionAssembly.castProjection
    (congrFun (congrFun (fill_inside rows hupper hij pref slots k) leaf) a) rfl
    (CutProjectionAssembly.fillProjection (stoppedPath rows hupper hij pref k) slots
      (inside rows hupper hij pref slots k)
      (mixedInside (inside rows hupper hij pref slots k) k.2.1.1 k.2.1.2)
      (insideProjection (inside rows hupper hij pref slots k) k.2.1.1 k.2.1.2) leaf a)

abbrev Sample := HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
  (projectedSlots rows hupper hij pref slots) (upper hupper pref)
  (lower rows hupper hij pref) (cut rows hupper hij pref)

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment :=
  HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
    slots (projectedSlots rows hupper hij pref slots) (projection rows hupper hij pref slots)
    (upper hupper pref) (i + 1) (lower rows hupper hij pref)
    (cut rows hupper hij pref) (direction rows hupper hij pref)
    (innerLaw rows hij hbranch hrows flag) σ

def family : OriginalDecoderMark.Family branch rows n t
    (Sample rows repeats hupper hij pref) where
  original slots := (experiment rows repeats hupper hij pref slots hbranch hrows flag σ).original
  arrays slots := (experiment rows repeats hupper hij pref slots hbranch hrows flag σ).arrays
  lowerEvent slots := HierarchicalAdviceExperiment.lowerEvent
    (experiment rows repeats hupper hij pref slots hbranch hrows flag σ)

end
end PerfectCompleteness.SlotProjectedExperiment

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourcePhysicalExteriorSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalExteriorSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))

def canonicalSlots (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  sourceSlots clauses (PreliminarySampler.endpoints
    (SourceQuestionCutSplit.join p (fun _ _ => (0 : Fin m)) external))

abbrev CanonicalExterior (external : SourceQuestionCutSplit.OutsideQuestions p t m) :=
  WholeCutGrouping.Exterior rows repeats p (canonicalSlots clauses p external)

abbrev ActualExterior (questions : PreliminarySampler.Questions branch root t m) :=
  CleanPhysicalReplay.Exterior rows repeats p
    (sourceSlots clauses (PreliminarySampler.endpoints questions))
    (sourceSlots clauses (PreliminarySampler.endpoints
      (SourceQuestionCutSplit.restrict p questions)))

theorem canonicalSlots_outside
    (external : SourceQuestionCutSplit.OutsideQuestions p t m)
    (leaf : SourceQuestionCutSplit.OutsideLeaf p) :
    canonicalSlots clauses p external leaf.val =
      fun coordinate => SourceKeys.slot clauses (.clause (external leaf coordinate)) := by
  funext coordinate
  change SourceKeys.slot clauses (.clause
    (SourceQuestionCutSplit.join p (fun _ _ => (0 : Fin m)) external leaf.val coordinate)) = _
  rw [SourceQuestionCutSplit.join_outside]

theorem exteriorSlots_eq
    (questions : PreliminarySampler.Questions branch root t m)
    (leaf : Slots branch root) (hleaf : WholeCutExteriorTransport.Outside p leaf) :
    CutSlotAssembly.fill p
        (sourceSlots clauses (PreliminarySampler.endpoints questions))
        (sourceSlots clauses (PreliminarySampler.endpoints
          (SourceQuestionCutSplit.restrict p questions))) leaf =
      canonicalSlots clauses p (SourceQuestionCutSplit.outside p questions) leaf := by
  rw [CutSlotAssembly.fill_outside p _ _ leaf hleaf]
  exact (canonicalSlots_outside clauses p
    (SourceQuestionCutSplit.outside p questions) ⟨leaf, hleaf⟩).symm

def toCanonical (questions : PreliminarySampler.Questions branch root t m) :
    ActualExterior clauses rows repeats p questions ≃
      CanonicalExterior clauses rows repeats p (SourceQuestionCutSplit.outside p questions) :=
  WholeCutExteriorTransport.equiv rows repeats p _ _
    (exteriorSlots_eq clauses p questions)

def fromCanonical (questions : PreliminarySampler.Questions branch root t m) :
    CanonicalExterior clauses rows repeats p (SourceQuestionCutSplit.outside p questions) ≃
      ActualExterior clauses rows repeats p questions :=
  (toCanonical clauses rows repeats p questions).symm

end
end PerfectCompleteness.SourcePhysicalExteriorSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourcePhysicalSourceSwapLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalSourceSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (designated : Fin (branch h) → Slots branch h)

abbrev Questions := PreliminarySampler.Questions branch root t m
abbrev Positions := SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t)
abbrev Raw := SourceChildKernelJoint.RawTuple (C := WholeCutCalls.Index rows repeats p)
  (t := t) rows clauses designated

omit [NeZero m] in
@[simp] theorem outside_join
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    SourceQuestionCutSplit.outside p (SourceQuestionCutSplit.join p inside external) = external := by
  funext leaf
  exact SourceQuestionCutSplit.join_outside p inside external leaf

def joinedExterior
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external ≃
      SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external) :=
  (Equiv.cast (congrArg (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p)
    (outside_join p inside external).symm)).trans
      (SourcePhysicalExteriorSwap.fromCanonical clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external))

end
end PerfectCompleteness.SourcePhysicalSourceSwap

end

section

namespace PerfectCompleteness.SourcePhysicalStoppedComparison

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Sources := SourceChildKernel.Sources (m := m) (t := t) designated

abbrev NativeArrays (sources : Sources (m := m) (t := t) designated) :=
  Arrays (CutSlotAssembly.fill p outside
    (SourceChildKernel.parentLeftSlots clauses designated sources)) rows

def modifiedLaw (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (sources : Sources (m := m) (t := t) designated) :
    FiniteDistribution (NativeArrays rows p outside clauses designated sources) :=
  (SourcePhysicalWholeLaw.rawLaw rows repeats p outside placeholder clauses designated
    (fun _ => ProjectionPosterior.bernoulli β hβ hβ') sources).pushforward
      (SourcePhysicalWholeLaw.observeLeft rows repeats p outside placeholder clauses designated sources)

def stoppedLaw (sources : Sources (m := m) (t := t) designated) :
    FiniteDistribution (NativeArrays rows p outside clauses designated sources) :=
  WholeArraySampler.law rows repeats p
    (CutSlotAssembly.fill p outside (SourceChildKernel.parentLeftSlots clauses designated sources))

end
end PerfectCompleteness.SourcePhysicalStoppedComparison

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedStoppedDecoderLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedDecoderLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

abbrev familySampleFintype
    {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
    {O : Type*} [Fintype O]
    {upper : O → Nodes branch n}
    {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
    (S : (o : O) → CleanDecoderRate.Setup branch rows repeats n h t v m (upper o) (lower o)) :
    Fintype (DecoderFamilyLaw.Sample S) := inferInstance

attribute [local instance] linearMapFintype

end
end PerfectCompleteness.FixedStoppedDecoderLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalLowerInverseLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLowerInverse

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance lowerHFintype_r2d0309_1 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _
abbrev Answer (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  HierarchicalDecoderTables.Answer slots upper lowerLevel d

local instance answerFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (Answer slots upper lowerLevel d) :=
  HierarchicalAllDecoderTables.answerFintype slots upper lowerLevel d

local instance upperDualFintype_r2d0309_2 : Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
def matrixTable {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r →
      Option (Answer slots upper lowerLevel d)) :
    HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d →
      Option (Answer slots upper lowerLevel d) :=
  fun X => table (HierarchicalLowerMatrixInput.input slots upper lowerLevel
    background d upperMatrix A X)

end
end PerfectCompleteness.HierarchicalLowerInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutFormCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutFormCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n height t : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (inside : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)

def nativeScalar (f : H inside) :
    HierarchicalDecoderTables.LowerH (CutSlotAssembly.fill path outside inside) upper level d :=
  LowerCutDecoderForm.spaceEquiv path (CutSlotAssembly.fill path outside inside)
    upper level d hnode
    (CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill path outside inside).symm f)

def nativeForm
    (answer : HierarchicalDecoderTables.Answer
      (CutSlotAssembly.fill path outside inside) upper level d) :
    ChildBilinearCollisionTransfer.ParentForm inside :=
  CutNativeForms.formCast (CleanPhysicalReplay.cutSlots_fill path outside inside)
    (LowerCutDecoderForm.form path (CutSlotAssembly.fill path outside inside)
      upper level d hnode answer)

end
end PerfectCompleteness.LowerCutFormCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LowerCutInstalledInput
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutInstalledInput

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

section NodeEquality

variable (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev NodeRows (node : Nodes branch n) := Fin (rows (Nodes.height node)) → H (nodeSlots slots node)
abbrev NodeMatrix (node : Nodes branch n) :=
  Module.Dual F2 (H (nodeSlots slots node)) →ₗ[F2] Block rows node

def rowCast {i j : Nodes branch n} (h : i = j) :
    NodeRows rows slots i ≃ₗ[F2] NodeRows rows slots j := by
  subst j
  exact LinearEquiv.refl F2 _

def matrixCast {i j : Nodes branch n} (h : i = j) :
    NodeMatrix rows slots i ≃ₗ[F2] NodeMatrix rows slots j := by
  subst j
  exact LinearEquiv.refl F2 _

def scalarCast {i j : Nodes branch n} (h : i = j) :
    H (nodeSlots slots i) ≃ₗ[F2] H (nodeSlots slots j) := by
  subst j
  exact LinearEquiv.refl F2 _

def directionCast {i j : Nodes branch n} (h : i = j) :
    BucketSampler.Direction (rows (Nodes.height i)) ≃
      BucketSampler.Direction (rows (Nodes.height j)) := by
  subst j
  exact Equiv.refl _

end NodeEquality

variable (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

def lowerMatrixEquiv : LowerCutPair.NativeMatrix rows p slots ≃ₗ[F2]
    HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d :=
  (LowerCutNodeMatrix.matrixEquiv rows p slots).trans (matrixCast rows slots hnode)

def lowerScalarEquiv : H (WholeCutGrouping.cutSlots p slots) ≃ₗ[F2]
    HierarchicalDecoderTables.LowerH slots upper lowerLevel d :=
  (LowerCutNodeCoordinates.scalarEquiv p slots).trans (scalarCast slots hnode)

def lowerDirectionEquiv : BucketSampler.Direction (rows (m + 1)) ≃
    BucketSampler.Direction (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) :=
  (LowerCutNodeCoordinates.directionEquiv rows p).trans (directionCast rows hnode)

end
end PerfectCompleteness.LowerCutInstalledInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutUniformCoordinatesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutUniformCoordinates

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}
  (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

abbrev NativeSample :=
  BucketSampler.Direction (rows (m + 1)) ×
    (LowerCutPair.NativeMatrix rows p slots × H (WholeCutGrouping.cutSlots p slots))

abbrev LowerSample :=
  BucketSampler.Direction
      (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) ×
    (HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d ×
      HierarchicalDecoderTables.LowerH slots upper lowerLevel d)

def sampleEquiv : NativeSample rows p slots ≃ LowerSample rows slots upper lowerLevel d :=
  (LowerCutInstalledInput.lowerDirectionEquiv rows p upper lowerLevel d hnode).prodCongr
    ((LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode).toEquiv.prodCongr
      (LowerCutInstalledInput.lowerScalarEquiv p slots upper lowerLevel d hnode).toEquiv)

@[simp] theorem sampleEquiv_apply (x : NativeSample rows p slots) :
    sampleEquiv rows p slots upper lowerLevel d hnode x =
      (LowerCutInstalledInput.lowerDirectionEquiv rows p upper lowerLevel d hnode x.1,
        (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode x.2.1,
          LowerCutInstalledInput.lowerScalarEquiv p slots upper lowerLevel d hnode x.2.2)) := rfl

variable [Nonempty (BucketSampler.Direction (rows (m + 1)))]

include p hnode in

theorem lowerDirection_nonempty :
    Nonempty (BucketSampler.Direction
      (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))) := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (BucketSampler.Direction (rows (m + 1))))
  exact ⟨LowerCutInstalledInput.lowerDirectionEquiv rows p upper lowerLevel d hnode a⟩

local instance lowerHFintype :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _

end
end PerfectCompleteness.LowerCutUniformCoordinates

end

section

namespace PerfectCompleteness.LowerCutUniformCollisionLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

variable (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)
  (hbranch : ∀ k < n, 0 < branch k) {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (table : HierarchicalAllDecoderTables.Input (rows := rows)
    slots upper lowerLevel adviceRows → HierarchicalAllDecoderTables.UpperAnswer slots upper)
  (cutoff : Nat)

local instance lowerHFintype :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _
local instance answerFintype :
    Fintype (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype (V := PointwiseSpaces.squareSpace
    (HierarchicalDecoderTables.LowerH slots upper lowerLevel d))

end
end PerfectCompleteness.LowerCutUniformCollisionLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionCollisionTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionCollisionTransport

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (tables : (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m)) →
    SourceQuestionLowerForms.UpperTable (rows := rows) path outside clauses
      upper level (adviceRows := adviceRows) q)
  (cutoff : Nat)

def firstAnswer
    (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m))
    (raw : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q) :
    Option (HierarchicalDecoderTables.Answer
      (SourceQuestionLowerForms.slots path outside clauses q) upper level d) :=
  LowerCutDecoderForm.answer (SourceQuestionLowerForms.slots path outside clauses q)
    upper level d hbranch A (tables q) cutoff
    (LowerCutPair.first rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior)
      (SourceQuestionLowerForms.rawAtCut path outside clauses q raw))

def secondAnswer (direction : BucketSampler.Direction (rows (height + 1)))
    (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m))
    (raw : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q) :
    Option (HierarchicalDecoderTables.Answer
      (SourceQuestionLowerForms.slots path outside clauses q) upper level d) :=
  LowerCutDecoderForm.answer (SourceQuestionLowerForms.slots path outside clauses q)
    upper level d hbranch A (tables q) cutoff
    (LowerCutPair.second rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior)
      direction (SourceQuestionLowerForms.rawAtCut path outside clauses q raw))

variable
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := height) (t := t))
  (raw : (i : Fin (branch height)) →
    SourceChildKernel.Raw (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (t := t) rows clauses designated i)

def projection : ∀ s k, MixedSupport.Projection
    (SourceQuestionLowerForms.slots path outside clauses q s k)
    (CutSlotAssembly.fill path outside
      (SourceChildKernel.parentRightSlots rows clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) raw) s k) :=
  CutProjectionAssembly.fillProjection path outside
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceChildKernel.parentRightSlots rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw)

def globalRestricted (direction : BucketSampler.Direction (rows (height + 1))) : Bool :=
  let record := SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw
  BilinearCollisionTransfer.restrictedCollision
    ((firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      q record.2).map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d)))
    ((secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      direction q record.2).map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d)))
    (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
      (projection path outside clauses designated q choices raw)
      (HierarchicalLeftDecoder.LowerNode upper level d))))

end
end PerfectCompleteness.SourceQuestionCollisionTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionPhysicalCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPhysicalCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple
    (branch := branch) (n := height) (t := t))
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)
  (table : SourceQuestionLowerForms.UpperTable (rows := rows)
    path outside clauses upper level (adviceRows := adviceRows) q)

def rawEvent (flags : SourceProjectedTag.Flags (branch := branch) (n := height))
    (raw : CutChildGrouping.Raw
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (SourceProjectedTag.mixedInside clauses designated q choices flags) rows) : Bool :=
  LowerProjectedFiberAverage.collision
    (SourceQuestionPhysicalHigh.originalSlots path outside clauses q)
    (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
    (SourceQuestionPhysicalHigh.projection path outside clauses designated q choices flags)
    upper level hbranch d A cutoff table
    (LowerCutPair.arraysPair rows repeats path
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
      (SourceQuestionPhysicalHigh.exteriorAt path outside placeholder clauses designated
        q choices flags exterior) direction
      (SourceQuestionPairPullback.rawAtCut rows repeats path outside
        (SourceProjectedTag.mixedInside clauses designated q choices flags) raw))

end
end PerfectCompleteness.SourceQuestionPhysicalCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedRawMeeting
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalProjectedRawMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω)
  (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (v : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan) upper lower A
    (FixedRows.repeats plan) cut)

local instance rowSpaceFintype_r2d0309_8 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance valueFintype_r2d0309_3 : Fintype
    (Block (FixedRows.rows plan) upper ×
      HierarchicalMatrixTable.SideOutput (rows := FixedRows.rows plan) upper) :=
  Fintype.ofFinite _
local instance upperDualFintype_r2d0309_3 : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def meetingProbability : ℝ :=
  ((HierarchicalProjectedMeeting.leftLaw slots projected projection upper lowerLevel
    (HierarchicalProjectedRawPrediction.visibleBackground slots projected projection
      (FixedRows.rows plan) upper lower A (FixedRows.repeats plan) cut v)
    original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
    (HierarchicalProjectedRawPrediction.known projected (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)).product
    (RightDecoder.law projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (FixedRows.repeats plan) cut σ
      (OwnInputReference.readInput projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projected upper lower (FixedRows.repeats plan) cut) v)
      (tau (InitialParameters.useful δ) plan.density plan.order
        (FixedRows.rows plan (Nodes.height upper))))).probability
    (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap
      pair.1 = pair.2))

end
end PerfectCompleteness.HierarchicalProjectedRawMeeting

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedRawAverage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalProjectedRawAverage

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
  {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)

abbrev Raw := HierarchicalProjectedRawPrediction.Raw projected (FixedRows.rows plan) upper lower A
  (FixedRows.repeats plan) cut

abbrev Visible := HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan) upper lower A
  (FixedRows.repeats plan) cut

def law (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    FiniteDistribution (Raw plan projected upper lower A cut) :=
  OwnInputReference.rawLaw projected (FixedRows.rows plan) upper lower (LinearMap.ker A)
    (FixedRows.repeats plan) cut externalLaw

abbrev J := HierarchicalProjectedRawPrediction.rawJ slots projected projection (FixedRows.rows plan) upper lower lowerLevel
  original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
  (FixedRows.repeats plan) cut

abbrev prediction := HierarchicalProjectedRawPrediction.rawPrediction slots projected projection (FixedRows.rows plan) upper lower lowerLevel
  original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
  (FixedRows.repeats plan) cut a

def goodRecord (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (v : Visible plan projected upper lower A cut) : Bool :=
  PositiveFiberMass.goodRecord (law plan projected upper lower A cut externalLaw)
    (fun sample : Raw plan projected upper lower A cut => sample.2)
    (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)
    (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
    (rhoPred (InitialParameters.useful δ) plan.density) v

def goodEvent (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (sample : Raw plan projected upper lower A cut) : Bool :=
  J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
    goodRecord plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut
      externalLaw sample.2

abbrev meetingProbability :=
  HierarchicalProjectedRawMeeting.meetingProbability plan slots projected projection upper lower lowerLevel
    original originalArrays lowerEvent σ A a cut

def expectedMeeting (externalLaw : FiniteDistribution
    (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) : ℝ :=
  (law plan projected upper lower A cut externalLaw).expectation
    (fun sample => meetingProbability plan slots projected projection upper lower lowerLevel
      original originalArrays lowerEvent σ A a cut sample.2)

end
end PerfectCompleteness.HierarchicalProjectedRawAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedPredictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedPrediction

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows repeats : Nat → Nat} {n t : Nat} {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (lower : K → Nodes branch n)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block rows (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (κ : ℝ) (r : Nat) (ρ : ℝ)

local notation "S" => HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
  slots projected projection upper lowerLevel lower cut direction outer σ

def rawJ (sample : HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
    projected upper lower cut r) : Bool :=
  HierarchicalProjectedRawPrediction.rawJ slots (projected sample.2.1) (projection sample.2.1)
    rows upper (lower sample.2.1) lowerLevel (S).original (S).arrays
    (HierarchicalAdviceExperiment.lowerEvent S) κ σ ρ sample.1
    repeats (cut sample.2.1) sample.2.2

def rawPrediction
    (sample : HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      projected upper lower cut r) : Bool :=
  HierarchicalProjectedRawPrediction.rawPrediction slots (projected sample.2.1) (projection sample.2.1)
    rows upper (lower sample.2.1) lowerLevel (S).original (S).arrays
    (HierarchicalAdviceExperiment.lowerEvent S) κ σ ρ sample.1
    repeats (cut sample.2.1) (direction sample.2.1) sample.2.2


end
end PerfectCompleteness.HierarchicalProjectedPrediction



namespace PerfectCompleteness.HierarchicalProjectedAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Projected

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : K → Nodes branch plan.depth)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block (FixedRows.rows plan) (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

local notation "S" => HierarchicalProjectedExperiment.experiment
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  slots projected projection upper lowerLevel lower cut direction outer σ

abbrev RawSample := HierarchicalProjectedExperiment.RawSample
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  projected upper lower cut plan.order

def meetingProbability (sample : RawSample plan projected upper lower cut) : ℝ :=
  HierarchicalProjectedRawMeeting.meetingProbability plan slots (projected sample.2.1)
    (projection sample.2.1) upper (lower sample.2.1) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ sample.1
    (direction sample.2.1) (cut sample.2.1) sample.2.2.2

def expectedMeeting : ℝ :=
  (HierarchicalProjectedExperiment.rawLaw (rows := FixedRows.rows plan)
    (repeats := FixedRows.repeats plan) projected upper lower cut outer plan.order).expectation
      (meetingProbability plan slots projected projection upper lowerLevel lower cut direction outer σ)

def predictionDifference : ℝ :=
  (HierarchicalAdviceExperiment.originalLaw S plan.order).probability
      (HierarchicalAdviceExperiment.prediction S (useful δ) plan.order plan.density) -
    rhoPred (useful δ) plan.density *
      (HierarchicalAdviceExperiment.originalLaw S plan.order).probability
        (fun x => HierarchicalAdviceExperiment.J S (useful δ) plan.order plan.density
          (HierarchicalAdviceExperiment.observe S plan.order x))

end Projected


end
end PerfectCompleteness.HierarchicalProjectedAverage



namespace PerfectCompleteness.HierarchicalProjectedOuterAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ)

variable {branch : Nat → Nat} {t : Nat} {O : Type*} [Fintype O]
  {K : O → Type*} [∀ o, Fintype (K o)]
  (slots : O → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projected : (o : O) → K o → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ o k s j, MixedSupport.Projection (slots o s j) (projected o k s j))
  (upper : O → Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : (o : O) → K o → Nodes branch plan.depth)
  (cut : ∀ o k, OwnInputReference.Cut (upper o) (lower o k))
  (direction : ∀ o k, Block (FixedRows.rows plan) (lower o k))
  (inner : (o : O) → FiniteDistribution (K o))
  (outer : FiniteDistribution O)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

abbrev experiment (o : O) :=
  HierarchicalProjectedExperiment.experiment
    (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
    (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
    (direction o) (inner o) σ

local notation "S" => experiment plan slots projected projection upper lowerLevel lower cut direction inner σ

def expectedMeeting : ℝ :=
  outer.expectation (fun o => HierarchicalProjectedAverage.expectedMeeting plan
    (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
    (direction o) (inner o) σ)

def predictionDifference : ℝ :=
  (HierarchicalAdviceFamily.originalLaw S outer plan.order).probability
      (HierarchicalAdviceFamily.prediction S (useful δ) plan.order plan.density) -
    rhoPred (useful δ) plan.density *
      (HierarchicalAdviceFamily.originalLaw S outer plan.order).probability
        (fun x => HierarchicalAdviceFamily.J S (useful δ) plan.order plan.density
          (HierarchicalAdviceFamily.observe S plan.order x))

end
end PerfectCompleteness.HierarchicalProjectedOuterAverage



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedMeetingTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedMeetingTransport

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {Sample : OriginalDecoderMark.SlotFamily branch plan.depth t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch (FixedRows.rows plan) plan.depth t Sample)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (slots projected : Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)
  (threshold : ℝ)
  (visible : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan)
    upper lower A (FixedRows.repeats plan) cut)

local instance physicalLeftFintype_r2d0309_1 {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def familyMeetingProbability : ℝ :=
  ((HierarchicalProjectedMeeting.leftLaw slots projected projection upper lowerLevel
    (HierarchicalProjectedRawPrediction.visibleBackground slots projected projection
      (FixedRows.rows plan) upper lower A (FixedRows.repeats plan) cut visible)
    (F.original slots) (F.arrays slots) (F.lowerEvent slots) (InitialParameters.useful δ)
    σ plan.density A
    (HierarchicalProjectedRawPrediction.known projected (FixedRows.rows plan)
      upper lower A (FixedRows.repeats plan) cut visible)).product
    (RightDecoder.law projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (FixedRows.repeats plan) cut σ
      (OwnInputReference.readInput projected (FixedRows.rows plan) upper lower
        (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projected upper lower (FixedRows.repeats plan) cut)
        visible) threshold)).probability
    (fun answer => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap
      answer.1 = answer.2))

end
end PerfectCompleteness.ProjectedMeetingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedChoices
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedChoices

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m v : Nat}

abbrev Positions :=
  SourceQuestionPositionSplit.ChildPositions (branch := branch) (n := n) (t := t)

abbrev Choices :=
  ProjectedCutChoices.Choices (Z := fun _ : Fin (branch n) =>
    Positions (branch := branch) (n := n) (t := t))

def tagEquiv : Choices (branch := branch) (n := n) (t := t) ≃
    SourceProjectedTag.Tag (branch := branch) (n := n) (t := t) where
  toFun choices := (fun child => (choices child).2, fun child => (choices child).1)
  invFun tag child := (tag.2 child, tag.1 child)
  left_inv _ := rfl
  right_inv _ := rfl

def choiceLaw (_child : Fin (branch n)) :
    FiniteDistribution (Positions (branch := branch) (n := n) (t := t)) :=
  FiniteDistribution.uniform _

variable (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)

def projected (child : Fin (branch n))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  fun leaf a => SlotProjectedExperiment.selectSlot (slots (child, leaf) a) (positions leaf a)

def projection : ∀ child positions leaf a,
    MixedSupport.Projection (childSlots slots child leaf a)
      (projected slots child positions leaf a) :=
  fun child positions leaf a =>
    SlotProjectedExperiment.selectProjection (slots (child, leaf) a) (positions leaf a)

end
end PerfectCompleteness.SourceProjectedChoices

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedArrays
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedArrays

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

theorem nativeSlots_eq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : StoppedProjectedExperiment.PhysicalBase
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    SourcePhysicalTapeLaw.nativeSlots
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows base))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o base) =
      StoppedProjectedExperiment.nativeSlots clauses o := by
  unfold SourcePhysicalTapeLaw.nativeSlots StoppedProjectedExperiment.physicalSources
  rw [SourceProjectedTag.parentLeftSlots_sources]
  exact StoppedProjectedExperiment.fill_native clauses rows hupper hij o
    (StoppedProjectedExperiment.baseTag rows base)

abbrev physicalArrays
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :=
  SourcePhysicalWholeLaw.observeLeft rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows sample.1))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1)))
    clauses designated
    (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1) sample.2

end
end PerfectCompleteness.StoppedProjectedArrays

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedContext
attribute [-simp] _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedContext

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t m : Nat}

abbrev Sample (rows : Nat → Nat) :=
  StoppedSharedSampler.Context branch n t m i rows ×
    SourceProjectedTag.Tag (branch := branch) (n := i) (t := t)

abbrev SplitSample (rows : Nat → Nat) :=
  StoppedProjectedExperiment.Outer (branch := branch) (n := n) (j := j) (t := t) (m := m) ×
    StoppedProjectedExperiment.Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows

variable (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)

def splitEquiv : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows ≃
    SplitSample (branch := branch) (n := n) (i := i) (j := j) (t := t) (m := m) rows where
  toFun x :=
    let prefixes := GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le) hupper x.1.2.1
    ((x.1.1, prefixes.1), (prefixes.2, (x.2, x.1.2.2)))
  invFun x :=
    ((x.1.1, ((GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le) hupper).symm
      (x.1.2, x.2.1), x.2.2.2)), x.2.2.1)
  left_inv x := by
    rcases x with ⟨⟨q, pref, directions⟩, tag⟩
    exact congrArg (fun pref => ((q, pref, directions), tag))
      ((GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le) hupper).symm_apply_apply pref)
  right_inv x := by
    rcases x with ⟨⟨q, upper⟩, lower, tag, directions⟩
    simp only [Equiv.apply_symm_apply]

@[simp] theorem questions_split
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (splitEquiv rows hupper hij x).1.1 = x.1.1 := rfl

@[simp] theorem tag_split
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (splitEquiv rows hupper hij x).2.2.1 = x.2 := rfl

@[simp] theorem directions_split
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (splitEquiv rows hupper hij x).2.2.2 = x.1.2.2 := rfl

end
end PerfectCompleteness.StoppedProjectedContext

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedProjectedGlobalLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedGlobalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j) (hi : i + 1 ≤ n)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)

abbrev ExperimentSample :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)

variable [NeZero m] (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :=
  StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ o

def experimentLaw : FiniteDistribution (ExperimentSample (t := t) clauses rows repeats hupper hij designated) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original)

end
end PerfectCompleteness.StoppedProjectedGlobalLaw

end

section

namespace PerfectCompleteness.StoppedProjectedPhysicalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)

abbrev Sample :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o

def read (sample : Sample (t := t) clauses rows repeats hupper hij designated) :
    StoppedProjectedGlobalLaw.ExperimentSample (t := t) clauses rows repeats hupper hij designated :=
  ⟨sample.1, StoppedProjectedExperiment.physicalExperimentRead
    clauses rows repeats hupper hij designated sample.1 sample.2⟩

variable [NeZero m]
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def law : FiniteDistribution (Sample (t := t) clauses rows repeats hupper hij designated) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag)

end
end PerfectCompleteness.StoppedProjectedPhysicalLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedOldRecord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedOldRecord

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance fixedBackgroundFintype_r2d0309_1 (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := rows) slots upper
abbrev OldRecord :=
  HierarchicalMatrixTable.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o) ×
    HierarchicalMatrixTable.Matrix (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)

def arrayRecord (arrays : Arrays (StoppedProjectedExperiment.nativeSlots clauses o) rows) :
    OldRecord clauses rows hupper o :=
  (HierarchicalMatrixTable.backgroundOf (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o) arrays,
    NodeEmbedding.matrix arrays (StoppedProjectedExperiment.upper hupper o))

end
end PerfectCompleteness.StoppedProjectedOldRecord

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedPhysicalAdvice
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedPhysicalAdvice

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

abbrev physicalSampleFintype
    {branch : Nat → Nat} {n i j t v m : Nat}
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
    (designated : Fin (branch i) → Slots branch i)
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    Fintype (StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o) :=
  inferInstance

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)

abbrev Advice (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :=
  ManyGoodRows.RowMap (Block rows (StoppedProjectedExperiment.upper hupper o)) r

local instance adviceFintype
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    Fintype (Advice rows hupper o r) := linearMapFintype

abbrev Sample (r : Nat) :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    (StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o ×
      Advice rows hupper o r)

abbrev RawSample (r : Nat) :=
  (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) ×
    HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) r

local instance physicalAdviceFintype
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    Fintype (StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o ×
      Advice rows hupper o r) := by
  let : Fintype (StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :=
    physicalSampleFintype clauses rows repeats hupper hij designated o
  infer_instance

local instance rawFiberFintype
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) r) := by
  let : (A : Advice rows hupper o r) →
      (k : StoppedProjectedExperiment.Inner
        (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) →
      Fintype (OwnInputReference.RawSample
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k) rows
        (StoppedProjectedExperiment.upper hupper o) (StoppedProjectedExperiment.lower rows hupper hij o k)
        (LinearMap.ker A) repeats (StoppedProjectedExperiment.cut rows hupper hij o k)) :=
    fun A k => OwnInputReference.rawSampleFintype
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k) rows
      (StoppedProjectedExperiment.upper hupper o) (StoppedProjectedExperiment.lower rows hupper hij o k)
      (LinearMap.ker A) repeats (StoppedProjectedExperiment.cut rows hupper hij o k)
  let : (A : Advice rows hupper o r) →
      Fintype ((k : StoppedProjectedExperiment.Inner
        (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) ×
        OwnInputReference.RawSample
          (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k) rows
          (StoppedProjectedExperiment.upper hupper o) (StoppedProjectedExperiment.lower rows hupper hij o k)
          (LinearMap.ker A) repeats (StoppedProjectedExperiment.cut rows hupper hij o k)) :=
    fun _ => Sigma.instFintype
  exact Sigma.instFintype

def read (r : Nat) (sample : Sample (t := t) clauses rows repeats hupper hij designated r) :
    RawSample (t := t) clauses rows repeats hupper hij designated r :=
  ⟨sample.1, HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated sample.1)
    (StoppedProjectedExperiment.upper hupper sample.1)
    (StoppedProjectedExperiment.lower rows hupper hij sample.1)
    (StoppedProjectedExperiment.cut rows hupper hij sample.1) r
    (StoppedProjectedExperiment.physicalExperimentRead clauses rows repeats hupper hij designated
      sample.1 sample.2.1, sample.2.2)⟩

variable [NeZero m]
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def law (r : Nat) : FiniteDistribution (Sample (t := t) clauses rows repeats hupper hij designated r) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).product
        (FiniteDistribution.uniform (Advice rows hupper o r)))

def rawLaw (r : Nat) : FiniteDistribution (RawSample (t := t) clauses rows repeats hupper hij designated r) :=
  CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)
      (StoppedProjectedExperiment.innerLaw rows hij
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) r)

end
end PerfectCompleteness.StoppedProjectedPhysicalAdvice

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedUsefulEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulEvent

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Outer := StoppedProjectedExperiment.Outer (branch := branch) (n := n)
  (j := j) (t := t) (m := m)
abbrev Inner := StoppedProjectedExperiment.Inner (branch := branch) (n := n)
  (i := i) (j := j) (t := t) rows

abbrev chosen (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  StoppedPathHead.child hij (StoppedProjectedExperiment.lowerPath rows hij k)

end
end PerfectCompleteness.StoppedProjectedUsefulEvent

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceEncoding

open UniqueGamesTheorem.Foundations Complexity Target

theorem body_length_le {n : Nat} (clauses : List (Clause n)) (first maximum : Nat)
    (indices : first + clauses.length ≤ maximum) :
    (body first clauses).length ≤ clauses.length * (maximum + 1 + 3 * (n + 2)) := by
  induction clauses generalizing first with
  | nil => simp
  | cons clause clauses ih =>
      have tail := ih (first + 1) (by simp only [List.length_cons] at indices; omega)
      have head := clauseBits_length_le clause
      rw [body_cons, recordBits_eq]
      simp only [List.length_append, encodeWord_length, List.length_cons]
      nlinarith

end PerfectCompleteness.SourceOccurrenceEncoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceLoopMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceLoopMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

variable (tape : Fin 5 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem bodyTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (remaining first : Nat) (output : List Bool) (scratchEmpty : base (tape 3) = []) :
    (advance (TM2.step program))^[bodySteps first clause]
      (some ⟨some (labels .guard), clean ambient,
        loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
          (remaining + 1) first output⟩) =
      some ⟨some (labels .guard), clean ambient,
        loopTapes tape base suffix remaining (first + 1)
          ((SourceOccurrenceEncoding.recordBits first clause).reverse ++ output)⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let input := encodeWords (clauseWords clause) ++ suffix
  let indexOutput := (encodeWord first).reverse ++ output
  let clauseOutput := (encodeWords (clauseWords clause)).reverse ++ indexOutput
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), clean ambient,
        loopTapes tape base input (remaining + 1) first output⟩) =
      some ⟨some (labels (.index SourceOccurrenceIndexMachine.main)), clean ambient,
        loopTapes tape base input remaining first output⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      guardStep tape distinct labels done rejected program atLabels base ambient
        input remaining first output
  have index := SourceOccurrenceIndexMachine.indexTrace (indexTapes tape)
    (indexTapes_injective tape distinct) (fun l => labels (.index l))
    (some (labels (.field 0))) program (fun l => atLabels (.index l))
    (loopTapes tape base input remaining first output) ambient first
    (by simp [indexTapes, indexMap, loopTapes, hd])
    (by simp [indexTapes, indexMap, loopTapes, hd, scratchEmpty])
  rw [show indexTapes tape 2 = tape 4 from rfl, loopTapes_output, update_output] at index
  have copied : (advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
      (some ⟨some (labels (.field 0)), clean ambient,
        loopTapes tape base input remaining first indexOutput⟩) =
      some ⟨some (labels .tally), clean ambient,
        loopTapes tape base suffix remaining first clauseOutput⟩ := by
    have h := UnaryBlockCopyMachine.listTrace (tape 0) (tape 4) (hd 0 4 (by decide))
      (fun slot => labels (.field slot)) (some (labels .tally)) rejected program
      (fun slot => atLabels (.field slot))
      (loopTapes tape base input remaining first indexOutput) ambient
      (clauseWords clause) (by simp) suffix indexOutput none
    simpa only [tapesAt_loop tape distinct, clean, SourceOccurrenceIndexMachine.clean,
      input, clauseOutput] using h
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient,
        loopTapes tape base suffix remaining first clauseOutput⟩) =
      some ⟨some (labels .guard), clean ambient,
        loopTapes tape base suffix remaining (first + 1) clauseOutput⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done rejected program atLabels base ambient
        suffix remaining first clauseOutput
  have full := joinTrace (joinTrace (joinTrace guard index) copied) tally
  simpa only [bodySteps, input, clauseOutput, indexOutput,
    SourceOccurrenceEncoding.recordBits_eq, List.reverse_append, List.append_assoc] using full

theorem loopTrace {n : Nat} (clauses : List (Target.Clause n)) (suffix : List Bool)
    (first : Nat) (output : List Bool) (scratchEmpty : base (tape 3) = []) :
    (advance (TM2.step program))^[steps first clauses]
      (some ⟨some (labels .guard), clean ambient,
        loopTapes tape base (encodeWords (clauses.flatMap clauseWords) ++ suffix)
          clauses.length first output⟩) =
      some ⟨done, clean ambient,
        loopTapes tape base suffix 0 (first + clauses.length)
          ((SourceOccurrenceEncoding.body first clauses).reverse ++ output)⟩ := by
  induction clauses generalizing first output with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, List.flatMap_nil, encodeWords,
        List.nil_append, List.length_nil, Nat.add_zero, SourceOccurrenceEncoding.body_nil,
        List.reverse_nil] using
        emptyStep tape distinct labels done rejected program atLabels base ambient suffix first output
  | cons clause clauses ih =>
      have head := bodyTrace tape distinct labels done rejected program atLabels base ambient clause
        (encodeWords (clauses.flatMap clauseWords) ++ suffix) clauses.length first output scratchEmpty
      have tail := ih (first + 1)
        ((SourceOccurrenceEncoding.recordBits first clause).reverse ++ output)
      have full := joinTrace head tail
      have indexEq : first + 1 + clauses.length = first + (clauses.length + 1) := by omega
      simpa only [steps, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons, indexEq, SourceOccurrenceEncoding.body_cons, List.reverse_append] using full

end Program

end PerfectCompleteness.SourceOccurrenceLoopMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

theorem loopTrace (formula : Formula) :
    (advance machine.step)^[SourceOccurrenceLoopMachine.steps 0 formula.clauses]
      (some (cfg (some (.loop .guard)) (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] [])) =
      some (cfg (some .restore) [] (List.replicate formula.variables true) []
        (List.replicate formula.clauses.length true)
        (SourceOccurrenceEncoding.body 0 formula.clauses).reverse []) := by
  change (advance (TM2.step program))^[SourceOccurrenceLoopMachine.steps 0 formula.clauses]
    (some ⟨some (.loop .guard), ((), none),
      tapes (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] []⟩) =
    some ⟨some .restore, ((), none),
      tapes [] (List.replicate formula.variables true) []
        (List.replicate formula.clauses.length true)
        (SourceOccurrenceEncoding.body 0 formula.clauses).reverse []⟩
  have updated (input : List Bool) (remaining first : Nat) (output : List Bool) :
      SourceOccurrenceLoopMachine.loopTapes loopTapes
        (tapes [] (List.replicate formula.variables true) [] [] [] [])
        input remaining first output =
      tapes input (List.replicate formula.variables true) (List.replicate remaining true)
        (List.replicate first true) output [] := by
    funext k
    fin_cases k <;> simp [SourceOccurrenceLoopMachine.loopTapes, loopTapes, tapes]
  have run := SourceOccurrenceLoopMachine.loopTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes [] (List.replicate formula.variables true) [] [] [] []) () formula.clauses [] 0 [] rfl
  simp only [updated, List.append_nil, List.replicate_zero, Nat.zero_add] at run
  exact run

theorem occurrenceTrace (formula : Formula) :
    (advance machine.step)^[steps formula] (some (initList machine (formulaBits formula))) =
      some (haltList machine (SourceOccurrenceEncoding.bits formula)) := by
  have first := headersTrace formula.variables formula.clauses.length
    (encodeWords (formula.clauses.flatMap clauseWords))
  have second := loopTrace formula
  have third := restoreTrace (List.replicate formula.variables true)
    (List.replicate formula.clauses.length true) (SourceOccurrenceEncoding.body 0 formula.clauses)
  have fourth := headerOutputTrace formula.variables formula.clauses.length
    (SourceOccurrenceEncoding.body 0 formula.clauses)
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  simpa only [steps, initList_eq, haltList_eq, formulaBits_eq,
    SourceOccurrenceEncoding.bits_eq] using full

theorem steps_le (formula : Formula) :
    steps formula ≤ timePolynomial.eval (formulaBits formula).length := by
  let B := (formulaBits formula).length
  have variablesBound : formula.variables ≤ B := (header_counts_le formula).1
  have clausesBound : formula.clauses.length ≤ B := (header_counts_le formula).2
  have loopBound := SourceOccurrenceLoopMachine.steps_le 0 formula.clauses.length
    formula.clauses (by omega)
  have loopUniform : SourceOccurrenceLoopMachine.steps 0 formula.clauses ≤
      B * (5 * B + 11) + 1 :=
    loopBound.trans (Nat.add_le_add_right
      (Nat.mul_le_mul clausesBound (by omega)) 1)
  have bodyBound := SourceOccurrenceEncoding.body_length_le formula.clauses 0
    formula.clauses.length (by omega)
  have bodyUniform : (SourceOccurrenceEncoding.body 0 formula.clauses).length ≤
      B * (4 * B + 7) :=
    bodyBound.trans (Nat.mul_le_mul clausesBound (by omega))
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  change steps formula ≤ 100 * (B + 1) ^ 2
  unfold steps
  nlinarith

def outputsInTime (formula : Formula) :
    TM2OutputsInTime machine (formulaBits formula)
      (some (SourceOccurrenceEncoding.bits formula))
      (timePolynomial.eval (formulaBits formula).length) where
  steps := steps formula
  evals_in_steps := occurrenceTrace formula
  steps_le_m := steps_le formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits SourceOccurrenceEncoding.bits (id : Formula → Formula) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((SourceOccurrenceEncoding.bits formula).map id))
      (timePolynomial.eval (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end PerfectCompleteness.SourceOccurrenceMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceProducerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedSourceInput


open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

theorem raw_satisfiable_iff (input : List Bool) :
    (raw input).formula.Satisfiable ↔ BinaryLanguage.language input :=
  PCPSourceMachine.rawSource_satisfiable_iff input

end
end PerfectCompleteness.NormalizedSourceInput

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_NormalizedTarget
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedTarget


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

variable (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ

def outputBits (input : NormalizedSourceInput.Input) : List Bool :=
  Encoding.gameBits (construct (t := t) rows repeats hn hbranch hrows δ input)

theorem edge_count (input : NormalizedSourceInput.Input) :
    (construct (t := t) rows repeats hn hbranch hrows δ input).edges.length =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q *
        (NormalizedSourceInput.clauseCount input) ^ TreeCanonical.locationCount branch n t :=
  ExactPreliminaryTarget.edge_count (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ

local instance leftVertex_fintype (input : NormalizedSourceInput.Input) :
    Fintype (CanonicalGame.LeftVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) := Fintype.ofFinite _

local instance rightVertex_fintype (input : NormalizedSourceInput.Input) :
    Fintype (CanonicalGame.RightVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) := Fintype.ofFinite _

local instance leftLabel_fintype (input : NormalizedSourceInput.Input)
    (x : CanonicalGame.LeftVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) :
    Fintype (CanonicalGame.LeftLabel (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats) x) := Fintype.ofFinite _

local instance rightLabel_fintype (input : NormalizedSourceInput.Input)
    (y : CanonicalGame.RightVertex (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats)) :
    Fintype (CanonicalGame.RightLabel (FinitePreliminaryCompletion.blockFamily
      (NormalizedSourceInput.clauses input) branch n t rows repeats) y) := Fintype.ofFinite _

theorem value_le (input : NormalizedSourceInput.Input) (hδ : 0 < δ) :
    (construct (t := t) rows repeats hn hbranch hrows δ input).value ≤
      (PreliminarySampler.game (NormalizedSourceInput.clauses input)
        branch n t rows repeats hn hbranch hrows).value + (δ : ℝ) / 3 :=
  ExactPreliminaryTarget.value_le (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ hδ

theorem perfectlyComplete (input : NormalizedSourceInput.Input)
    (satisfiable : input.formula.Satisfiable) :
    PerfectlyComplete (construct (t := t) rows repeats hn hbranch hrows δ input) := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  apply ExactPreliminaryTarget.perfectlyComplete (t := t)
    (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ assignment
  intro occurrence
  exact satisfies _ (List.getElem_mem occurrence.isLt)

theorem outputBits_length_le (input : NormalizedSourceInput.Input) :
    let N := (construct (t := t) rows repeats hn hbranch hrows δ input).edges.length
    (outputBits (t := t) rows repeats hn hbranch hrows δ input).length ≤
      2 * N + q + N + 4 + N * (2 * N + 2 * q * q + 2 * q + 2) :=
  ExactPreliminaryTarget.encoding_length_le (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ

end
end PerfectCompleteness.NormalizedTarget

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizedTargetTapeBound
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedTargetTapeBound


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
  (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "clauses" => NormalizedSourceInput.clauses input
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "target" => NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ input
local notation "E" => List.length order

def finalData : SignedTupleBodyMachine.Data width :=
  SignedTupleSemantics.dataOfPrefix (t := t) clauses rows repeats hn hbranch hrows δ order []

def finalTapes : SignedTupleLayout.Tape width (Fin 4) → List Bool :=
  ExactTargetOdometer.nativeTapes (t := t) input
    (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)
    (finalData (t := t) rows repeats hn hbranch hrows δ input) (fun _ => [])

theorem order_length_eq_edges : E = (target).edges.length := by
  exact (CompletedVisitOrder.completedOrder_length
    (t := t) clauses rows repeats hn hbranch hrows δ).trans
    (NormalizedTarget.edge_count (t := t) rows repeats hn hbranch hrows δ input).symm

theorem reversedOutput_length_le_output :
    (finalData (t := t) rows repeats hn hbranch hrows δ input).reversedOutput.length ≤
      (NormalizedTarget.outputBits (t := t) rows repeats hn hbranch hrows δ input).length := by
  have encoded := ExactTargetOnlineEncoding.target_gameBits (t := t)
    clauses rows repeats hn hbranch hrows δ
  change (Encoding.gameBits target) = _ at encoded
  change _ ≤ (Encoding.gameBits target).length
  rw [encoded]
  simp only [finalData, SignedTupleSemantics.dataOfPrefix, List.append_nil,
    List.length_reverse, List.length_append]
  omega

theorem reversedOutput_length_le :
    (finalData (t := t) rows repeats hn hbranch hrows δ input).reversedOutput.length ≤
      TargetTapeEnvelope.outputBound q E := by
  have h := (reversedOutput_length_le_output (t := t) rows repeats hn hbranch hrows δ input).trans
    (NormalizedTarget.outputBits_length_le (t := t) rows repeats hn hbranch hrows δ input)
  rw [← order_length_eq_edges (t := t) rows repeats hn hbranch hrows δ input] at h
  exact h

end
end PerfectCompleteness.NormalizedTargetTapeBound

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_NormalizedTargetInitialization
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedTargetInitialization


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open scoped Classical

noncomputable section

abbrev Tape (width : Nat) := SignedTupleLayout.Tape width (Fin 4)
abbrev Alphabet {width : Nat} (_ : Tape width) := Bool

variable {width : Nat}

def countTape : Fin 4 → Tape width
  | 0 => .source .table
  | 1 => .extra 1
  | 2 => .extra 2
  | 3 => .extra 0

theorem countTape_injective : Function.Injective (countTape (width := width)) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp [countTape] at same ⊢

def currents (width : Nat) : List (Tape width) := List.ofFn SignedTupleLayout.Tape.current
def remaining (width : Nat) : List (Tape width) := List.ofFn SignedTupleLayout.Tape.remaining

theorem destinations_nodup (width : Nat) : (currents width ++ remaining width).Nodup := by
  unfold currents remaining
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_ofFn.mpr
    intro i j same
    simpa using same
  · apply List.nodup_ofFn.mpr
    intro i j same
    simpa using same
  · intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    intro same
    cases same

theorem count_not_destination :
    (SignedTupleLayout.Tape.extra 0 : Tape width) ∉ currents width ++ remaining width := by
  simp [currents, remaining, List.mem_ofFn]

variable {Λ A : Type}

def instruction (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (width := width)) Λ (State A)
  | .seed => .push (.extra 0) (fun _ => false)
      (.push .edgeCount (fun _ => false)
        (.load (fun state => clean state.1)
          (.goto (fun _ => labels (.count SourceClauseCountMachine.main)))))
  | .count label => SourceClauseCountMachine.instruction countTape
      (fun l => labels (.count l)) (some (labels (.tuple .seed))) rejected label
  | .tuple label => TupleInitializationMachine.instruction (.extra 0)
      (currents width) (remaining width) (fun l => labels (.tuple l)) done label

def inputTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool
  | .source .table => NormalizedSourceInput.bits input
  | _ => []

def seededTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool :=
  Function.update (Function.update (inputTapes input) (.extra 0) [false]) .edgeCount [false]

def countedTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool :=
  Function.update (seededTapes input) (.extra 0)
    (encodeWord (NormalizedSourceInput.clauseCount input))

def zeroDigits (input : NormalizedSourceInput.Input) :
    Fin width → Fin (NormalizedSourceInput.clauseCount input) :=
  fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩

def readyTapes (input : NormalizedSourceInput.Input) : Tape width → List Bool :=
  Function.update (ExactTargetOdometer.baseTapes input (zeroDigits input) (fun _ => []))
    .edgeCount (encodeWord 0)

@[simp] theorem seeded_count (input : NormalizedSourceInput.Input) :
    seededTapes (width := width) input (.extra 0) = [false] := by
  simp [seededTapes]

@[simp] theorem counted_count (input : NormalizedSourceInput.Input) :
    countedTapes (width := width) input (.extra 0) =
      encodeWord (NormalizedSourceInput.clauseCount input) := by
  simp [countedTapes]

theorem initializedTapes_eq_ready (input : NormalizedSourceInput.Input) :
    TupleInitializationMachine.initializedTapes (.extra 0) (currents width) (remaining width)
        (countedTapes input) (NormalizedSourceInput.clauseCount input - 1) [] =
      readyTapes input := by
  funext key
  cases key with
  | source source =>
      cases source <;>
        simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
          currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
          readyTapes, ExactTargetOdometer.baseTapes]
  | current position =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes, zeroDigits, encodeWord]
  | remaining position =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes, zeroDigits, encodeWord]
  | encodedVariable position slot =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes]
  | adapterScratch =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes]
  | edgeWork slot =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
        readyTapes, ExactTargetOdometer.baseTapes]
  | edgeCount =>
      simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
        currents, remaining, List.mem_ofFn, countedTapes, seededTapes,
        readyTapes, encodeWord]
  | extra slot =>
      fin_cases slot <;>
        simp [TupleInitializationMachine.initializedTapes, TupleInitializationMachine.prefixOn,
          currents, remaining, List.mem_ofFn, countedTapes, seededTapes, inputTapes,
          readyTapes, ExactTargetOdometer.baseTapes]

@[simp] theorem ready_table (input : NormalizedSourceInput.Input) :
    readyTapes (width := width) input (.source .table) = NormalizedSourceInput.bits input := by
  simp [readyTapes, ExactTargetOdometer.baseTapes]

@[simp] theorem ready_current (input : NormalizedSourceInput.Input) (position : Fin width) :
    readyTapes input (.current position) = encodeWord 0 := by
  simp [readyTapes, ExactTargetOdometer.baseTapes, zeroDigits]

@[simp] theorem ready_remaining (input : NormalizedSourceInput.Input) (position : Fin width) :
    readyTapes input (.remaining position) =
      encodeWord (NormalizedSourceInput.clauseCount input - 1) := by
  simp [readyTapes, ExactTargetOdometer.baseTapes, zeroDigits]

@[simp] theorem ready_extra (input : NormalizedSourceInput.Input) (slot : Fin 4) :
    readyTapes (width := width) input (.extra slot) = [] := by
  simp [readyTapes, ExactTargetOdometer.baseTapes]

theorem ready_eq_native {branch : Nat → Nat} {n t : Nat}
    (input : NormalizedSourceInput.Input) :
    readyTapes (width := TreeCanonical.locationCount branch n t) input =
      ExactTargetOdometer.nativeTapes (branch := branch) (n := n) (t := t)
        input (zeroDigits input) ⟨[], [], [], 0⟩ (fun _ : Fin 4 => []) := by
  funext key
  cases key with
  | source source =>
      cases source <;>
        simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes,
          ExactTargetOdometer.baseTapes]
  | current position =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | remaining position =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | encodedVariable position slot =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | adapterScratch =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | edgeWork slot =>
      fin_cases slot <;>
        simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes,
          ExactTargetOdometer.baseTapes, CanonicalVertexNames.tokens]
  | edgeCount =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
  | extra slot =>
      simp [readyTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]

variable (labels : Label → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction labels done rejected label)

include atLabels in
theorem seedStep (input : NormalizedSourceInput.Input) (ambient : A) (register : Option Bool) :
    TM2.step program ⟨some (labels .seed), (ambient, register), inputTapes input⟩ =
      some ⟨some (labels (.count SourceClauseCountMachine.main)), clean ambient, seededTapes input⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [atLabels .seed]
  simp [instruction, TM2.stepAux, seededTapes, inputTapes, clean]

def initializeExactInTime (input : NormalizedSourceInput.Input)
    (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), (ambient, register), inputTapes input⟩
      (some ⟨done, clean ambient, readyTapes input⟩)
      (1 + 3 * ((NormalizedSourceInput.bits input).length + 1) +
        (NormalizedSourceInput.clauseCount input + 1)) := by
  have seeded : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), (ambient, register), inputTapes input⟩
      (some ⟨some (labels (.count SourceClauseCountMachine.main)),
        clean ambient, seededTapes input⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    exact seedStep labels done rejected program atLabels input ambient register
  have counted : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.count SourceClauseCountMachine.main)), clean ambient, seededTapes input⟩
      (some ⟨some (labels (.tuple .seed)), clean ambient, countedTapes input⟩)
      (3 * ((NormalizedSourceInput.bits input).length + 1)) := by
    have run := SourceClauseCountMachine.countInTime countTape countTape_injective
      (fun label => labels (.count label)) (some (labels (.tuple .seed))) rejected
      program (fun label => atLabels (.count label)) (seededTapes input) ambient input.formula
      (by simp [countTape, seededTapes, inputTapes, NormalizedSourceInput.bits])
      (by simp [countTape, seededTapes, inputTapes])
      (by simp [countTape, seededTapes, inputTapes])
    simpa only [SourceClauseCountMachine.clean, clean, countTape, countedTapes, seeded_count,
      NormalizedSourceInput.bits, NormalizedSourceInput.clauseCount, encodeWord] using run
  have initialized : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.tuple .seed)), clean ambient, countedTapes input⟩
      (some ⟨done, clean ambient, readyTapes input⟩)
      (NormalizedSourceInput.clauseCount input + 1) := by
    have run := TupleInitializationMachine.initializeInTime (σ := A)
      (SignedTupleLayout.Tape.extra 0 : Tape width)
      (currents width) (remaining width) (destinations_nodup width) count_not_destination
      (fun label => labels (.tuple label)) done program
      (fun label => by simpa only [instruction] using atLabels (.tuple label))
      (countedTapes input) ambient (NormalizedSourceInput.clauseCount input)
      (NormalizedSourceInput.clauseCount_positive input) []
      (by simp only [counted_count, List.append_nil])
    simpa only [TupleInitializationMachine.clean, clean, initializedTapes_eq_ready] using run
  have first := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seeded counted
  have full := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first initialized
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem count_length_le (input : NormalizedSourceInput.Input) :
    NormalizedSourceInput.clauseCount input + 1 ≤ (NormalizedSourceInput.bits input).length := by
  rw [NormalizedSourceInput.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

def initializeInTime (input : NormalizedSourceInput.Input) (ambient : A) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .seed), (ambient, register), inputTapes input⟩
      (some ⟨done, clean ambient, readyTapes input⟩)
      (4 * ((NormalizedSourceInput.bits input).length + 1)) := by
  let run := initializeExactInTime labels done rejected program atLabels input ambient register
  refine
    { steps := run.steps
      evals_in_steps := run.evals_in_steps
      steps_le_m := run.steps_le_m.trans ?_ }
  have bounded := count_length_le input
  omega

end
end PerfectCompleteness.NormalizedTargetInitialization

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizedTargetMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedTargetMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

abbrev Tape (branch : Nat → Nat) (n t : Nat) :=
  SignedTupleLayout.Tape (TreeCanonical.locationCount branch n t) (Fin 4)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "Arena" => Tape branch n t

def tapeEnumeration (branch : Nat → Nat) (n t : Nat) :
    Fin (Fintype.card (Tape branch n t)) ≃ Tape branch n t :=
  (Fintype.equivFin (Tape branch n t)).symm

def finalizerTape (branch : Nat → Nat) (n t : Nat) : Fin 4 → Tape branch n t
  | 0 => .edgeWork 7
  | 1 => .edgeCount
  | 2 => .extra 2
  | 3 => .extra 3

theorem finalizerTape_injective (branch : Nat → Nat) (n t : Nat) :
    Function.Injective (finalizerTape branch n t) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp [finalizerTape] at same ⊢

variable (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "Desc" => SignedCompletionSchedule.Descriptor
  (rows := rows) (repeats := repeats)
  (CanonicalLocalCompletion.alphabet_positive width δ)
  (CanonicalLocalCompletion.partitionWidth_le_alphabet width δ)
local notation "Native" => ExactTargetOdometer.NativeLabel
  (branch := branch) (n := n) (t := t) rows repeats hn hbranch hrows δ (Fin 4)
local notation "Final" => TargetFinalizeMachine.Labels
  (tapeEnumeration branch n t) (finalizerTape branch n t 3)

abbrev Control := ExactTargetOdometer.Control (branch := branch) (n := n) (t := t)
  rows repeats δ

abbrev Ambient := ExactTargetOdometer.Ambient (branch := branch) (n := n) (t := t)
  rows repeats δ

abbrev Label := NormalizedTargetInitialization.Label ⊕ (Native ⊕ Final)

def initialControl : Control (branch := branch) (n := n) (t := t) rows repeats δ :=
  SignedTupleLayout.clean («width» := width) («Desc» := Desc) ()

def initialAmbient : Ambient (branch := branch) (n := n) (t := t) rows repeats δ :=
  (initialControl (branch := branch) (n := n) (t := t) rows repeats δ).1

local notation "Labels" => Label (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "Registers" => Control (branch := branch) (n := n) (t := t) rows repeats δ
local notation "initial" => initialControl (branch := branch) (n := n) (t := t) rows repeats δ
local notation "ambient" => initialAmbient (branch := branch) (n := n) (t := t) rows repeats δ

def initLabel (label : NormalizedTargetInitialization.Label) : Labels := .inl label

def driverLabel (label : Native) : Labels := .inr (.inl label)

def finalizerLabel (label : Final) : Labels := .inr (.inr label)

local notation "liftInit" => initLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "liftDriver" => driverLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "liftFinal" => finalizerLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ
local notation "nativeProgram" => ExactTargetOdometer.program
  (branch := branch) (n := n) (t := t) (Extra := Fin 4)
  rows repeats hn hbranch hrows δ
local notation "nativeEntry" => ExactTargetOdometer.body
  (branch := branch) (n := n) (t := t) (Extra := Fin 4)
  rows repeats hn hbranch hrows δ

def program : Labels → TM2.Stmt (fun _ : Arena => Bool) Labels Registers
  | .inl label => NormalizedTargetInitialization.instruction liftInit
      (some (liftDriver nativeEntry)) none label
  | .inr (.inl label) => MachineSubroutine.statement liftDriver
      (some (liftFinal .reverse)) (nativeProgram label)
  | .inr (.inr label) => TargetFinalizeMachine.instruction q
      (tapeEnumeration branch n t) (finalizerTape branch n t) ambient liftFinal label

local notation "runProgram" => program (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

def machine : FinTM2 where
  K := Arena
  k₀ := .source .table
  k₁ := .extra 3
  Γ _ := Bool
  Λ := Labels
  main := liftInit .seed
  σ := Registers
  initialState := initial
  m := runProgram

local notation "tm" => machine (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

def configuration (label : Option Labels) (tapes : Arena → List Bool) : (tm).Cfg :=
  ⟨label, initial, tapes⟩

local notation "cfg" => configuration (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

def returnInTime (tapes : Arena → List Bool) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftDriver .exit)) tapes)
      (some (cfg (some (liftFinal .reverse)) tapes)) 1 where
  steps := 1
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl 1

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "finalData" => NormalizedTargetTapeBound.finalData
  (t := t) rows repeats hn hbranch hrows δ
local notation "output" => NormalizedTarget.outputBits (t := t) rows repeats hn hbranch hrows δ

theorem header_body_eq_outputBits (input : NormalizedSourceInput.Input) :
    encodeWords [(finalData input).count, (finalData input).count,
        q, (finalData input).count] ++ (finalData input).reversedOutput.reverse =
      output input := by
  simpa only [NormalizedTargetTapeBound.finalData, SignedTupleSemantics.dataOfPrefix,
    List.append_nil, List.reverse_reverse, NormalizedTarget.outputBits,
    NormalizedTarget.construct] using
    (ExactTargetOnlineEncoding.target_gameBits (t := t)
      (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ).symm

def initializeInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftInit .seed)) (NormalizedTargetInitialization.inputTapes input))
      (some (cfg (some (liftDriver nativeEntry))
        (NormalizedTargetInitialization.readyTapes input)))
      (4 * ((NormalizedSourceInput.bits input).length + 1)) := by
  exact NormalizedTargetInitialization.initializeInTime liftInit
    (some (liftDriver nativeEntry)) none runProgram (fun _ => rfl) input ambient none

def finalizeBudget (size : Nat) : Nat :=
  (15 + Fintype.card Arena * (q + 9)) *
    (TargetTapeEnvelope.coeff width q D * (size + 1) ^ (2 * width + 2) + 1)

def totalBudget (size : Nat) : Nat :=
  4 * (size + 1) + ExactTargetOdometer.timeBound (t := t) rows repeats hn hbranch hrows δ size + 1 +
    finalizeBudget (t := t) rows repeats hn hbranch hrows δ size

def time : Polynomial Nat :=
  4 * (Polynomial.X + 1) +
    Polynomial.C (SignedCostEnvelope.bodyCoeff width D + 2 * width) *
      (Polynomial.X + 1) ^ (SignedCostEnvelope.degree width + width) + 1 +
    Polynomial.C (15 + Fintype.card Arena * (q + 9)) *
      (Polynomial.C (TargetTapeEnvelope.coeff width q D) *
        (Polynomial.X + 1) ^ (2 * width + 2) + 1)

theorem time_eval (size : Nat) :
    (time (t := t) rows repeats hn hbranch hrows δ).eval size =
      totalBudget (t := t) rows repeats hn hbranch hrows δ size := by
  simp [time, totalBudget, finalizeBudget, ExactTargetOdometer.timeBound]

theorem initList_eq (input : NormalizedSourceInput.Input) :
    initList tm (NormalizedSourceInput.bits input) =
      cfg (some (liftInit .seed)) (NormalizedTargetInitialization.inputTapes input) := by
  unfold initList configuration
  congr 1
  funext key
  cases key with
  | source source =>
      cases source <;> simp [machine, NormalizedTargetInitialization.inputTapes]
      rfl
  | current i => simp [machine, NormalizedTargetInitialization.inputTapes]
  | remaining i => simp [machine, NormalizedTargetInitialization.inputTapes]
  | encodedVariable i j => simp [machine, NormalizedTargetInitialization.inputTapes]
  | adapterScratch => simp [machine, NormalizedTargetInitialization.inputTapes]
  | edgeWork j => simp [machine, NormalizedTargetInitialization.inputTapes]
  | edgeCount => simp [machine, NormalizedTargetInitialization.inputTapes]
  | extra j => simp [machine, NormalizedTargetInitialization.inputTapes]

theorem haltList_eq (word : List Bool) :
    haltList tm word = cfg none (MachineDrainMany.haltTapes (.extra 3) word) := by
  unfold haltList configuration
  congr 1

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet tm :=
  MachineFiniteAlphabet.of_bool tm (fun _ => rfl)

end
end PerfectCompleteness.NormalizedTargetMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedTargetValue
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedTargetValue


open UniqueGamesTheorem.Foundations Target
open FixedRows
open scoped Classical

noncomputable section

theorem packed_value_le (formula : Formula) [NeZero formula.clauses.length]
    (nonempty : formula.clauses ≠ [])
    (distinct : ∀ clause ∈ formula.clauses, ∀ i j : Fin 3,
      clause[i].variableIndex = clause[j].variableIndex → i = j)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ) (hδ : 0 < δ) :
    (NormalizedTarget.construct (branch := branch) (n := n) (t := t)
      rows repeats hn hbranch hrows δ ⟨formula, nonempty, distinct⟩).value ≤
      PreliminaryOutput.value
        (fun index : Fin formula.clauses.length =>
          ({ clause := PCP.clauseAt formula index
             distinct := fun i j same => distinct _ (List.getElem_mem index.isLt) i j same } :
            SourceClause.NormalizedClause formula.variables))
        branch n t rows repeats hn hbranch hrows + (δ : ℝ) / 3 := by
  have clauses_eq :
      NormalizedSourceInput.clauses ⟨formula, nonempty, distinct⟩ =
        (fun index : Fin formula.clauses.length =>
          ({ clause := PCP.clauseAt formula index
             distinct := fun i j same => distinct _ (List.getElem_mem index.isLt) i j same } :
            SourceClause.NormalizedClause formula.variables)) := by
    funext index
    rfl
  have native :
      (NormalizedTarget.construct (branch := branch) (n := n) (t := t)
        rows repeats hn hbranch hrows δ ⟨formula, nonempty, distinct⟩).value ≤
        PreliminaryOutput.value (NormalizedSourceInput.clauses ⟨formula, nonempty, distinct⟩)
          branch n t rows repeats hn hbranch hrows + (δ : ℝ) / 3 := by
    simpa only [PreliminaryOutput.value] using
      (NormalizedTarget.value_le (branch := branch) (n := n) (t := t)
        rows repeats hn hbranch hrows δ ⟨formula, nonempty, distinct⟩ hδ)
  rw [clauses_eq] at native
  exact native

end
end PerfectCompleteness.FixedTargetValue

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FixedStoppedPhysicalLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

section PathTransport

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  {p q : Path branch root (h + 1)}

def sourceSampleEquiv (hp : p = q) :
    SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated ≃
    SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats q) (t := t)
      rows clauses designated :=
  Equiv.cast (congrArg (fun path : Path branch root (h + 1) =>
    SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats path) (t := t)
      rows clauses designated) hp)

end PathTransport

end
end PerfectCompleteness.FixedStoppedNativeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedProjectedMeetingLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedMeetingLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype
  StoppedProjectedPhysicalAdvice.rawFiberFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ)

variable {branch : Nat → Nat} {i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (hupper : j + 1 ≤ plan.depth) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

abbrev Sample := StoppedProjectedPhysicalAdvice.Sample (t := t) clauses
  (FixedRows.rows plan) (FixedRows.repeats plan) hupper hij designated plan.order

abbrev RawSample := StoppedProjectedPhysicalAdvice.RawSample (t := t) clauses
  (FixedRows.rows plan) (FixedRows.repeats plan) hupper hij designated plan.order

variable [NeZero m]
  (hbranch : ∀ k < plan.depth, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

def rawMeetingProbability
    (sample : RawSample (t := t) plan clauses hupper hij designated) : ℝ :=
  HierarchicalProjectedAverage.meetingProbability plan
    (StoppedProjectedExperiment.nativeSlots clauses sample.1)
    (StoppedProjectedExperiment.projectedSlots clauses (FixedRows.rows plan)
      hupper hij designated sample.1)
    (StoppedProjectedExperiment.projection clauses (FixedRows.rows plan)
      hupper hij designated sample.1)
    (StoppedProjectedExperiment.upper hupper sample.1) (i + 1)
    (StoppedProjectedExperiment.lower (FixedRows.rows plan) hupper hij sample.1)
    (StoppedProjectedExperiment.cut (FixedRows.rows plan) hupper hij sample.1)
    (StoppedProjectedExperiment.direction (FixedRows.rows plan) hupper hij sample.1)
    (StoppedProjectedExperiment.innerLaw (FixedRows.rows plan) hij
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))
      (rows_positive plan) flag) σ sample.2

def meetingProbability
    (sample : Sample (t := t) plan clauses hupper hij designated) : ℝ :=
  rawMeetingProbability plan clauses hupper hij designated hbranch flag σ
    (StoppedProjectedPhysicalAdvice.read clauses (FixedRows.rows plan)
      (FixedRows.repeats plan) hupper hij designated plan.order sample)

abbrev expectedMeeting : ℝ :=
  HierarchicalProjectedOuterAverage.expectedMeeting plan
    (StoppedProjectedExperiment.nativeSlots clauses)
    (StoppedProjectedExperiment.projectedSlots clauses (FixedRows.rows plan)
      hupper hij designated)
    (StoppedProjectedExperiment.projection clauses (FixedRows.rows plan)
      hupper hij designated)
    (StoppedProjectedExperiment.upper hupper) (i + 1)
    (StoppedProjectedExperiment.lower (FixedRows.rows plan) hupper hij)
    (StoppedProjectedExperiment.cut (FixedRows.rows plan) hupper hij)
    (StoppedProjectedExperiment.direction (FixedRows.rows plan) hupper hij)
    (fun _ => StoppedProjectedExperiment.innerLaw (FixedRows.rows plan) hij
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))
      (rows_positive plan) flag)
    (StoppedProjectedExperiment.outerLaw hupper hbranch) σ

end
end PerfectCompleteness.StoppedProjectedMeetingLaw

end

end OAI
end


