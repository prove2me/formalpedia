-- Prove2me | Definitions.Def_OAIQ252P018
-- name    : OAIQ252P018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:58:48.026218+00:00
-- url     : https://prove2.me/theorems/fc89cc6a-907a-4cc3-8d6b-3559c105c0c9
-- title:
--   Definitions bundle OAIQ252P018 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 425 declarations of OpenAI's Lean: 338 definitions, 2 inductive types or structures, 1 instance and 84 theorems. The definitions and types are `OAI.PerfectCompleteness.FixedBinaryGapReduction.ofPreliminarySoundness`, `OAI.PerfectCompleteness.FixedDecoderCleanRate.Geometry`, `OAI.PerfectCompleteness.FixedDecoderCleanRate.setup`, `OAI.PerfectCompleteness.FixedDecoderFamilyRate.setups`, `OAI.PerfectCompleteness.FixedLowerRawCollision.UpperTable`, `OAI.PerfectCompleteness.FixedLowerRawCollision.fullCollisionProbability`, `OAI.PerfectCompleteness.FixedNativeHigh.probability`, `OAI.PerfectCompleteness.FixedNativeHigh.questionUseful`, `OAI.PerfectCompleteness.FixedParameters.projectionProbability`, `OAI.PerfectCompleteness.FixedPreliminaryGame.Strategy`, `OAI.PerfectCompleteness.FixedPreliminaryGame.game`, `OAI.PerfectCompleteness.FixedRankContradiction.gamma`, `OAI.PerfectCompleteness.FixedSourceChildCollision.Calls`, `OAI.PerfectCompleteness.FixedSourceChildCollision.Form`, `OAI.PerfectCompleteness.FixedSourceChildCollision.Native`, `OAI.PerfectCompleteness.FixedSourceChildCollision.Questions`, `OAI.PerfectCompleteness.FixedSourceChildCollision.Sample`, `OAI.PerfectCompleteness.FixedSourceChildCollision.fullEvent`, `OAI.PerfectCompleteness.FixedSourceChildCollision.markedLaw`, `OAI.PerfectCompleteness.FixedSourceChildCollision.restrictedEvent`, `OAI.PerfectCompleteness.FixedSourceChildCollision.uniformLaw`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.Choice`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.Questions`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.Table`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.TableFamily`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.flag`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.globalProbability`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.localProbability`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.localTables`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.nativeProbability`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.tableFintype`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.upperAnswerFintype`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.Questions`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.Table`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.TableFamily`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.first`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.markedProbability`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.second`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.tableFintype`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.tableLaw` and 300 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_FixedRankContradiction`, `PerfectCompleteness_Construction_OriginalCutBucketReplacement`, `PerfectCompleteness_Construction_OriginalOwnBucketSplit`, `PerfectCompleteness_Construction_StoppedProjectedBuckets`, `PerfectCompleteness_Decoding_DecoderFamilyLawLemmas`, `PerfectCompleteness_Decoding_FixedDecoderCleanRateLemmas`, `PerfectCompleteness_Decoding_FixedSourceChildCollision`, `PerfectCompleteness_Decoding_FixedSourceLowerCollision`, `PerfectCompleteness_Decoding_FixedStoppedDecoderContext`, `PerfectCompleteness_Decoding_FixedStoppedDecoderLaw`, `PerfectCompleteness_Decoding_FixedStoppedNativeProjection`, `PerfectCompleteness_Decoding_FixedUpperPairErrorLemmas`, `PerfectCompleteness_Decoding_LowerCutUniformCoordinatesLemmas`, `PerfectCompleteness_Decoding_OriginalCutCollision`, `PerfectCompleteness_Decoding_OriginalWholeCutProjection`, `PerfectCompleteness_Decoding_ProjectedUpperPair`, `PerfectCompleteness_Decoding_SourceQuestionCollisionTransportLemmas`, `PerfectCompleteness_Decoding_UpperCutTriangle`, `PerfectCompleteness_Decoding_UpperScalarCutErasure`, `PerfectCompleteness_Decoding_UpperScalarCutLaw`, `PerfectCompleteness_Decoding_UpperScalarCutProjection`, `PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas`, `PerfectCompleteness_Decoding_UpperScalarFreshProjectionLemmas`, `PerfectCompleteness_Decoding_UpperScalarPairAveraging`, `PerfectCompleteness_Foundations_OriginalExtraCutComparison`, `PerfectCompleteness_Foundations_OriginalWholeCut`, `PerfectCompleteness_Foundations_OriginalWholeCutBridge`, `PerfectCompleteness_Foundations_ProjectedWholeCut`, `PerfectCompleteness_Foundations_SourceProjectedWholeChoices`, `PerfectCompleteness_Foundations_StoppedProjectedCoarseLemmas`, `PerfectCompleteness_Foundations_StoppedProjectedOldRecord`, `PerfectCompleteness_Foundations_StoppedProjectedUsefulAverage`, `PerfectCompleteness_Foundations_StoppedProjectedUsefulEvent`, `PerfectCompleteness_Machines_FixedBinaryGapReduction`, `PerfectCompleteness_Machines_FixedStoppedNativeTape`, `PerfectCompleteness_Machines_NormalizationMachine`, `PerfectCompleteness_Machines_NormalizedTargetMachine`, `PerfectCompleteness_Machines_NormalizedTargetTapeBound`, `PerfectCompleteness_Machines_PreprocessingMachineLemmas`, `PerfectCompleteness_Machines_SourceOccurrenceProducerLemmas`, `PerfectCompleteness_Reduction_FixedCallBudgetLemmas`, `PerfectCompleteness_Reduction_FixedComparisonErrorsLemmas`, `PerfectCompleteness_Reduction_FixedNativeHigh`, `PerfectCompleteness_Reduction_FixedPhysicalStoppedComparison`, `PerfectCompleteness_Reduction_FixedSourcePhysicalHighLemmas`, `PerfectCompleteness_Reduction_FixedStoppedDirections`, `PerfectCompleteness_Reduction_FixedStoppedHighBound`, `PerfectCompleteness_Reduction_FixedStoppedInverseBound`, `PerfectCompleteness_Reduction_FixedStoppedMeetingEquality`, `PerfectCompleteness_Reduction_FixedStoppedUsefulMass`, `PerfectCompleteness_Reduction_FixedTarget`, `PerfectCompleteness_Reduction_FixedTargetValue`, `PerfectCompleteness_Reduction_HierarchicalFixedAdviceFamilyLemmas`, `PerfectCompleteness_Reduction_PreliminaryOutputLemmas`, `PerfectCompleteness_Repetition_StoppedCleanGeometry`, `PerfectCompleteness_Sampling_FixedSourcePairVariation`, `PerfectCompleteness_Sampling_FixedStoppedPhysicalLawLemmas`, `PerfectCompleteness_Sampling_OriginalCutBucketLaw`, `PerfectCompleteness_Sampling_OriginalCutPairLaw`, `PerfectCompleteness_Sampling_OriginalUniformCut`, `PerfectCompleteness_Sampling_OriginalUniformCutBase`, `PerfectCompleteness_Sampling_OriginalWholeCutLaw`, `PerfectCompleteness_Sampling_StoppedSourcePairLaw`, `PerfectCompleteness_Sampling_StoppedUsefulPairLaw`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_FinalCNFOutputLemmas`, `UniqueGames_Machines_GraphIterationBoundsLemmas`, `UniqueGames_Machines_MachineLazyTableRuntime`, `UniqueGames_Machines_MachineOverlayTable`, `UniqueGames_Machines_MachinePaddedOverlay`, `UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas`, `UniqueGames_Machines_MachinePaddingTable`, `UniqueGames_Machines_MachineRegularTableBoundsLemmas`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_PCP_LoopInitializationLemmas`, `UniqueGames_PCP_PreprocessingPaddingWords`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P016` and `OAIQ252P017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ252P020`; the statements `OAI.PerfectCompleteness.FixedDecoderPairRate.probability_lt_accuracy`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.globalProbability_le_marked`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.mean_local_le`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.supported_uniform_le`, `OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability_square_le_collision`, `OAI.PerfectCompleteness.FixedStoppedActualBounds.coarseVariation_le_pairedVariation`, `OAI.PerfectCompleteness.FixedStoppedContradiction.meeting_lt_gamma`, `OAI.PerfectCompleteness.FixedStoppedHighBound.directionMean_square_le`, `OAI.PerfectCompleteness.FixedStoppedInverseBound.expectedMeeting_ge_gamma`, `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting`, `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.native_expectation_eq_cleanMeeting`, `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.physical_expectation_eq_expectedMeeting`, `OAI.PerfectCompleteness.FixedStoppedNativeProjection.projection_heq`, `OAI.PerfectCompleteness.FixedStoppedNativeProjection.rightSlots_eq`, `OAI.PerfectCompleteness.FixedStoppedNativeTape.experimentTape_heq`, `OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq`, `OAI.PerfectCompleteness.FixedStoppedPair.exists_pair`, `OAI.PerfectCompleteness.FixedStoppedUpperProbability.pairedVariation_le`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.useful_probability_ge_of_reserve`, `OAI.PerfectCompleteness.FixedUpperCutTriangle.original_reference_lt`, `OAI.PerfectCompleteness.FixedUpperPairError.lower_errors_lt`, `OAI.PerfectCompleteness.OriginalCutPairLaw.actual_pair_totalVariation_le`, `OAI.PerfectCompleteness.OriginalExtraCutComparison.actualLaw_eq_mixture`, `OAI.PerfectCompleteness.OriginalUniformCut.uniform_toStoppedTape`, `OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct_child_law`, `OAI.PerfectCompleteness.OriginalWholeCutLaw.readRecord_law`, `OAI.PerfectCompleteness.PreliminaryPairReserve.exists_pair`, `OAI.PerfectCompleteness.StoppedProjectedCoarse.original_observe_law`, `OAI.PerfectCompleteness.StoppedProjectedUsefulAverage.original_probability_eq_mean`, `OAI.PerfectCompleteness.StoppedProjectedUsefulEvent.arrays_readout`, `OAI.PerfectCompleteness.StoppedProjectedUsefulEvent.usefulEvent_eq`, `OAI.PerfectCompleteness.StoppedProjectedUsefulProbability.original_probability_eq_usefulProbability`, `OAI.PerfectCompleteness.StoppedSourcePairLaw.prefix_pair_law`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.actualPair_law`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.matrix_readout`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.observe_law`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.pairRecord_observe`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.readout_law`, `OAI.PerfectCompleteness.UpperCutTriangle.modified_reference_variation` and `OAI.PerfectCompleteness.UpperScalarPairComparison.modified_original_variation`; the proofs of `OAI.PerfectCompleteness.FixedDecoderPairRate.probability_lt_accuracy`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.globalProbability_le_marked`, `OAI.PerfectCompleteness.FixedSourceGlobalCollision.mean_local_le`, `OAI.PerfectCompleteness.FixedSourceLowerCollision.supported_uniform_le`, `OAI.PerfectCompleteness.FixedSourcePhysicalHigh.probability_square_le_collision`, `OAI.PerfectCompleteness.FixedStoppedActualBounds.coarseVariation_le_pairedVariation`, `OAI.PerfectCompleteness.FixedStoppedContradiction.meeting_lt_gamma`, `OAI.PerfectCompleteness.FixedStoppedHighBound.directionMean_square_le`, `OAI.PerfectCompleteness.FixedStoppedInverseBound.expectedMeeting_ge_gamma`, `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting`, `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.native_expectation_eq_cleanMeeting`, `OAI.PerfectCompleteness.FixedStoppedMeetingEquality.physical_expectation_eq_expectedMeeting`, `OAI.PerfectCompleteness.FixedStoppedNativeProjection.projection_heq`, `OAI.PerfectCompleteness.FixedStoppedNativeProjection.rightSlots_eq`, `OAI.PerfectCompleteness.FixedStoppedNativeTape.experimentTape_heq`, `OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq`, `OAI.PerfectCompleteness.FixedStoppedPair.exists_pair`, `OAI.PerfectCompleteness.FixedStoppedUpperProbability.pairedVariation_le`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical`, `OAI.PerfectCompleteness.FixedStoppedUsefulMass.useful_probability_ge_of_reserve`, `OAI.PerfectCompleteness.FixedUpperCutTriangle.original_reference_lt`, `OAI.PerfectCompleteness.FixedUpperPairError.lower_errors_lt`, `OAI.PerfectCompleteness.OriginalCutPairLaw.actual_pair_totalVariation_le`, `OAI.PerfectCompleteness.OriginalExtraCutComparison.actualLaw_eq_mixture`, `OAI.PerfectCompleteness.OriginalUniformCut.uniform_toStoppedTape`, `OAI.PerfectCompleteness.OriginalWholeCutBridge.reconstruct_child_law`, `OAI.PerfectCompleteness.OriginalWholeCutComparison.totalVariation_le`, `OAI.PerfectCompleteness.OriginalWholeCutLaw.readRecord_law`, `OAI.PerfectCompleteness.PreliminaryPairReserve.exists_pair`, `OAI.PerfectCompleteness.StoppedProjectedCoarse.original_observe_law`, `OAI.PerfectCompleteness.StoppedProjectedUsefulAverage.original_probability_eq_mean`, `OAI.PerfectCompleteness.StoppedProjectedUsefulEvent.arrays_readout`, `OAI.PerfectCompleteness.StoppedProjectedUsefulEvent.usefulEvent_eq`, `OAI.PerfectCompleteness.StoppedProjectedUsefulProbability.original_probability_eq_usefulProbability`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.matrix_readout`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.pairRecord_observe`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.readout_law`, `OAI.PerfectCompleteness.Theorem11.exists_reduction` and `OAI.PerfectCompleteness.UpperScalarPairComparison.modified_original_variation`.
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
import Definitions.Def_OAIQ252P016
import Definitions.Def_OAIQ252P017

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFLoopLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
attribute [-simp] _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows.headerCommands_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixWords_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudRank_cloudSelect _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_cloudRank _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_oldCloudIndex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.mem_cloudDarts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_new_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_old_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudRank_select _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudSelect_castAdd _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudSelect_natAdd _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.paddedCloudSelect_rank _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_internal _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.rotation_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.vertexOrder_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes; FinalCNFCleanup
supplies the subsequent canonical halt required by the machine interface.
-/

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

/-- The input is read from the genuine `initList` configuration. Header, every
row, final guard, and reversal are all actual transitions of this one program. -/
noncomputable def rawRun (plan : Plan) (table : GraphTables.Table) : RawRun plan table := by
  let base := headerResultTapes table.vertices table.darts (tableRowsBits (genericTable table))
  let ambient : Ambient := ((), fun _ => false)
  have headerRun : StateTransition.EvalsToInTime (machine headerPlan plan).step
      (initList (machine headerPlan plan) (GraphTables.tableBits table))
      (some ⟨some .guard, ((ambient, ()), none), base⟩)
      (headerTimePolynomial.eval (GraphTables.tableBits table).length) := by
    simpa only [genericTable_tableBits, genericTable_vertices, genericTable_darts, base, ambient]
      using initializedTableHeaderInTime plan (genericTable table)
  let loop := loopInTime headerPlan plan table table.darts 0 (by omega)
    base ambient (header_loopInvariant table)
  have acc : loop.finalTapes .accumulator = (emittedBytes plan table).reverse := by
    rw [loop.accumulator]
    simp only [remainingEvents_zero, base, headerResultTapes_accumulator, emittedBytes,
      List.reverse_append]
  have out : loop.finalTapes .output = [] := by
    rw [loop.output]
    rfl
  let finalTapes := Reduction.MachineTransfer.tapesAt Tape.accumulator Tape.output
    loop.finalTapes [] (emittedBytes plan table)
  have finish : StateTransition.EvalsToInTime (machine headerPlan plan).step
      ⟨some .reverseOutput, ((loop.finalAmbient, ()), none), loop.finalTapes⟩
      (some ⟨none, ((loop.finalAmbient, ()), none), finalTapes⟩)
      ((emittedBytes plan table).length + 1) := by
    have run := Reduction.MachineTransfer.transferAtInTime Tape.accumulator Tape.output
      (by decide) id false .reverseOutput none (program headerPlan plan) rfl
      loop.finalTapes (loop.finalAmbient, ()) none
    simpa only [acc, out, List.reverse_reverse, List.length_reverse, List.map_id,
      List.append_nil, finalTapes, machine, FinTM2.step] using! run
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headerRun loop.execution
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  exact {
    finalAmbient := loop.finalAmbient
    finalTapes := finalTapes
    execution := {
      toEvalsTo := run.toEvalsTo
      steps_le_m := by
        have hb := run.steps_le_m
        unfold rawBudget
        omega }
    output := by simp [finalTapes, Reduction.MachineTransfer.tapesAt] }

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFOutputLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
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


theorem rawBudget_le_phaseTime (table : GraphTables.Table) :
    rawBudget rowPlan table ≤ phaseTimePolynomial.eval (GraphTables.tableBits table).length := by
  unfold rawBudget
  rw [emittedBytes_eq_formulaBits]
  simpa only [Nat.add_assoc] using table_phaseTime_le table

/-- A concrete finite machine computes the complete CNF serialization from
the exact unary graph-table serialization, with a proved polynomial bound. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits formulaBits FinalTableFormula.output where
  tm := FinalCNFCleanup.completedMachine headerPlan rowPlan
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))
  outputsFun table := by
    change TM2OutputsInTime (FinalCNFCleanup.completedMachine headerPlan rowPlan)
      ((GraphTables.tableBits table).map id)
      (some ((formulaBits (FinalTableFormula.output table)).map id))
      ((finalTimePolynomial (Runtime.programPushBound (machine headerPlan rowPlan))).eval
        (GraphTables.tableBits table).length)
    have input_eq :
        @List.map ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
          ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₀)
          id (GraphTables.tableBits table) = GraphTables.tableBits table := List.map_id _
    have output_eq :
        @List.map ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
          ((FinalCNFCleanup.completedMachine headerPlan rowPlan).Γ
            (FinalCNFCleanup.completedMachine headerPlan rowPlan).k₁)
          id (formulaBits (FinalTableFormula.output table)) =
          formulaBits (FinalTableFormula.output table) := List.map_id _
    rw [input_eq, output_eq, finalTimePolynomial_eval]
    let raw := rawRun rowPlan table
    let bounded : StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
        (initList (machine headerPlan rowPlan) (GraphTables.tableBits table))
        (some ⟨none, ((raw.finalAmbient, ()), none), raw.finalTapes⟩)
        (phaseTimePolynomial.eval (GraphTables.tableBits table).length) := {
      toEvalsTo := raw.execution.toEvalsTo
      steps_le_m := raw.execution.steps_le_m.trans (rawBudget_le_phaseTime table) }
    have correct : raw.finalTapes .output = formulaBits (FinalTableFormula.output table) :=
      raw.output.trans (emittedBytes_eq_formulaBits table)
    have run := FinalCNFCleanup.outputsInTime headerPlan rowPlan
      (GraphTables.tableBits table) (formulaBits (FinalTableFormula.output table))
      ((raw.finalAmbient, ()), none) raw.finalTapes
      (phaseTimePolynomial.eval (GraphTables.tableBits table).length) bounded correct
    exact run

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- Exact final codec identity used by the machine-output correspondence. -/
theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphIterationBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial bounds every actual intermediate encoding in the concrete
logarithmic graph iteration. The linear recurrence is on graph size. -/



/-! Actual polynomial-time iteration of the concrete graph-table round. A
certificate for that one body is the only supplied machine input. Counter
preparation, repeated calls, tape handoffs, and final cleanup are all proved. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds


variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

/-- Actual 3SAT gap-map runtime follows from the one concrete round certificate;
initialization, variable repetition, and the final CNF converter are supplied. -/
noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end UniqueGamesTheorem.Foundations.Complexity.MachineTableIteration



namespace UniqueGamesTheorem.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem gapMap : FiniteAlphabet (MachineTableIteration.gapMapCertificate H body).tm :=
  composeBits (MachineTableIteration.tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime (table H body finiteBody) finalCNF

end UniqueGamesTheorem.Foundations.Complexity.TableIterationFiniteAlphabet

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

/-- Every tape alphabet of this exact completed computation certificate is finite. -/
theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineOverlayTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.counted_count _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_current _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.boolView_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.caller_normalizeState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.clearRegister_initialState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.program_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.tableExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.familyBudget_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds.resizeSum_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_firstEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_outputEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.program_secondEmit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.accumulatedVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_prepareState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_resetState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.caller_rowAfterState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.clearRegister_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.prepareState_boundaryState _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_outer _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.program_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowAfterState_position _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.rowExecution_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.overlayView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.generatedWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.priorVertices_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_drop_full _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration.vertexWords_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.leftMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rightMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rowBits_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords.vertexBits_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

variable {AmbientState : Type}

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

/-- The complete existing splitter is executed, retaining both archives. -/
theorem splitTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (table : GraphTables.Table) (rawH : List Bool) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps
      table.vertices table.darts (MachineTableSplit.rowsBits table)]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (GraphTables.tableBits table) rawH⟩) =
      some ⟨next .copyHFirst, clean d e hd he a,
        splitTapes table.vertices table.darts (MachineTableSplit.rowsBits table) rawH⟩ := by
  let ambient := (clean d e hd he a).1
  have source := MachineTableSplit.tableTrace table ambient none
  have placed := Placement.trace (Sum.inl : Fin 5 → Tape) splitView (fun _ => rfl)
    (by intro j k h; cases j <;> simp_all [splitView])
    (Sum.inl : MachineTableSplit.Label → Label d e) (next .copyHFirst)
    (initialTapes [] rawH) MachineTableSplit.program (program d e hd he) (fun _ => rfl)
    _ _ _ source
  simp only [Placement.configuration, Placement.label] at placed
  rw [placedTapes, placedTapes] at placed
  simpa only [initialTapes,
    splitTapes, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using placed

/-- Preserve and copy raw H, emit both output headers from the parsed unary
vertex count, copy the actual fuel field, and initialize_ the physical counter. -/
theorem preparationTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs : List Bool) (n m : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[preparationSteps n h]
      (some ⟨next .copyHFirst, clean d e hd he a,
        memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
  let b0 := memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []
  let b1 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] []
  let b2 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] (encodeWord ((d + e) * n))
  let b3 := memory g h gs h (encodeWord n) (encodeWord m) [] [] []
    (encodeWords [n, n * (d + e)])
  let b4 := memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) [] []
    (encodeWords [n, n * (d + e)])
  let ambient := (clean d e hd he a).1
  have hcopy := MachineCopy.copyTrace expanderArchive expanderStream scratch
    (by decide) (by decide) (by decide) false (.inr .copyHFirst) (.inr .copyHSecond)
    (next .countSeed) (program d e hd he) rfl rfl b0 rfl ambient none
  have copyRun : (advance (TM2.step (program d e hd he)))^[2 * (h.length + 1)]
      (some ⟨next .copyHFirst, clean d e hd he a, b0⟩) =
      some ⟨next .countSeed, clean d e hd he a, b1⟩ := by
    simpa only [b0, b1, memory_expanderArchive, memory_expanderStream, next, List.append_nil,
      update_expanderStream, ambient, clean, MachineLazyRows.streamClean,
      MachinePortReindex.clean] using hcopy
  have hcount := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) (d + e) 0
    (.inr .countSeed) (.inr .countScan) (.inr .countRestore) (next .headerSeed)
    (program d e hd he) rfl rfl rfl b1 n [] (by simp [b1, memory, vertexCount]) rfl ambient none
  have countRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .countSeed, clean d e hd he a, b1⟩) =
      some ⟨next .headerSeed, clean d e hd he a, b2⟩ := by
    simpa only [b1, b2, memory_output, next, List.append_nil, Nat.add_zero, update_output,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hcount
  have hheader := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) 1 0
    (.inr .headerSeed) (.inr .headerScan) (.inr .headerRestore) (next .fuelSeed)
    (program d e hd he) rfl rfl rfl b2 n [] (by simp [b2, memory, vertexCount]) rfl ambient none
  have headerRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .headerSeed, clean d e hd he a, b2⟩) =
      some ⟨next .fuelSeed, clean d e hd he a, b3⟩ := by
    simpa only [b2, b3, memory_output, next, Nat.one_mul, Nat.add_zero, update_output,
      Nat.mul_comm (d + e) n, encodeWords, List.append_nil,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hheader
  have hfuel := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch fuel
    (by decide) (by decide) (by decide) 1 0
    (.inr .fuelSeed) (.inr .fuelScan) (.inr .fuelRestore) (next .vertexSeed)
    (program d e hd he) rfl rfl rfl b3 n [] (by simp [b3, memory, vertexCount]) rfl ambient none
  have fuelRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .fuelSeed, clean d e hd he a, b3⟩) =
      some ⟨next .vertexSeed, clean d e hd he a, b4⟩ := by
    simpa only [b3, b4, memory_fuel, next, List.append_nil, Nat.one_mul, Nat.add_zero,
      update_fuel, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hfuel
  have seedRun : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .vertexSeed, clean d e hd he a, b4⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .vertexSeed)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, b4, memory_vertex,
      update_vertex, next, encodeWord, List.replicate_zero, List.nil_append]
  have all := joinTrace (joinTrace (joinTrace (joinTrace copyRun countRun) headerRun) fuelRun) seedRun
  have count : preparationSteps n h =
      (((2 * (h.length + 1) + (2 * (n + 1) + 1)) + (2 * (n + 1) + 1)) +
        (2 * (n + 1) + 1)) + 1 := by unfold preparationSteps; omega
  rw [count]
  exact all

theorem oldVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (v : Fin n) (g h gs hs nv mv f current out : List Bool)
    (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) hs nv mv f current [] out⟩) =
      some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f current [] (out ++ oldOutput G e v)⟩ := by
  have hrun := MachineLazyRows.vertexTrace d hd (d + e) 0 oldTapes oldTapes_injective
    (fun stage => .inr (.old stage)) (next .tailSeed) (program d e hd he) (fun _ => rfl)
    (memory g h gs hs nv mv f current [] []) (row G v)
    (by
      intro i hi7 hi9
      fin_cases i <;> simp_all [oldTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, graphStream])
    (a, MachineFixedDivMod.residue e he 0) out
  simpa only [next, oldFrame, MachineLazyRows.recordsInput, List.flatMap_nil, List.nil_append,
    clean, oldBlock, oldRows, oldOutput] using hrun

theorem expanderVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (H : ExpanderTables.Table n e) (v : Fin n) (g h gs hs nv mv f current out : List Bool)
    (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineOverlayRows.vertexSteps d e v.val
      (List.ofFn (expanderValues H v)) out]
      (some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs (expanderBlock H v ++ hs) nv mv f current (encodeWord v.val) out⟩) =
      some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f current (encodeWord v.val) (out ++ expanderOutput d H v)⟩ := by
  let source := MachineStateEquiv.program (expanderState AmbientState d e).symm (program d e hd he)
  have code (stage : MachineOverlayRows.VertexLabel e) : source (.inr (.expander stage)) =
      MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage := by
    change MachineStateEquiv.statement (expanderState AmbientState d e).symm
      (MachineStateEquiv.statement (expanderState AmbientState d e) _) = _
    exact MachineStateEquiv.statement_symm_statement _ _
  have native := MachineOverlayRows.vertexTrace d e he expanderTapes expanderTapes_injective
    (fun stage => .inr (.expander stage)) (next .drainTail) source code
    (memory g h gs hs nv mv f current (encodeWord v.val) []) v.val (expanderValues H v)
    rfl
    (by
      intro i hi0 hi7 hi9
      fin_cases i <;> simp_all [expanderTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream])
    ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0) out
  have transported := MachineStateEquiv.trace (expanderState AmbientState d e) source _ _ _ native
  have back : MachineStateEquiv.program (expanderState AmbientState d e) source = program d e hd he :=
    MachineStateEquiv.program_symm_program (expanderState AmbientState d e).symm _
  rw [back] at transported
  simpa only [next, MachineStateEquiv.configuration, expanderState_clean, expanderFrame,
    encodeWords, List.nil_append, expanderBlock, expanderOutput] using transported

theorem tailCopyTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[2 * (k + 1) + 1]
      (some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩ := by
  let ambient := (clean d e hd he a).1
  have hrun := MachineUnaryAffineAt.seededAffineTrace vertex scratch tail
    (by decide) (by decide) (by decide) 1 0
    (.inr .tailSeed) (.inr .tailScan) (.inr .tailRestore) (next (.expander (0, none)))
    (program d e hd he) rfl rfl rfl
    (memory g h gs hs nv mv f (encodeWord k) [] out) k []
    (by simp [memory, vertex]) rfl ambient none
  simpa only [memory_tail, next, List.append_nil, Nat.one_mul, Nat.add_zero, update_tail,
    ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hrun

theorem tailFinishTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[k + 3]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have hd₀ := MachineDrain.drainTrace tail (.inr .drainTail) (next .increment)
    (program d e hd he) rfl (memory g h gs hs nv mv f (encodeWord k) [] out)
    (encodeWord k) ambient none
  have drain : (advance (TM2.step (program d e hd he)))^[k + 2]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩ := by
    simpa only [next, encodeWord_length, Nat.add_assoc, update_tail, ambient, clean,
      MachineLazyRows.streamClean, MachinePortReindex.clean] using hd₀
  have increment : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .increment)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, memory_vertex, next,
      update_vertex, encodeWord, List.replicate_succ, List.cons_append]
  have all := joinTrace drain increment
  simpa only [Nat.add_assoc] using all

/-- The complete old/expander pair for one actual vertex, with both physical
stream suffixes and the unchanged unary fuel accounted for. -/
theorem pairTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n)
    (g h gs hs nv mv f out : List Bool) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[pairSteps G H v out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) (expanderBlock H v ++ hs)
          nv mv f (encodeWord v.val) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (v.val + 1)) [] (out ++ outputBlock G H v)⟩ := by
  have h₁ := oldVertexTrace d e hd he G v g h gs (expanderBlock H v ++ hs)
    nv mv f (encodeWord v.val) out a
  have h₂ := tailCopyTrace d e hd he g h gs (expanderBlock H v ++ hs)
    nv mv f (out ++ oldOutput G e v) v.val a
  have h₃ := expanderVertexTrace d e hd he H v g h gs hs nv mv f
    (encodeWord v.val) (out ++ oldOutput G e v) a
  have h₄ := tailFinishTrace d e hd he g h gs hs nv mv f
    ((out ++ oldOutput G e v) ++ expanderOutput d H v) v.val a
  simpa only [pairSteps, outputBlock, List.append_assoc] using
    joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

theorem cleanupTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h out : List Bool) (n m : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[cleanupSteps n m]
      (some ⟨next .drainFuel, clean d e hd he a,
        memory g h [] [] (encodeWord n) (encodeWord m) (encodeWord 0) (encodeWord n) [] out⟩) =
      some ⟨none, clean d e hd he a, memory g h [] [] [] [] [] [] [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have h₁ := MachineDrain.drainTrace fuel (.inr .drainFuel) (next .drainVertex)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] (encodeWord n) [] out)
    (encodeWord 0) ambient none
  have h₂ := MachineDrain.drainTrace vertex (.inr .drainVertex) (next .drainVertexCount)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₃ := MachineDrain.drainTrace vertexCount (.inr .drainVertexCount) (next .drainDartCount)
    (program d e hd he) rfl (memory g h [] [] [] (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₄ := MachineDrain.drainTrace dartCount (.inr .drainDartCount) none
    (program d e hd he) rfl (memory g h [] [] [] [] [] [] [] out)
    (encodeWord m) ambient none
  simp only [encodeWord_length, update_fuel, update_vertex, update_vertexCount, update_dartCount] at h₁ h₂ h₃ h₄
  have all := joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄
  have hsteps : cleanupSteps n m = ((0 + 1 + 1 + (n + 1 + 1)) + (n + 1 + 1)) + (m + 1 + 1) := by
    unfold cleanupSteps
    omega
  rw [hsteps]
  exact all

/-- Each body premise needed by the generic unary counted-loop theorem is
constructed from the actual old/expander pair execution. -/
theorem loopBodyTraces {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    MachineCountedLoop.BodyTraces fuel (.inr .guard) (.inr (.old (0, none)))
      (program d e hd he) [] (fun _ => (clean d e hd he a).1) (fun _ => none)
      (loopBase G H) (loopCost G H) n := by
  intro r hr
  let v : Fin n := ⟨n - (r + 1), by omega⟩
  have hv : v.val + 1 = n - r := by dsimp [v]; omega
  have hinput : MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (oldBlock G v ++ remaining (oldBlock G) (v.val + 1))
        (expanderBlock H v ++ remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord v.val) []
        (outputPrefix G H v.val) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    change memory _ _ (remaining (oldBlock G) v.val) (remaining (expanderBlock H) v.val)
      _ _ _ _ _ _ = _
    rw [remaining_step (oldBlock G) v, remaining_step (expanderBlock H) v]
  have houtput : MachineUnaryCounter.counterTapes fuel (loopBase G H r) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord (v.val + 1)) []
        (outputPrefix G H v.val ++ outputBlock G H v) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    rw [← hv, outputPrefix_step]
  have run := pairTrace d e hd he G H v (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
    (encodeWord n) (encodeWord (n * d)) (encodeWord r) (outputPrefix G H v.val) a
  change (advance (TM2.step (program d e hd he)))^[loopCost G H r]
    (some ⟨next (.old (0, none)), clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r []⟩) =
    some ⟨next .guard, clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H r) r []⟩
  rw [hinput, houtput]
  simpa only [loopCost, dite_eq_left hr, v] using run

theorem loopTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineCountedLoop.totalSteps (loopCost G H) n]
      (some ⟨next .guard, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H)
          (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
          (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩) =
      some ⟨next .drainFuel, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] []
          (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have run := MachineCountedLoop.loopTrace fuel (.inr .guard) (.inr (.old (0, none)))
    (.inr .drainFuel) (program d e hd he) rfl []
    (fun _ => (clean d e hd he a).1) (fun _ => none) (loopBase G H) (loopCost G H) n
    (loopBodyTraces d e hd he G H a)
  have startFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H n) n [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
        (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
        (encodeWords [n, n * (d + e)]) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_self, remaining_zero, outputPrefix, prefix_zero]
    simp only [graphRows_blocks, rawExpander, expanderRows_blocks]
  have endFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H 0) 0 [] =
      memory (PortTables.tableBits G) (rawExpander H) [] []
        (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
        (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_zero, remaining_end, outputPrefix, prefix_end, tableBits_blocks]
  simp only [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration] at run
  rw [startFrame, endFrame] at run
  simpa only [next, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using run

theorem tableTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[tableSteps G H]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
      some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have h₁ := splitTrace d e hd he (PortTables.graphTable G) (rawExpander H) a
  rw [splitTapes_memory] at h₁
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  change (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps n (n * d)
      (MachineTableSplit.rowsBits (PortTables.graphTable G))]
    (some ⟨some (.inl .copyFirst), clean d e hd he a,
      initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
    some ⟨next .copyHFirst, clean d e hd he a,
      memory (encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G))
        (rawExpander H) (MachineTableSplit.rowsBits (PortTables.graphTable G)) []
        (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ at h₁
  rw [header] at h₁
  have h₂ := preparationTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (MachineTableSplit.rowsBits (PortTables.graphTable G)) n (n * d) a
  have h₃ := loopTrace d e hd he G H a
  have h₄ := cleanupTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) n (n * d) a
  exact joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

def tableInTime {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    StateTransition.EvalsToInTime (TM2.step (program d e hd he))
      ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩
      (some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩)
      ((timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length)) where
  steps := tableSteps G H
  evals_in_steps := tableTrace d e hd he G H a
  steps_le_m := tableSteps_le G H

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddingTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def execution {n d m : Nat} (table : PortTables.Table n d) (h : n ≤ m) (hd : 0 < d) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize_), (((), none), ()),
        initialTapes n (n * d) (m - n) (initialOutput (m := m) table)⟩
      (some (cfg d none m (m * d) 0
        (PortTables.tableBits (PreprocessingPaddingTables.pad table h))))
      ((MachinePaddingCertificate.timePolynomial d).eval
        (MachinePaddingBounds.inputSize n (n * d) (m - n) (initialOutput (m := m) table))) where
  steps := steps d n (n * d) (initialOutput (m := m) table) (m - n) + 1
  evals_in_steps := by
    have run := paddingTrace d hd (m - n) n (n * d) (initialOutput (m := m) table)
    have hv : n + (m - n) = m := Nat.add_sub_of_le h
    have he : n * d + (m - n) * d = m * d := by rw [← Nat.add_mul, hv]
    have hout : initialOutput (m := m) table ++ paddingBits d n (n * d) (m - n) =
        PortTables.tableBits (PreprocessingPaddingTables.pad table h) := by
      rw [PreprocessingPaddingWords.tableBits_pad]
      rfl
    rw [hv, he, hout] at run
    convert run using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  steps_le_m := by
    simp only [MachinePaddingCertificate.timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d n (n * d) (m - n) (initialOutput (m := m) table)) 1

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineVertexPadding
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.counted_count _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_current _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.paddingView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

theorem splitTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineTableSplit.exactSteps n (n * d)
      (PreprocessingPaddingWords.rowsBits t)]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory (PortTables.tableBits t) (PreprocessingPaddingWords.rowsBits t)
          (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ := by
  have h := Placement.trace splitTape splitView splitView_left splitView_right
    (Label.splitCode (d := d)) (some (.powerCode .init)) (fun _ => [])
    (MachineTableSplit.program (σ := σ × Bool)) (program d hd) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n (n * d) (PreprocessingPaddingWords.rowsBits t)
      (ambient, false) register)
  simpa only [Placement.configuration, Placement.label, splitInitialTapes, splitResultTapes,
    ← tableBits_split] using h

theorem powerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge : List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineCeilingPower.totalTime ExpanderFamily.growth n]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory input output (encodeWord n) edge [] [] [] []⟩) =
      some ⟨some .dartSeed, ((ambient, false), none),
        memory input output (encodeWord n) edge (encodeWord (PreprocessingLevels.paddedSize n))
          (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    (Label.powerCode (d := d)) (some .dartSeed) (memory input output [] edge [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) (program d hd)
    (fun _ => rfl) _ _ _ (MachineCeilingPower.paddingTrace n ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes] using h

theorem affineOutputTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (coefficient : Nat) (seed scan restore : Label d) (exit : Option (Label d))
    (atSeed : program (σ := σ) d hd seed = MachineUnaryAffineAt.seed (σ := σ × Bool) .output 0 scan)
    (atScan : program (σ := σ) d hd scan = MachineUnaryAffineAt.scan (σ := σ × Bool) .power .scratch .output
      coefficient scan restore)
    (atRestore : program (σ := σ) d hd restore = Reduction.MachineTransfer.loopAt (σ := σ × Bool)
      .scratch .power id false restore exit)
    (input output vertex edge level fuel relation : List Bool) (m : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[1 + 2 * (m + 1)]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨exit, ((ambient, false), none),
        memory input (encodeWord (coefficient * m) ++ output) vertex edge
          (encodeWord m) level fuel relation⟩ := by
  have hs : (advance (TM2.step (program d hd)))^[1]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨some scan, ((ambient, false), register),
        memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation⟩ := by
    change some (TM2.stepAux (program d hd seed) _ _) = _
    rw [atSeed]
    simp [MachineUnaryAffineAt.seed, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, encodeWord, memory]
  let base := memory input output vertex edge (encodeWord m) level fuel relation
  have ht := MachineUnaryAffineAt.affineTrace Tape.power Tape.scratch Tape.output
    (by decide) (by decide) (by decide) coefficient scan restore exit (program d hd)
    atScan atRestore base m 0 [] output (ambient, false) register
  have hstart : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord 0 ++ output) =
      memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  have hfinish : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord (coefficient * m + 0) ++ output) =
      memory input (encodeWord (coefficient * m) ++ output) vertex edge
        (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  rw [hstart, hfinish] at ht
  exact appendTrace _ hs ht

theorem headersTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[4 * (m + 1) + 2]
      (some ⟨some .dartSeed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory input (encodeWords [m, m * d] ++ output) vertex edge (encodeWord m) level [] []⟩ := by
  have h₁ := affineOutputTrace d hd d .dartSeed .dartScan .dartRestore (some .vertexSeed)
    rfl rfl rfl input output vertex edge level [] [] m ambient register
  have h₂ := affineOutputTrace d hd 1 .vertexSeed .vertexScan .vertexRestore (some .copyFirst)
    rfl rfl rfl input (encodeWord (d * m) ++ output) vertex edge level [] [] m ambient none
  have h := appendTrace _ h₁ h₂
  simpa only [Nat.one_mul, Nat.mul_comm d m, encodeWords, List.append_nil, List.append_assoc,
    show (1 + 2 * (m + 1)) + (1 + 2 * (m + 1)) = 4 * (m + 1) + 2 by omega] using h

theorem copyPowerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * (m + 2)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some (.subtractCode .subtract), ((ambient, false), none),
        memory input output vertex edge (encodeWord m) level (encodeWord m) []⟩ := by
  have h := MachineCopy.copyTrace Tape.power Tape.fuel Tape.scratch
    (by decide) (by decide) (by decide) false (Label.copyFirst (d := d)) .copySecond
    (some (.subtractCode .subtract)) (program d hd) rfl rfl
    (memory input output vertex edge (encodeWord m) level [] []) rfl (ambient, false) register
  simpa only [memory, encodeWord_length, List.append_nil, update_fuel] using h

theorem subtractTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge power level : List Bool) (n m : Nat) (hnm : n ≤ m)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * n + 2]
      (some ⟨some (.subtractCode .subtract), ((ambient, false), register),
        memory input output (encodeWord n) edge power level (encodeWord m) []⟩) =
      some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input output (encodeWord n) edge power level (encodeWord (m - n)) []⟩ := by
  have h := Placement.trace subtractTape subtractView subtractView_left subtractView_right
    (Label.subtractCode (d := d)) (some (.rowsCode (.inr .initialize_)))
    (memory [] [] [] edge power [] [] [])
    (MachineCloudPadding.program (σ := σ)) (program d hd) (fun _ => rfl) _ _ _
    (MachineCloudPadding.subtractTrace input output level n m hnm ambient register)
  simpa only [Placement.configuration, Placement.label, subtractTapes] using h

/-- The checked padding-row machine is transported through alphabet/state
equalities and a static tape placement. No row execution is assumed. -/
theorem rowsTrace {σ : Type} {n d m : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (hnm : n ≤ m) (input power level : List Bool) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[rowTime (m := m) t]
      (some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input (MachinePaddingTable.initialOutput (m := m) t)
          (encodeWord n) (encodeWord (n * d)) power level (encodeWord (m - n)) []⟩) =
      some ⟨some .cleanVertex, ((ambient, false), none),
        memory input (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))
          (encodeWord m) (encodeWord (m * d)) power level (encodeWord 0)
          MachineDummyRows.trueBits⟩ := by
  have hraw := (MachinePaddingTable.execution t hnm hd).evals_in_steps
  change (advance (TM2.step (MachinePaddingRows.program d hd)))^[rowTime (m := m) t]
    (some ⟨some (.inr .initialize_), (((), none), ()),
      MachinePaddingRows.initialTapes n (n * d) (m - n)
        (MachinePaddingTable.initialOutput (m := m) t)⟩) =
    some (MachinePaddingRows.cfg d none m (m * d) 0
      (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))) at hraw
  have hb := MachineAlphabetTransport.successfulTrace rowAlphabet_eq
    (MachinePaddingRows.program d hd) _ _ _ hraw
  have hf := frameTrace
    (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd))
    (ambient, false) _ _ _ hb
  have hs := MachineStateEquiv.trace (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))
    _ _ _ hf
  have hp := Placement.trace rowTape rowView rowView_left rowView_right
    (Label.rowsCode (d := d)) (some .cleanVertex) (memory input [] [] [] power level [] [])
    (rowProgram d hd (σ := σ)) (program d hd) (fun _ => rfl) _ _ _ hs
  simpa only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    MachineStateFrame.frameConfiguration, MachineAlphabetTransport.configuration_mk,
    rowCastTapes, MachinePaddingRows.cfg, rowStateEquiv, Equiv.coe_fn_mk,
    rowInitialTapes, rowFinalTapes] using hp

theorem cleanupTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output level : List Bool) (m : Nat) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[cleanupTime d m]
      (some ⟨some .cleanVertex, ((ambient, false), none),
        memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
          (encodeWord 0) MachineDummyRows.trueBits⟩) =
      some ⟨none, ((ambient, false), none), memory input output [] [] [] level [] []⟩ := by
  have h₁ := (MachineDrain.drainInTime Tape.vertex (Label.cleanVertex (d := d)) (some .cleanEdge)
    (program d hd) rfl
    (memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₂ := (MachineDrain.drainInTime Tape.edge (Label.cleanEdge (d := d)) (some .cleanPower)
    (program d hd) rfl
    (memory input output [] (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₃ := (MachineDrain.drainInTime Tape.power (Label.cleanPower (d := d)) (some .cleanRelation)
    (program d hd) rfl
    (memory input output [] [] (encodeWord m) level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₄ := (MachineDrain.drainInTime Tape.relation (Label.cleanRelation (d := d)) (some .cleanFuel)
    (program d hd) rfl
    (memory input output [] [] [] level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₅ := (MachineDrain.drainInTime Tape.fuel (Label.cleanFuel (d := d)) none
    (program d hd) rfl (memory input output [] [] [] level (encodeWord 0) [])
    (ambient, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, memory, encodeWord_length, MachineDummyRows.trueBits_length,
    update_vertex, update_edge, update_power, update_relation, update_fuel] at h₁ h₂ h₃ h₄ h₅
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅
  have ht : cleanupTime d m = (((m + 2 + (m * d + 2)) + (m + 2)) + 8193) + 2 := by
    unfold cleanupTime
    omega
  rw [ht]
  exact h

/-- The whole table transformation begins with only its original encoding.
Every row-emitter counter and the updated prefix are produced by this run. -/
theorem vertexPaddingTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[totalTime t]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  let m := PreprocessingLevels.paddedSize n
  let level := encodeWord (PreprocessingLevels.boundedLevel n)
  let input := PortTables.tableBits t
  let rows := PreprocessingPaddingWords.rowsBits t
  let initialOutput := MachinePaddingTable.initialOutput (m := m) t
  have h₁ := splitTrace hd t ambient register
  have h₂ := powerTrace d hd input rows (encodeWord (n * d)) n ambient none
  have h₃ := headersTrace d hd input rows (encodeWord n) (encodeWord (n * d)) level m ambient none
  have h₄ := copyPowerTrace d hd input initialOutput (encodeWord n) (encodeWord (n * d))
    level m ambient none
  have h₅ := subtractTrace d hd input initialOutput (encodeWord (n * d)) (encodeWord m)
    level n m (PreprocessingLevels.le_paddedSize n) ambient none
  have h₆ := rowsTrace hd t (PreprocessingLevels.le_paddedSize n) input (encodeWord m) level ambient
  have h₇ := cleanupTrace d hd input
    (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
    level m ambient
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _
    (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅) h₆) h₇
  have ht : totalTime t =
      (((((MachineTableSplit.exactSteps n (n * d) rows +
        MachineCeilingPower.totalTime ExpanderFamily.growth n) + (4 * (m + 1) + 2)) +
        (2 * (m + 2))) + (2 * n + 2)) + rowTime (m := m) t) + cleanupTime d m := by
    dsimp only [totalTime, otherTime, m, rows]
    omega
  rw [ht]
  exact h

theorem totalTime_le {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    totalTime t ≤ (timePolynomial d).eval (PortTables.tableBits t).length := by
  have hrow := (MachinePaddingTable.execution t (PreprocessingLevels.le_paddedSize n) hd).steps_le_m
  change rowTime (m := PreprocessingLevels.paddedSize n) t ≤
    (MachinePaddingCertificate.timePolynomial d).eval
      (MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
        (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t)) at hrow
  have hmono := natPolynomial_eval_mono (MachinePaddingCertificate.timePolynomial d) (intermediate_bound t)
  have h := Nat.add_le_add (otherTime_le t) (hrow.trans hmono)
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp] using h

/-- Complete runtime certificate from the original input alone, with an
explicit clean final frame and an actual polynomial in its encoded length. -/
def vertexPaddingInTime {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program d hd))
      ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) where
  steps := totalTime t
  evals_in_steps := vertexPaddingTrace hd t ambient register
  steps_le_m := totalTime_le hd t

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.familyView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_level_shadow _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level_shadow _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.program_family _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

/-- The actual padding execution stops at the family entry on the same
physical level stack, and preserves both inactive finite states. -/
noncomputable def paddingInTime (H : BaseTable) {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨some familyEntry, clean H d hd, paddedTapes t⟩)
      ((MachineVertexPadding.timePolynomial d).eval (PortTables.tableBits t).length) := by
  let ambient := (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ())
  have run := placeExecution paddingTape paddingView paddingView_left paddingView_right
    paddingLabel (some familyEntry) (fun _ => []) (MachineVertexPadding.program d hd) (program H d hd)
    (fun _ => rfl) (MachineVertexPadding.vertexPaddingInTime hd t ambient none)
  simpa only [Placement.configuration, Placement.label, padding_initial_memory,
    padding_final_memory, initialTapes, paddedTapes, padded, main, clean, ambient] using run

/-- Overlay executes on the two archives physically produced above; only
its output stack changes in the retained outside frame. -/
noncomputable def overlayInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some overlayEntry, clean H d hd, familyTapes H t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  have original := MachineOverlayTable.tableInTime d overlayDegree hd overlayDegree_positive
    (padded t) (PreprocessingStageMaps.familyAt H n) ()
  have framed := MachineStateFrame.frameExecution
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)
    ((f, false), (none : Option Bool))
    original
  have transported := MachineStateEquiv.execution (overlayStates d)
    (MachineStateFrame.frameProgram
      (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (overlaySource d hd))
      ⟨some (.inl .copyFirst), clean H d hd,
        MachineOverlayTable.initialTapes (PortTables.tableBits (padded t)) (rotor H n)⟩
      (some ⟨none, clean H d hd,
        MachineOverlayTable.memory (PortTables.tableBits (padded t)) (rotor H n)
          [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
    simpa only [overlaySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, overlayStates, Equiv.coe_fn_mk, clean, f,
      rotor_familyAt, PreprocessingStageMaps.paddedOverlay, PreprocessingStageMaps.padding,
      padded] using transported
  have run := placeExecution overlayTape overlayView overlayView_left overlayView_right
    overlayLabel none (familyTapes H t) (overlaySource d hd) (program H d hd)
    (fun _ => rfl) sourceRun
  simpa only [Placement.configuration, Placement.label, familyTapes, finalTapes,
    MachineOverlayTable.initialTapes_memory, overlay_memory, overlayEntry] using run

/-- The complete three-phase program executes from the original serialized
input alone, with a polynomial bound in that input's full unary length. -/
noncomputable def execution (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) := by
  let first := paddingInTime H hd t
  let second := familyInTime H hd t
  let third := overlayInTime H hd t
  let firstTwo := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ firstTwo third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := all.steps_le_m.trans ?_ }
  have hn := PortTables.vertices_le_tableBits_length t
  have hf := Nat.mul_le_mul_left MachineExpanderFamilyBounds.inputCoefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 5)
  have ho := natPolynomial_eval_mono (MachineOverlayTable.timePolynomial d overlayDegree)
    (archive_length_le H t)
  have h := Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl ((MachineVertexPadding.timePolynomial d).eval
      (PortTables.tableBits t).length)) hf) ho
  simpa only [timePolynomial, familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def machine (H : BaseTable) (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl .original
  k₁ := .inr (.inr MachineOverlayTable.output)
  Γ := Alphabet
  Λ := Label d
  main := main
  σ := State d
  initialState := clean H d hd
  m := program H d hd

theorem initial_configuration (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    initList (machine H d hd) (PortTables.tableBits t) =
      ⟨some main, clean H d hd, initialTapes t⟩ := by
  have ht : (initList (machine H d hd) (PortTables.tableBits t)).stk = initialTapes t := by
    funext k
    rcases k with k | k
    · cases k <;> simp [initList, machine, initialTapes, memory, MachineVertexPadding.memory]
      rfl
    · rcases k with k | k
      · rcases k with k | k
        · rcases k with k | k <;> cases k <;>
            simp [initList, machine, initialTapes, memory]
        · cases k <;> simp [initList, machine, initialTapes, memory]
      · simp [initList, machine, initialTapes, memory]
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem final_output (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    finalTapes H t (machine H d hd).k₁ =
      PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩) := by
  simp [finalTapes, machine, memory, PortTables.inputBits]

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

theorem initial_configuration (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram H d hd))
        (PortTables.inputBits a) =
      ⟨some MachinePaddedOverlay.main, MachinePaddedOverlay.clean H d hd,
        MachinePaddedOverlay.initialTapes a.2⟩ := by
  change initList (MachinePaddedOverlay.machine H d hd) (PortTables.tableBits a.2) = _
  exact MachinePaddedOverlay.initial_configuration H hd a.2

/-- The raw terminal witness is the actual three-phase execution. No phase
trace, output-size bound, or complexity assertion is an input hypothesis. -/
noncomputable def terminalRun (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram H d hd) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d a))
      ((MachinePaddedOverlay.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachinePaddedOverlay.clean H d hd
  tapes := MachinePaddedOverlay.finalTapes H a.2
  execution := by
    rw [initial_configuration]
    exact MachinePaddedOverlay.execution H hd a.2
  output_eq := MachinePaddedOverlay.final_output H hd a.2

/-- A concrete machine reaches the canonical `haltList` encoding of the
existing executable preprocessing map in polynomial time. -/
noncomputable def computableInPolyTime (H : BaseTable) (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := d + MachinePaddedOverlay.overlayDegree))
      (PreprocessingStageMaps.paddedOverlay H d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

/-- Finiteness belongs to the exact machine stored in the certificate above. -/
theorem finite_alphabet (H : BaseTable) (d : Nat) (hd : 0 < d) :
    ∀ k, Finite ((computableInPolyTime H d hd).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTableBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/



namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)


/-- Finiteness refers to the exact machine in the preceding certificate. -/
theorem finite_alphabet (H : PreprocessingRegularTables.BaseTable) :
    ∀ k, Finite ((computableInPolyTime H).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_LoopInitializationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

/-- Both stages supply complete executions, cleanup, and polynomial bounds;
the sequential composition includes the physical interstage bit transfer. -/
noncomputable def computableInPolyTime (H : PreprocessingTables.BaseTable)
    (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * (d + internalDegree))) (finish H d) := by
  change TM2ComputableInPolyTime _ _
    (fun input => PreprocessingStageMaps.lazy (d + internalDegree)
      (PreprocessingStageMaps.paddedOverlay H d input))
  exact MachineSequential.composeBits (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))

theorem finite_alphabet (H : PreprocessingTables.BaseTable) (d : Nat) (hd : 0 < d) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime H d hd).tm :=
  MachineFiniteAlphabet.composeBits
    (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))
    (MachinePaddedOverlayRuntime.finite_alphabet H d hd)
    (MachineLazyTableRuntime.finite_alphabet (d + internalDegree)
      (finish_degree_positive d hd))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime



/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRuntime
open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def tablePolynomialTime (H : PreprocessingTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingTables.degree))
      (PreprocessingTables.output H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := 2 * ((internalDegree + 1) + internalDegree)))
    (fun t => PreprocessingFinishRuntime.finish H (internalDegree + 1)
      (PreprocessingStageMaps.regular H t))
  exact MachineSequential.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

theorem finiteAlphabet (H : PreprocessingTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (tablePolynomialTime H).tm :=
  MachineFiniteAlphabet.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))
    (MachineRegularTableRuntime.finite_alphabet H)
    (PreprocessingFinishRuntime.finite_alphabet H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRuntime



/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationMachine


open Turing UniqueGamesTheorem.Foundations Complexity
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end PerfectCompleteness.NormalizationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_PreprocessingMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.PreprocessingMachine

open Turing UniqueGamesTheorem.Foundations
open Complexity PCP Target

noncomputable section

def preprocessing : RoundComputation.PreprocessingCertificate PCPSource.baseTable :=
  PreprocessingRuntime.tablePolynomialTime PCPSource.baseTable

theorem preprocessing_finite_alphabet :
    MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm :=
  PreprocessingRuntime.finiteAlphabet PCPSource.baseTable

def round :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build PCPSource.baseTable) :=
  RoundComputation.tablePolynomialTime PCPSource.baseTable preprocessing

theorem round_finite_alphabet : MachineFiniteAlphabet.FiniteAlphabet round.tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet PCPSource.baseTable
    preprocessing preprocessing_finite_alphabet

def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits formulaBits PCPSource.rawFormula :=
  MachineTableIteration.gapMapCertificate PCPSource.baseTable round

theorem finite_alphabet :
    MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  TableIterationFiniteAlphabet.gapMap PCPSource.baseTable round round_finite_alphabet

end
end PerfectCompleteness.PreprocessingMachine


namespace PerfectCompleteness.PCPSourceMachine

open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

def normalizedComputation :
    TM2ComputableInPolyTime formulaBits formulaBits PCPSource.normalizedFormula := by
  change TM2ComputableInPolyTime formulaBits formulaBits
    (fun formula => Normalization.normalize (PCPSource.rawFormula formula))
  exact MachineSequential.composeBits PreprocessingMachine.computableInPolyTime
    NormalizationMachine.computableInPolyTime

theorem normalized_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet normalizedComputation.tm :=
  MachineFiniteAlphabet.composeBits PreprocessingMachine.computableInPolyTime
    NormalizationMachine.computableInPolyTime PreprocessingMachine.finite_alphabet
    NormalizationMachine.computation_finiteAlphabet

def rawComputation : TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits rawSource := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => PCPSource.normalizedFormula (BinaryLanguage.totalRename input))
  exact MachineSequential.composeBits BinaryInputReduction.computation normalizedComputation

theorem raw_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet rawComputation.tm :=
  MachineFiniteAlphabet.composeBits BinaryInputReduction.computation normalizedComputation
    BinaryInputReduction.computation_finiteAlphabet normalized_finiteAlphabet

end
end PerfectCompleteness.PCPSourceMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedCallBudgetLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedParameters

open FixedRows AscendingBranching

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

def projectionProbability (n : Nat) : ℚ := 1 / (p.cubeSize n : ℚ) ^ 2

theorem projectionProbability_bounds (n : Nat) :
    0 < projectionProbability p n ∧ projectionProbability p n < 1 :=
  FixedBranching.rational_probability (p.cube_errors n).1

end
end PerfectCompleteness.FixedParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_FixedRankContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedRankContradiction

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

def gamma (height : Nat) : ℝ :=
  UpperParameterScalars.gamma (InitialParameters.useful δ) p.plan.density
    (InitialParameters.inverse δ) p.plan.order (FixedRows.rows p.plan height)

end
end PerfectCompleteness.FixedRankContradiction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
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

def reconstructRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) : Arrays slots rows :=
  reconstruct rows repeats p slots record.1 record.2.1 record.2.2

def readRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) :
    Record rows repeats p slots :=
  let split := splitTape rows repeats p chosen q slots ω
  (split.1,
    (fun call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (cutSlots p slots)) (split.2.1 call),
      belowEvaluate rows repeats chosen q (cutSlots p slots) split.2.2))

def reconstructNumbered (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (values : Fin (OriginalCutCalls.count rows repeats n (m + 1)) → H (cutSlots p slots))
    (below : BelowArrays rows p slots) : Arrays slots rows :=
  reconstruct rows repeats p slots exterior (fun call => values (callNumbering rows repeats p call)) below

end
end PerfectCompleteness.OriginalWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalCutBucketReplacement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
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

def replaceRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    Record rows repeats p slots :=
  (record.1, (replaceValues rows repeats p slots record.2.1 a fresh, record.2.2))

end
end PerfectCompleteness.OriginalCutBucketReplacement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalWholeCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

def recordLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (OriginalWholeCut.Record rows repeats p slots) :=
  (OriginalWholeCutTape.exteriorLaw rows repeats p slots).product
    ((valuesLaw rows repeats p chosen q slots).product
      (belowArraysLaw rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)))

end
end PerfectCompleteness.OriginalWholeCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalOwnBucketSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
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

attribute [local instance 2000] valuesChildrenFintype

def recordEquiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Record rows repeats p slots ≃ BucketTape rows p slots × Complement rows repeats p slots where
  toFun record :=
    ((valuesEquiv rows repeats p (H (cutSlots p slots)) record.2.1).1,
      (record.1,
        ((valuesEquiv rows repeats p (H (cutSlots p slots)) record.2.1).2, record.2.2)))
  invFun z :=
    (z.2.1, ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm (z.1, z.2.2.1),
      z.2.2.2))
  left_inv record := by
    rcases record with ⟨exterior, values, below⟩
    change (exterior, ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm
      (valuesEquiv rows repeats p (H (cutSlots p slots)) values), below)) = _
    rw [Equiv.symm_apply_apply]
  right_inv z := by
    rcases z with ⟨own, exterior, other, below⟩
    change
      (((valuesEquiv rows repeats p (H (cutSlots p slots)))
          ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm (own, other))).1,
        (exterior,
          (((valuesEquiv rows repeats p (H (cutSlots p slots)))
            ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm (own, other))).2,
            below))) = _
    rw [Equiv.apply_symm_apply]

def assembleRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    Record rows repeats p slots :=
  (recordEquiv rows repeats p slots).symm (own, complement)

@[simp] theorem recordEquiv_own (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) (a : BucketSampler.Direction (rows (m + 1))) :
    (recordEquiv rows repeats p slots record).1 a =
      record.2.1 (OriginalCutCalls.ownBucket rows repeats p a) :=
  valuesEquiv_own rows repeats p (H (cutSlots p slots)) record.2.1 a

@[simp] theorem split_assembleRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    recordEquiv rows repeats p slots (assembleRecord rows repeats p slots own complement) =
      (own, complement) :=
  (recordEquiv rows repeats p slots).apply_symm_apply (own, complement)

@[simp] theorem assembleRecord_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) :
    assembleRecord rows repeats p slots (recordEquiv rows repeats p slots record).1
        (recordEquiv rows repeats p slots record).2 = record :=
  (recordEquiv rows repeats p slots).symm_apply_apply record

@[simp] theorem assembleRecord_exterior (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    (assembleRecord rows repeats p slots own complement).1 = complement.1 := rfl

@[simp] theorem assembleRecord_below (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    (assembleRecord rows repeats p slots own complement).2.2 = complement.2.2 := rfl

@[simp] theorem assembleRecord_own (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (assembleRecord rows repeats p slots own complement).2.1
        (OriginalCutCalls.ownBucket rows repeats p a) = own a :=
  valuesEquiv_symm_own rows repeats p (H (cutSlots p slots)) own complement.2.1 a

@[simp] theorem assembleRecord_other (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (call : OtherIndex rows repeats p) :
    (assembleRecord rows repeats p slots own complement).2.1 (otherCall rows repeats p call) =
      complement.2.1 call :=
  valuesEquiv_symm_other rows repeats p (H (cutSlots p slots)) own complement.2.1 call

def zeroOwnReconstruction (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (complement : Complement rows repeats p slots) : Arrays slots rows :=
  reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots 0 complement)

def background (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (complement : Complement rows repeats p slots) :
    HierarchicalMatrixTable.Background (rows := rows) slots (WholeArrayInteriorExterior.upperNode p) :=
  HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
    (zeroOwnReconstruction rows repeats p slots complement)

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) := Fintype.ofFinite _

def backgroundLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) :=
  (FiniteDistribution.uniform (Complement rows repeats p slots)).pushforward
    (background rows repeats p slots)

end
end PerfectCompleteness.OriginalOwnBucketSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedComparisonErrorsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedAdvice

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {branch : Nat → Nat} {t : Nat} {Ω P : Type*} [Fintype Ω] [Fintype P]
  (S : HierarchicalAdviceExperiment.Experiment branch (FixedRows.rows p.plan) p.plan.depth t Ω)

local instance backgroundFintype_r92c44a_1 : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _
local instance rowSpaceFintype_r92c44a_1 : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _
local instance inputFintype_r92c44a_1 :
    (b : HierarchicalAdviceExperiment.Background S) → Fintype (HierarchicalAdviceExperiment.Input S b) :=
  HierarchicalAdviceExperiment.inputFintype S
theorem rows_positive : 0 < FixedRows.rows p.plan (Nodes.height S.upper) := by
  exact p.plan.rows_pos (p.plan.depth - Nodes.height S.upper)

end
end PerfectCompleteness.HierarchicalFixedAdvice


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_HierarchicalFixedAdviceFamilyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

variable {branch : Nat → Nat} {t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment
    branch (FixedRows.rows p.plan) p.plan.depth t (Ω o))

local instance backgroundFiberFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) := Fintype.ofFinite _

local instance inputFintype (z : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Input S z) :=
  HierarchicalAdviceFamily.inputFintype S z

local instance valueFintype_r92c44a_1 (z : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S z) :=
  HierarchicalAdviceFamily.valueFintype S z
local instance coarseFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

omit [Fintype O] in
theorem rows_positive (o : O) :
    0 < FixedRows.rows p.plan (Nodes.height (S o).upper) :=
  HierarchicalFixedAdvice.rows_positive p (S o)

def predictionDifference (outer : FiniteDistribution O) : ℝ :=
  (HierarchicalAdviceFamily.originalLaw S outer p.plan.order).probability
      (HierarchicalAdviceFamily.prediction S (useful δ) p.plan.order p.plan.density) -
    rhoPred (useful δ) p.plan.density *
      (HierarchicalAdviceFamily.originalLaw S outer p.plan.order).probability
        (fun x => HierarchicalAdviceFamily.J S (useful δ) p.plan.order p.plan.density
          (HierarchicalAdviceFamily.observe S p.plan.order x))

end
end PerfectCompleteness.HierarchicalFixedAdviceFamily


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCutBridge
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
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

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

def reconstruct (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : NumberedRecord rows repeats p slots) : Arrays slots rows :=
  reconstructNumbered rows repeats p slots record.1 record.2.1 record.2.2

end
end PerfectCompleteness.OriginalWholeCutBridge

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalUniformCutBase
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalUniformCutBase

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

attribute [local instance 2000] instFintypeProd

def assembleEquiv
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    ((Fin (rows (n + 1)) → H slots) × ChildArrays rows slots) ≃ Arrays slots rows where
  toFun z := WholeArraySampler.assemble slots rows z.1 z.2
  invFun arrays := (arrays (.inl ()), fun child node => arrays (.inr (child, node)))
  left_inv z := by
    rcases z with ⟨root, children⟩
    rfl
  right_inv arrays := by
    funext node
    rcases node with u | ⟨child, node⟩
    · cases u
      rfl
    · rfl

end
end PerfectCompleteness.OriginalUniformCutBase

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalUniformCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalUniformCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalUniformCutBase.valuesChildrenFintype

variable {branch : Nat → Nat} {n m t : Nat}

def recordStepEquiv (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Record rows repeats (.step i p) slots ≃
      WholeArraySampler.RootTape rows repeats (.step i p) slots ×
        (Record rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows)) :=
  (OriginalWholeCutTape.regroupStep
    (D := BucketSampler.Direction (rows (n + 1)))
    (T := TerminalCalls.TerminalIndex repeats (.step i p))
    (C := OriginalCutCalls.Index rows repeats p)
    (S := H (cutSlots (.step i p) slots))
    (E := OriginalTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots))
    (L := Exterior rows repeats p (childSlots slots i))
    (O := (j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows)
    (B := BelowArrays rows p (childSlots slots i))).symm.trans
      (Equiv.prodCongr
        (Equiv.piCongrRight (fun _ : BucketSampler.Direction (rows (n + 1)) =>
          (OriginalScalarReconstruction.prefixSplit F2 repeats (.step i p)
            (LeafDomain slots)).symm))
        (Equiv.refl _))

def toStoppedTape (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Record rows repeats p slots → WholeArraySampler.Tape rows repeats p slots
  | _, _, .refl _, slots, record =>
      reconstructRecord rows repeats (.refl _) slots record
  | _, _, .step i p, slots, record =>
      let split := recordStepEquiv rows repeats i p slots record
      WholeCutSampler.stepEquiv i
        (WholeArraySampler.RootTape rows repeats (.step i p) slots)
        (WholeArraySampler.Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)
        (split.1, (toStoppedTape rows repeats p (childSlots slots i) split.2.1,
          split.2.2))

def referenceLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Record rows repeats p slots) :=
  (exteriorLaw rows repeats p slots).product
    ((FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p =>
        FiniteDistribution.uniform (H (cutSlots p slots)))).product
      (FiniteProduct.law (fun child : Fin (branch m) =>
        FiniteDistribution.uniform (Arrays (childSlots (cutSlots p slots) child) rows))))

end
end PerfectCompleteness.OriginalUniformCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_OriginalWholeCutProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem exterior_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) →
      Exterior rows repeats p left = Exterior rows repeats p right := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro left right hs; rfl
      | step i p =>
          intro left right hs
          have hroot := OriginalScalarProjection.scalarExterior_eq repeats (.step i p) left right hs
          have hselected := ih p (childSlots left i) (childSlots right i)
            (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
          have hord :
              ((j : RecursiveSampler.OffPath i) → Arrays (childSlots left j.val) rows) =
                ((j : RecursiveSampler.OffPath i) → Arrays (childSlots right j.val) rows) :=
            congrArg (fun A : RecursiveSampler.OffPath i → Type => (j : RecursiveSampler.OffPath i) → A j)
              (funext (fun j => congrArg
                (fun ss : Slots branch n → Fin t → MixedSupport.Slot => Arrays ss rows)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs j)))
          exact congrArg₂ (fun A B : Type => A × B)
            (congrArg (fun A : Type => BucketSampler.Direction (rows (n + 1)) → A) hroot)
            (congrArg₂ (fun A B : Type => A × B) hselected hord)

def exteriorEquiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) :
    Exterior rows repeats p left ≃ Exterior rows repeats p right :=
  Equiv.cast (exterior_eq rows repeats p left right hs)

end
end PerfectCompleteness.OriginalWholeCutProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

def oldRecord (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p r slots) :
    OriginalWholeCut.Record rows repeats (p.append r) slots :=
  (record.1.1, (fun call => record.2.1 (.inl call), record.2.2))

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

def descendRecord (rows repeats : Nat → Nat) :
    {n j i : Nat} → (p : Path branch n j) → (r : Path branch j (i + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        OriginalWholeCut.Record rows repeats (p.append r) slots →
          OriginalWholeCut.Record rows repeats r (cutSlots p slots)
  | _, _, _, .refl _, _, _, record => record
  | _, _, _, .step child p, r, slots, record =>
      descendRecord rows repeats p r (childSlots slots child)
        (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))

def rootBuckets (rows repeats : Nat → Nat) :
    {j i : Nat} → (r : Path branch (j + 1) (i + 1)) →
      (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot) →
        OriginalWholeCut.Record rows repeats r slots →
          BucketSampler.Tape (rows (j + 1)) (H slots)
  | _, _, .refl _, _, record => record.2.1
  | _, _, .step child r, slots, record => fun direction =>
      OriginalScalarReconstruction.reconstruct F2 repeats (.step child r) (LeafDomain slots)
        (fun terminal => record.2.1 (.inl (direction, terminal))) (record.1.1 direction)

def upperBuckets (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots) :
    BucketSampler.Tape (rows (j + 1)) (H (cutSlots p slots)) :=
  rootBuckets rows repeats r (cutSlots p slots) (descendRecord rows repeats p r slots record)

def replaceArrays (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    Arrays slots rows :=
  SelectedArrayReplacement.replace rows p slots
    (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
    (BucketSampler.evaluate (rows (j + 1)) (id : H (cutSlots p slots) → _)
      (Function.update (upperBuckets rows repeats p r slots record) a fresh))

def pairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  (HierarchicalMatrixTable.backgroundOf slots (upperNode p)
      (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record),
    (NodeEmbedding.matrix (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
        (upperNode p),
      NodeEmbedding.matrix (replaceArrays rows repeats p r slots record a fresh) (upperNode p)))

def enlargedPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      UpperScalarCutReconstruction.Record rows repeats p r slots) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  pairRecord rows repeats p r slots
    (UpperScalarCutReconstruction.oldRecord rows repeats p r slots sample.2) sample.1
    (UpperScalarCutReconstruction.reconstructFresh repeats p r slots
      (UpperScalarCutReconstruction.freshRecord rows repeats p r slots sample.2))

def numberedPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  enlargedPairRecord rows repeats p r slots
    (sample.1, (UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots).symm sample.2)

@[simp] theorem numberedPairRecord_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (record : UpperScalarCutReconstruction.Record rows repeats p r slots) :
    numberedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots record) =
      enlargedPairRecord rows repeats p r slots (a, record) := by
  simp only [numberedPairRecord, Equiv.symm_apply_apply]

end
end PerfectCompleteness.UpperScalarCutBucket

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def freshExteriorLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (FreshExterior repeats p r slots) :=
  OriginalTerminalSplit.exteriorLaw F2 repeats r (LeafDomain (cutSlots p slots))

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.Exterior rows repeats p r slots) :=
  (OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).product
    (freshExteriorLaw repeats p r slots)

def assembledEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((UpperScalarCutCalls.Index rows repeats p r → H (cutSlots (p.append r) slots)) ×
      OriginalWholeCut.ChildArrays rows (cutSlots (p.append r) slots)) ≃
        CutChildGrouping.Assembled (C := UpperScalarCutCalls.Index rows repeats p r)
          (cutSlots (p.append r) slots) rows := Equiv.refl _

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.UpperScalarCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarFreshProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarPairComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i k t : Nat} {K : Type*} [Fintype K]

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype_r92c44a_2 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
def pairLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (assembled : FiniteDistribution (CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
      (cutSlots (p.append r) slots) rows)) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :=
  (directions.product ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    assembled)).pushforward (UpperScalarCutBucket.numberedPairRecord rows repeats p r slots)

end
end PerfectCompleteness.UpperScalarPairComparison

end

section

namespace PerfectCompleteness.UpperStoppedBuckets

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

attribute [local instance 2000] OriginalUniformCutBase.valuesChildrenFintype

variable {branch : Nat → Nat} {n j i t : Nat}

def stoppedRootBuckets (rows repeats : Nat → Nat) :
    {j i : Nat} → (r : Path branch (j + 1) (i + 1)) → i + 1 < j + 1 →
      (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats r slots →
          BucketSampler.Tape (rows (j + 1)) (H slots)
  | _, _, .refl _, hproper, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step child r, _, slots, tape, direction =>
      RecursiveSampler.evaluate F2 repeats (.step child r) (LeafDomain slots)
        (tape (.inl ()) direction)

def stoppedBuckets (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append r) slots) :
    BucketSampler.Tape (rows (j + 1)) (H (cutSlots p slots)) :=
  stoppedRootBuckets rows repeats r hproper (cutSlots p slots)
    (WholeArraySubtreeSplit.extract rows repeats p r slots tape)

end
end PerfectCompleteness.UpperStoppedBuckets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

def projectedPair (rows : Nat → Nat) (p : Path branch n (j + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (arrays : Arrays right rows)
    (buckets : BucketSampler.Tape (rows (j + 1)) (H (cutSlots p right)))
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    HierarchicalAgreementMean.PairRecord (rows := rows) left (upperNode p) :=
  (HierarchicalMatrixTable.backgroundOf left (upperNode p)
      (ChildBlockProjection.arraysPullback rows q arrays),
    (NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows q arrays) (upperNode p),
      NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows q
        (SelectedArrayReplacement.replace rows p right arrays
          (BucketSampler.evaluate (rows (j + 1)) id (Function.update buckets a fresh)))) (upperNode p)))

def stoppedProjectedPair (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      (WholeArraySampler.Tape rows repeats (p.append r) right × H (cutSlots p right))) :
    HierarchicalAgreementMean.PairRecord (rows := rows) left (upperNode p) :=
  projectedPair rows p left right q
    (WholeArraySampler.evaluate rows repeats (p.append r) right sample.2.1)
    (UpperStoppedBuckets.stoppedBuckets rows repeats p r hproper right sample.2.1)
    sample.1 sample.2.2

attribute [local instance] linearMapFintype

end
end PerfectCompleteness.UpperScalarCutProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedUsefulPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedUsefulPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {N j i t : Nat}

abbrev Descriptor (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) :=
  WholeArrayInteriorHiddenLaw.Exterior rows repeats p chosen q right

def externalLaw (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Descriptor rows repeats p chosen q right) :=
  WholeArrayInteriorHiddenLaw.exteriorLaw rows repeats p chosen q right

local instance rowSpaceFintype (p : Path branch N (j + 1))
    (native : Slots branch N → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace native (upperNode p)) := Fintype.ofFinite _

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch N (j + 1))
    (native : Slots branch N → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) native (upperNode p)) :=
  Fintype.ofFinite _

def background (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (external : Descriptor rows repeats p chosen q right) :
    HierarchicalMatrixTable.Background (rows := rows) native (upperNode p) :=
  fun node row => HPullback (ChildBlockProjection.nodeProjection projection node.val)
    (WholeArrayInteriorExterior.nodeArray rows repeats p chosen q right external node row)

def scalarValue (repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (tape : WholeArrayInteriorHiddenLaw.ScalarTape repeats p chosen q right) :
    H (cutSlots p native) :=
  HPullback (CutGroupedProjection.cutProjection p projection)
    (RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain (cutSlots p right)) tape)

def nativeScalarLaw (repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a)) :
    FiniteDistribution (H (cutSlots p native)) :=
  (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right))).pushforward
    (HPullback (CutGroupedProjection.cutProjection p projection))

def scalarLaw (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (_external : Descriptor rows repeats p chosen q right) :
    FiniteDistribution (NodeEmbedding.RowSpace native (upperNode p)) :=
  (nativeScalarLaw repeats p chosen q native right projection).pushforward
    (CutNodeRows.cutRowEquiv p native)

def readout (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a)) :=
  WholeArrayBucketsLaw.readout rows repeats p chosen q right
    (scalarValue repeats p chosen q native right projection)
    (id : Descriptor rows repeats p chosen q right → _)

abbrev Sample (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) :=
  BucketSampler.Direction (rows (j + 1)) ×
    (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right × H (cutSlots p right))

def directionLaw (rows : Nat → Nat) (j : Nat) (hrows : 0 < rows (j + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (j + 1))) := by
  letI : Nonempty (BucketSampler.Direction (rows (j + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact FiniteDistribution.uniform _

def actualLaw (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (right : Slots branch N → Fin t → MixedSupport.Slot) (hrows : 0 < rows (j + 1)) :
    FiniteDistribution (Sample rows repeats p chosen q right) :=
  (directionLaw rows j hrows).product
    ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).product
      (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right))))

def observe (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    HierarchicalUsefulCollision.Sample (P := Descriptor rows repeats p chosen q right)
      (rows := rows) native (upperNode p) :=
  let old := readout rows repeats p chosen q native right projection sample.2.1
  ⟨old.1, CutNodeRows.bucketSampleEquiv rows p native
    (sample.1, (old.2, HPullback (CutGroupedProjection.cutProjection p projection) sample.2.2))⟩

def actualPair (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    HierarchicalAgreementMean.PairRecord (rows := rows) native (upperNode p) :=
  UpperScalarCutProjection.projectedPair rows p native right projection
    (WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) right sample.2.1)
    (fun direction => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (cutSlots p right))
      ((WholeArrayBucketsLaw.split rows repeats p chosen q right sample.2.1).1 direction))
    sample.1 sample.2.2

end
end PerfectCompleteness.StoppedUsefulPairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_StoppedProjectedBuckets
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
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

abbrev lowerPath (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedExperiment.lowerPath rows hij (key (n := n) rows hrows base)

def chosen (base : Base (branch := branch) (i := i) (j := j) (t := t)) : Fin (branch j) :=
  StoppedPathHead.child hij (lowerPath (n := n) rows hij hrows base)

def continuation (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    Path branch j (i + 1) :=
  StoppedPathHead.tail hij (lowerPath (n := n) rows hij hrows base)

abbrev projected (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
    (key (n := n) rows hrows base)

abbrev projection (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedProjectedExperiment.projection clauses rows hupper hij designated o
    (key (n := n) rows hrows base)

abbrev Exterior (base : Base (branch := branch) (i := i) (j := j) (t := t)) :=
  StoppedUsefulPairLaw.Descriptor rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows base) (continuation (n := n) rows hij hrows base)
    (projected clauses rows hupper hij designated hrows o base)

abbrev Descriptor := (base : Base (branch := branch) (i := i) (j := j) (t := t)) ×
  Exterior clauses rows repeats hupper hij designated hrows o base

def exteriorLaw (base : Base (branch := branch) (i := i) (j := j) (t := t)) :
    FiniteDistribution (Exterior clauses rows repeats hupper hij designated hrows o base) :=
  StoppedUsefulPairLaw.externalLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows base) (continuation (n := n) rows hij hrows base)
    (projected clauses rows hupper hij designated hrows o base)

def externalLaw (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool) :
    FiniteDistribution (Descriptor clauses rows repeats hupper hij designated hrows o) :=
  CompletionSoundness.sigmaLaw
    (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag)
    (exteriorLaw clauses rows repeats hupper hij designated hrows o)

local instance backgroundFintype : Fintype (HierarchicalMatrixTable.Background (rows := rows)
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

def background (descriptor : Descriptor clauses rows repeats hupper hij designated hrows o) :
    HierarchicalMatrixTable.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o) :=
  StoppedUsefulPairLaw.background rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows descriptor.1)
    (continuation (n := n) rows hij hrows descriptor.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (projected clauses rows hupper hij designated hrows o descriptor.1)
    (projection clauses rows hupper hij designated hrows o descriptor.1) descriptor.2

def scalarLaw (descriptor : Descriptor clauses rows repeats hupper hij designated hrows o) :
    FiniteDistribution (NodeEmbedding.RowSpace
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  StoppedUsefulPairLaw.scalarLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen (n := n) rows hij hrows descriptor.1)
    (continuation (n := n) rows hij hrows descriptor.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (projected clauses rows hupper hij designated hrows o descriptor.1)
    (projection clauses rows hupper hij designated hrows o descriptor.1) descriptor.2

variable (hbranch : ∀ k < j + 1, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment :=
  StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
    hbranch hrows flag σ o

def usefulProbability (κ : ℝ) : ℝ :=
  HierarchicalAdviceFromBuckets.usefulProbability
    (experiment clauses rows repeats hupper hij designated hrows o hbranch flag σ) κ
    (externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
    (background clauses rows repeats hupper hij designated hrows o)
    (scalarLaw clauses rows repeats hupper hij designated hrows o)
    (rows_positive rows hupper hrows o)

end
end PerfectCompleteness.StoppedProjectedBuckets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedDecoderCleanRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedDecoderCleanRate

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

structure Geometry {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
    (n h : Nat) (upper : Nodes (FixedParameters.branch p) n)
    (d : HierarchicalFrozenTables.LowerNodes upper (h + 1)) where
  designated : Fin (FixedParameters.branch p h) → Slots (FixedParameters.branch p) h
  cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  outside : Slots (FixedParameters.branch p) n →
    Fin (FixedRows.sourceLength p.plan hδ) → MixedSupport.Slot
  placeholder : Slots (FixedParameters.branch p) (h + 1) →
    Fin (FixedRows.sourceLength p.plan hδ) → MixedSupport.Slot
  exterior : CleanPhysicalReplay.Exterior (FixedRows.rows p.plan) (FixedRows.repeats p.plan)
    (CleanRecordDecoderInput.path upper d cut) outside placeholder

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {n h : Nat} {upper : Nodes (FixedParameters.branch p) n}
  {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (G : Geometry p n h upper d)

def setup (input : List Bool) :
    CleanDecoderRate.Setup (FixedParameters.branch p) (FixedRows.rows p.plan)
      (FixedRows.repeats p.plan) n h (FixedRows.sourceLength p.plan hδ)
      (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).variables
      (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length
      upper d where
  clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)
  designated := G.designated
  cut := G.cut
  outside := G.outside
  placeholder := G.placeholder
  exterior := G.exterior

theorem cubePositive (height : Nat) : 0 < p.cubeSize height := by
  have hsize := (p.cube_errors height).1
  omega

theorem branchPositive : ∀ k < n, 0 < FixedParameters.branch p k :=
  fun k _ => FixedParameters.branch_pos p k

end
end PerfectCompleteness.FixedDecoderCleanRate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderFamilyLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedDecoderFamilyRate

noncomputable section

open scoped BigOperators Classical
open HierarchicalArrays FixedDecoderCleanRate
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {O : Type*} [Fintype O] {n h : Nat}
  {upper : O → Nodes (FixedParameters.branch p) n}
  {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
  (G : (o : O) → Geometry p n h (upper o) (lower o))
  (input : List Bool)

def setups (o : O) := setup p (G o) input

end
end PerfectCompleteness.FixedDecoderFamilyRate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedSourceChildCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourceChildCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {n height v m : Nat} [NeZero m]
  (path : Path (branch parameters) n (height + 1))
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)

abbrev Calls := Option (WholeCutCalls.Index (rows parameters.plan) (repeats parameters.plan) path)

abbrev Questions := SourceChildMarkedLaw.Questions
  (branch := branch parameters) (n := height)
  (t := sourceLength parameters.plan hδ) (m := m)

abbrev Native (q : Questions (m := m) parameters (height := height)) :=
  CutChildGrouping.Raw (C := Calls parameters path)
    (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan)

abbrev Form (q : Questions (m := m) parameters (height := height)) :=
  ChildBilinearCollisionTransfer.ParentForm (SourceChildMarkedLaw.questionSlots clauses q)

abbrev Sample := SourceChildKernel.Sample (C := Calls parameters path)
  (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated

def markedLaw : FiniteDistribution (Sample parameters path clauses designated) :=
  SourceChildKernel.originalLaw (C := Calls parameters path)
    (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated
    (fun _ => ProjectionPosterior.bernoulli (projectionProbability parameters height : ℝ)
      (by exact_mod_cast (projectionProbability_bounds parameters height).1.le)
      (by exact_mod_cast (projectionProbability_bounds parameters height).2.le))

def uniformLaw : FiniteDistribution
    (Σ q : Questions (m := m) parameters (height := height), Native parameters path clauses q) :=
  CompletionSoundness.sigmaLaw
    (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
      (t := sourceLength parameters.plan hδ) (m := m))
    (fun q => CutChildGrouping.rawLaw (C := Calls parameters path)
      (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan))

variable (F₀ F₁ : (q : Questions (m := m) parameters (height := height)) →
  Native parameters path clauses q → Option (Form parameters clauses q))

def restrictedEvent (sample : Sample parameters path clauses designated) : Bool :=
  let record := SourceChildMarkedLaw.observe (rows parameters.plan) clauses designated sample
  BilinearCollisionTransfer.restrictedCollision
    (F₀ record.1 record.2.2) (F₁ record.1 record.2.2)
    (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses record.1) record.2.1)

def fullEvent (record :
    Σ q : Questions (m := m) parameters (height := height), Native parameters path clauses q) : Bool :=
  BilinearCollisionTransfer.fullCollision (F₀ record.1 record.2) (F₁ record.1 record.2)

end
end PerfectCompleteness.FixedSourceChildCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutUniformCoordinatesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedLowerRawCollision

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height t : Nat}
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (slots : Slots (branch parameters) parameters.plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)

local instance cutDirectionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

local instance lowerDirectionNonempty_r92c44a_1 :
    Nonempty (BucketSampler.Direction (rows parameters.plan
      (Nodes.height (HierarchicalLeftDecoder.LowerNode upper (height + 1) d)))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth -
      Nodes.height (HierarchicalLeftDecoder.LowerNode upper (height + 1) d)))⟩⟩
local instance lowerHFintype_r92c44a_1 :
    Fintype (HierarchicalDecoderTables.LowerH slots upper (height + 1) d) :=
  Fintype.ofFinite _
local instance upperDualFintype_r92c44a_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
theorem branchPositive : ∀ k < parameters.plan.depth, 0 < branch parameters k :=
  fun k _ => branch_pos parameters k

variable {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : WholeCutGrouping.Exterior (rows parameters.plan) (repeats parameters.plan) path slots)

abbrev UpperTable :=
  HierarchicalAllDecoderTables.Input (rows := rows parameters.plan)
    slots upper (height + 1) adviceRows →
      HierarchicalAllDecoderTables.UpperAnswer slots upper

def fullCollisionProbability (table : UpperTable parameters slots upper (height := height)
    (adviceRows := adviceRows)) : ℝ :=
  (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
    (fun direction =>
      (CutChildGrouping.rawLaw
        (C := Option (WholeCutCalls.Index (rows parameters.plan) (repeats parameters.plan) path))
        (WholeCutGrouping.cutSlots path slots) (rows parameters.plan)).probability
          (fun raw => BilinearCollisionTransfer.fullCollision
            (LowerCutDecoderForm.first path slots upper (height + 1) d hnode
              (branchPositive parameters) A table (cutoff parameters.plan hδ) exterior raw)
            (LowerCutDecoderForm.second path slots upper (height + 1) d hnode
              (branchPositive parameters) A table (cutoff parameters.plan hδ) exterior direction raw)))

end
end PerfectCompleteness.FixedLowerRawCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedSourceLowerCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourceLowerCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    path outside placeholder)

abbrev Questions := FixedSourceChildCollision.Questions
  (m := m) parameters (height := height)

abbrev Table (q : Questions (m := m) parameters (height := height)) :=
  SourceQuestionLowerForms.UpperTable (rows := rows parameters.plan)
    path outside clauses upper (height + 1) (adviceRows := adviceRows) q

local instance rowSpaceFintype_r92c44a_3 (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper)

local instance tableFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (Table parameters path outside clauses upper (adviceRows := adviceRows) q) :=
  inferInstanceAs (Fintype (HierarchicalAllDecoderTables.Input (rows := rows parameters.plan)
    (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) adviceRows →
    HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots path outside clauses q) upper))

abbrev TableFamily := (q : Questions (m := m) parameters (height := height)) →
  Table parameters path outside clauses upper (adviceRows := adviceRows) q

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

def first (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows)) :=
  SourceQuestionLowerForms.first path outside placeholder clauses upper (height + 1) d hnode
    (FixedLowerRawCollision.branchPositive parameters) A exterior tables (cutoff parameters.plan hδ)

def second (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  SourceQuestionLowerForms.second path outside placeholder clauses upper (height + 1) d hnode
    (FixedLowerRawCollision.branchPositive parameters) A exterior tables (cutoff parameters.plan hδ)
    direction

def markedProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (FixedSourceChildCollision.markedLaw parameters path clauses designated).probability
    (FixedSourceChildCollision.restrictedEvent parameters path clauses designated
      (first parameters path outside placeholder clauses upper d hnode A exterior tables)
      (second parameters path outside placeholder clauses upper d hnode A exterior tables direction))

def uniformProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (FixedSourceChildCollision.uniformLaw parameters path clauses).probability
    (FixedSourceChildCollision.fullEvent parameters path clauses
      (first parameters path outside placeholder clauses upper d hnode A exterior tables)
      (second parameters path outside placeholder clauses upper d hnode A exterior tables direction))

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots path outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) bg → Prop)
  (density : ℝ)

def tableLaw : FiniteDistribution
    (TableFamily parameters path outside clauses upper (adviceRows := adviceRows)) :=
  FiniteProduct.law (fun q => HierarchicalAllDecoderTables.upperTableLaw
    (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
    σ (useful q) adviceRows density)

end
end PerfectCompleteness.FixedSourceLowerCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_StoppedCleanGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
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

variable {N j i : Nat} (p : Path branch N (j + 1))
  (q : Path branch (j + 1) (i + 1)) (hij : i < j)

section Fixed

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (input : List Bool) {N j i : Nat}
  (p : Path (FixedParameters.branch parameters) N (j + 1))
  (q : Path (FixedParameters.branch parameters) (j + 1) (i + 1))

abbrev OutsideQuestions := SourceQuestionCutSplit.OutsideQuestions (p.append q)
  (FixedRows.sourceLength parameters.plan hδ)
  (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length

def fixedOutside (external : OutsideQuestions parameters input p q) :=
  sourceSlots (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (PreliminarySampler.endpoints
      (SourceQuestionCutSplit.join (p.append q) (fun _ _ => 0) external))

def placeholder : Slots (FixedParameters.branch parameters) (i + 1) →
    Fin (FixedRows.sourceLength parameters.plan hδ) → MixedSupport.Slot :=
  fun _ _ => SourceKeys.slot (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) (.clause 0)

abbrev Exterior (external : OutsideQuestions parameters input p q) :=
  WholeCutGrouping.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (p.append q) (fixedOutside parameters input p q external)

variable (hij : i < j) (external : OutsideQuestions parameters input p q)

def filledExteriorEquiv : Exterior parameters input p q external ≃
    CleanPhysicalReplay.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (p.append q) (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)) :=
  WholeCutExteriorTransport.equiv (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (p.append q) (fixedOutside parameters input p q external)
    (CutSlotAssembly.fill (p.append q) (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)))
    (fun leaf hleaf => (CutSlotAssembly.fill_outside (p.append q)
      (fixedOutside parameters input p q external) (placeholder parameters input (i := i))
      leaf hleaf).symm)

def exteriorEquiv : Exterior parameters input p q external ≃
    CleanPhysicalReplay.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (CleanRecordDecoderInput.path (WholeArrayInteriorExterior.upperNode p)
        (descendant p q hij) (cut p q hij)) (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)) :=
  (filledExteriorEquiv parameters input p q external).trans
    (Equiv.cast (congrArg (fun path : Path (FixedParameters.branch parameters) N (i + 1) =>
    CleanPhysicalReplay.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      path (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)))
    (cleanPath_eq p q hij).symm))

def geometry (exterior : Exterior parameters input p q external) :
    FixedDecoderCleanRate.Geometry parameters N i (WholeArrayInteriorExterior.upperNode p)
      (descendant p q hij) where
  designated := fun _ => firstLeaf (FixedParameters.branch_pos parameters) i
  cut := cut p q hij
  outside := fixedOutside parameters input p q external
  placeholder := placeholder parameters input
  exterior := exteriorEquiv parameters input p q hij external exterior

theorem geometry_path (exterior : Exterior parameters input p q external) :
    CleanRecordDecoderInput.path (WholeArrayInteriorExterior.upperNode p) (descendant p q hij)
      (geometry parameters input p q hij external exterior).cut = p.append q :=
  cleanPath_eq p q hij

end Fixed
end
end PerfectCompleteness.StoppedCleanGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedStoppedDecoderContext
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedDecoderContext

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j)

abbrev Prefixes :=
  GeometricCutSplit.Prefix (FixedParameters.branch parameters) parameters.plan.depth (j.val + 1) ×
    GeometricCutSplit.Prefix (FixedParameters.branch parameters) (j.val + 1) (i.val + 1)

def upperPath (pref : Prefixes parameters i j) :
    Path (FixedParameters.branch parameters) parameters.plan.depth (j.val + 1) :=
  GeometricCutSplit.prefixPath (Nat.succ_le_of_lt j.isLt) pref.1

def lowerPath (pref : Prefixes parameters i j) :
    Path (FixedParameters.branch parameters) (j.val + 1) (i.val + 1) :=
  GeometricCutSplit.prefixPath (Nat.succ_le_succ (Nat.le_of_lt hij)) pref.2

def upper (pref : Prefixes parameters i j) : Nodes (FixedParameters.branch parameters) parameters.plan.depth :=
  WholeArrayInteriorExterior.upperNode (upperPath parameters i j pref)

def lower (pref : Prefixes parameters i j) :
    HierarchicalFrozenTables.LowerNodes (upper parameters i j pref) (i.val + 1) :=
  StoppedCleanGeometry.descendant (upperPath parameters i j pref)
    (lowerPath parameters i j hij pref) hij

@[simp] theorem upper_height (pref : Prefixes parameters i j) :
    Nodes.height (upper parameters i j pref) = j.val + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

def prefixLaw : FiniteDistribution (Prefixes parameters i j) :=
  (GeometricCutSplit.prefixLaw (Nat.succ_le_of_lt j.isLt)
    (fun k _ => FixedParameters.branch_pos parameters k)).product
      (GeometricCutSplit.prefixLaw (Nat.succ_le_succ (Nat.le_of_lt hij))
        (fun k _ => FixedParameters.branch_pos parameters k))

variable (input : List Bool)

abbrev OutsideQuestions (pref : Prefixes parameters i j) :=
  StoppedCleanGeometry.OutsideQuestions parameters input
    (upperPath parameters i j pref) (lowerPath parameters i j hij pref)

abbrev Exterior (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :=
  StoppedCleanGeometry.Exterior parameters input
    (upperPath parameters i j pref) (lowerPath parameters i j hij pref) external

abbrev Advice (pref : Prefixes parameters i j) :=
  ManyGoodRows.RowMap (Block (FixedRows.rows parameters.plan) (upper parameters i j pref))
    parameters.plan.order

abbrev Directions := CanonicalDirections.Tuple (FixedRows.rows parameters.plan) parameters.plan.depth

abbrev Fiber (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :=
  Advice parameters i j pref ×
    (Directions parameters × Exterior parameters i j hij input pref external)

abbrev Context :=
  (pref : Prefixes parameters i j) ×
    (external : OutsideQuestions parameters i j hij input pref) ×
      Fiber parameters i j hij input pref external

def directionLaw : FiniteDistribution (Directions parameters) :=
  CanonicalDirections.law (FixedRows.rows parameters.plan) parameters.plan.depth
    (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))

def fiberLaw (pref : Prefixes parameters i j)
    (external : OutsideQuestions parameters i j hij input pref) :
    FiniteDistribution (Fiber parameters i j hij input pref external) :=
  (FiniteDistribution.uniform (Advice parameters i j pref)).product
    ((directionLaw parameters).product
      (FiniteDistribution.uniform (Exterior parameters i j hij input pref external)))

def law : FiniteDistribution (Context parameters i j hij input) :=
  CompletionSoundness.sigmaLaw (prefixLaw parameters i j hij) (fun pref =>
    CompletionSoundness.sigmaLaw
      (FiniteDistribution.uniform (OutsideQuestions parameters i j hij input pref))
      (fiberLaw parameters i j hij input pref))

def upperNode (context : Context parameters i j hij input) := upper parameters i j context.1

def lowerIndex (context : Context parameters i j hij input) := lower parameters i j hij context.1

def geometry (context : Context parameters i j hij input) :
    FixedDecoderCleanRate.Geometry parameters parameters.plan.depth i.val
      (upperNode parameters i j hij input context) (lowerIndex parameters i j hij input context) :=
  StoppedCleanGeometry.geometry parameters input
    (upperPath parameters i j context.1) (lowerPath parameters i j hij context.1) hij
    context.2.1 context.2.2.2.2

def advice (context : Context parameters i j hij input) :
    ManyGoodRows.RowMap
      (Block (FixedRows.rows parameters.plan) (upperNode parameters i j hij input context))
      parameters.plan.order := context.2.2.1

def direction (context : Context parameters i j hij input) :
    OwnInputReference.LowerVector (FixedRows.rows parameters.plan)
      (HierarchicalLeftDecoder.LowerNode (upperNode parameters i j hij input context)
        (i.val + 1) (lowerIndex parameters i j hij input context)) :=
  (PrefixTests.nodeDirection (FixedRows.rows parameters.plan) i
    ⟨HierarchicalLeftDecoder.LowerNode (upperNode parameters i j hij input context)
      (i.val + 1) (lowerIndex parameters i j hij input context),
      CleanDecoderContext.lowerHeight (upperNode parameters i j hij input context)
        (lowerIndex parameters i j hij input context)⟩ (context.2.2.2.1 i)).val

end
end PerfectCompleteness.FixedStoppedDecoderContext

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedPhysicalStoppedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedPhysicalStoppedComparison

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces FixedParameters FixedRows
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (params : Parameters δ hδ)
  {root h v m : Nat} (p : Path (branch params) root (h + 1))
  (outside : Slots (branch params) root → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch params) (h + 1) → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch params h) → Slots (branch params) h)

theorem beta_nonneg : 0 ≤ (projectionProbability params h : ℝ) := by
  exact_mod_cast (projectionProbability_bounds params h).1.le

theorem beta_le_one : (projectionProbability params h : ℝ) ≤ 1 := by
  exact_mod_cast (projectionProbability_bounds params h).2.le

end
end PerfectCompleteness.FixedPhysicalStoppedComparison

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryOutputLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedPreliminaryGame

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

def game (input : List Bool) :=
  PreliminarySampler.game (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1))

abbrev Strategy (input : List Bool) :=
  PreliminaryStrategy.Strategy (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)

end
end PerfectCompleteness.FixedPreliminaryGame


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

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev Context := FixedStoppedDecoderContext.Context parameters i j hij input

def labeling (strategy : FixedPreliminaryGame.Strategy parameters input) :
    KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ)) :=
  PreliminaryStrategy.extend (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (FixedParameters.branch parameters) parameters.plan.depth
    (FixedRows.sourceLength parameters.plan hδ) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) strategy

def flag : Fin (FixedParameters.branch parameters i.val) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli
    (FixedParameters.projectionProbability parameters i.val : ℝ)
    (FixedPhysicalStoppedComparison.beta_nonneg parameters)
    (FixedPhysicalStoppedComparison.beta_le_one parameters)

def markFamily (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :=
  SlotProjectedExperiment.family
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij pref.1
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))
    (flag parameters i) (labeling parameters input strategy)

abbrev setups :=
  FixedDecoderFamilyRate.setups parameters
    (FixedStoppedDecoderContext.geometry parameters i j hij input) input

def useful (strategy : FixedPreliminaryGame.Strategy parameters input)
    (context : Context parameters i j hij input)
    (record : CleanDecoderRate.Record (setups parameters i j hij input context)) :
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed
        (CleanDecoderRate.context (setups parameters i j hij input context) record))
      (FixedStoppedDecoderContext.upperNode parameters i j hij input context) (i.val + 1) :=
  OriginalDecoderMark.useful
    (markFamily parameters i j hij input strategy context.1)
    (FixedStoppedDecoderContext.upperNode parameters i j hij input context) (i.val + 1)
    (InitialParameters.useful δ)
    (CleanDecoderContext.leftExposed
      (CleanDecoderRate.context (setups parameters i j hij input context) record))

def threshold : ℝ :=
  UpperParameterScalars.tau (InitialParameters.useful δ) parameters.plan.density
    parameters.plan.order (FixedRows.rows parameters.plan (j.val + 1))

abbrev Sample := DecoderFamilyLaw.Sample (setups parameters i j hij input)

local instance sampleFintype : Fintype (Sample parameters i j hij input) :=
  familySampleFintype (setups parameters i j hij input)

def law (strategy : FixedPreliminaryGame.Strategy parameters input) :
    FiniteDistribution (Sample parameters i j hij input) :=
  DecoderFamilyLaw.law (setups parameters i j hij input)
    (labeling parameters input strategy) (useful parameters i j hij input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input) (FixedStoppedDecoderContext.direction parameters i j hij input)
    (threshold parameters j) (FixedStoppedDecoderContext.law parameters i j hij input)
    (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)

abbrev meeting : Sample parameters i j hij input → Bool :=
  DecoderFamilyLaw.meeting (setups parameters i j hij input)

abbrev highAgreement : Sample parameters i j hij input → Bool :=
  DecoderFamilyLaw.highAgreement (setups parameters i j hij input)
    (FixedDecoderCleanRate.branchPositive parameters)
    (FixedRows.cutoff parameters.plan hδ)

end
end PerfectCompleteness.FixedStoppedDecoderLaw

end

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

namespace PerfectCompleteness.FixedStoppedPhysicalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)

def designated : Fin (FixedParameters.branch parameters i.val) →
    Slots (FixedParameters.branch parameters) i.val :=
  fun _ => StoppedCleanGeometry.firstLeaf (FixedParameters.branch_pos parameters) i.val

def flag : Fin (FixedParameters.branch parameters i.val) → FiniteDistribution Bool :=
  fun _ => ProjectedCleanRate.projectionFlag (parameters.cubeSize i.val)
    (FixedDecoderCleanRate.cubePositive parameters i.val)

abbrev Prefixes := FixedStoppedDecoderContext.Prefixes parameters i j
abbrev Context := FixedStoppedDecoderContext.Context parameters i j hij input

def path (pref : Prefixes parameters i j) :=
  (FixedStoppedDecoderContext.upperPath parameters i j pref).append
    (FixedStoppedDecoderContext.lowerPath parameters i j hij pref)

abbrev ChildSample (pref : Prefixes parameters i j) :=
  SourceChildKernel.Sample
    (C := WholeCutCalls.Index (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij pref))
    (t := FixedRows.sourceLength parameters.plan hδ)
    (FixedRows.rows parameters.plan) (clauses input) (designated parameters i)

abbrev Sample := (context : Context parameters i j hij input) ×
  ChildSample parameters i j hij input context.1

abbrev PhysicalSample := StoppedProjectedPhysicalAdvice.Sample
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) parameters.plan.order

def childLaw (pref : Prefixes parameters i j) :
    FiniteDistribution (ChildSample parameters i j hij input pref) :=
  SourceChildKernel.originalLaw
    (C := WholeCutCalls.Index (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij pref))
    (t := FixedRows.sourceLength parameters.plan hδ)
    (FixedRows.rows parameters.plan) (clauses input) (designated parameters i) (flag parameters i)

def law : FiniteDistribution (Sample parameters i j hij input) :=
  CompletionSoundness.sigmaLaw (FixedStoppedDecoderContext.law parameters i j hij input)
    (fun context => childLaw parameters i j hij input context.1)

def read (sample : Sample parameters i j hij input) :
    PhysicalSample parameters i j hij input :=
  let context := sample.1
  let inside := SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) sample.2
  let questions := SourceQuestionCutSplit.join (path parameters i j hij context.1)
    inside context.2.1
  let positions := SourceQuestionRawSwap.positions (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) sample.2
  let exterior := SourcePhysicalSourceSwap.joinedExterior (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (path parameters i j hij context.1) inside context.2.1 context.2.2.2.2
  let raw := SourceQuestionRawSwap.raw (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) sample.2
  ⟨(questions, context.1.1),
    (⟨(context.1.2, (positions, context.2.2.2.1)), (exterior, raw)⟩, context.2.2.1)⟩

abbrev physicalLaw := StoppedProjectedPhysicalAdvice.law
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
  (fun k _ => FixedParameters.branch_pos parameters k)
  (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))
  (flag parameters i) parameters.plan.order

end
end PerfectCompleteness.FixedStoppedPhysicalLaw

end

section

namespace PerfectCompleteness.FixedStoppedNativeLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

local instance contextAdviceFintype
    (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    Fintype (FixedStoppedDecoderContext.Advice parameters i j pref) :=
  UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

abbrev Context := FixedStoppedDecoderContext.Context parameters i j hij input

abbrev setup (context : Context parameters i j hij input) :=
  FixedDecoderCleanRate.setup parameters
    (FixedStoppedDecoderContext.geometry parameters i j hij input context) input

abbrev Sample := (context : Context parameters i j hij input) ×
  CleanDecoderRate.Sample (setup parameters i j hij input context)

theorem path_eq (context : Context parameters i j hij input) :
    CleanDecoderRate.path (setup parameters i j hij input context) =
      FixedStoppedPhysicalLaw.path parameters i j hij context.1 :=
  StoppedCleanGeometry.geometry_path parameters input
    (FixedStoppedDecoderContext.upperPath parameters i j context.1)
    (FixedStoppedDecoderContext.lowerPath parameters i j hij context.1) hij
    context.2.1 context.2.2.2.2

def childRead (context : Context parameters i j hij input) :
    CleanDecoderRate.Sample (setup parameters i j hij input context) ≃
      FixedStoppedPhysicalLaw.ChildSample parameters i j hij input context.1 :=
  sourceSampleEquiv (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (FixedStoppedPhysicalLaw.clauses input) (FixedStoppedPhysicalLaw.designated parameters i)
    (path_eq parameters i j hij input context)

def law : FiniteDistribution (Sample parameters i j hij input) :=
  CompletionSoundness.sigmaLaw (FixedStoppedDecoderContext.law parameters i j hij input)
    (fun context => CleanDecoderRate.rawLaw (setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val))

def sourceRead (sample : Sample parameters i j hij input) :
    FixedStoppedPhysicalLaw.Sample parameters i j hij input :=
  ⟨sample.1, childRead parameters i j hij input sample.1 sample.2⟩

def read (sample : Sample parameters i j hij input) :
    FixedStoppedPhysicalLaw.PhysicalSample parameters i j hij input :=
  FixedStoppedPhysicalLaw.read parameters i j hij input
    (sourceRead parameters i j hij input sample)

end
end PerfectCompleteness.FixedStoppedNativeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedStoppedNativeProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeProjection

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev physicalSample (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  FixedStoppedNativeLaw.read parameters i j hij input sample

abbrev innerTag (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  (StoppedProjectedExperiment.physicalRead (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (physicalSample parameters i j hij input sample).1
    (physicalSample parameters i j hij input sample).2.1).1

abbrev originalQuestions (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  (physicalSample parameters i j hij input sample).1.1

abbrev path (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  FixedStoppedPhysicalLaw.path parameters i j hij sample.1.1

abbrev childSample (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  FixedStoppedNativeLaw.childRead parameters i j hij input sample.1 sample.2

abbrev sources (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  SourcePhysicalTapeLaw.sourceTag (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (path parameters i j hij input sample) (clauses input) (designated parameters i)
    (childSample parameters i j hij input sample)

abbrev flags (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :=
  fun child => SourceChildKernel.rawProjected (FixedRows.rows parameters.plan)
    (clauses input) (designated parameters i) child
    ((childSample parameters i j hij input sample) child).2.2

@[simp] theorem flags_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    (innerTag parameters i j hij input sample).2.1.2 = flags parameters i j hij input sample := rfl

end
end PerfectCompleteness.FixedStoppedNativeProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalExtraCutComparison
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalExtraCutComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat} {K : Type*} [Fintype K]

abbrev Record (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalWholeCutBridge.NumberedRecord rows repeats p slots × H (cutSlots p slots)

def actualLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m) :
    FiniteDistribution (Record rows repeats p slots) :=
  ((exteriorLaw rows repeats p slots).product
    (OriginalPrefixContinuation.assembledLaw
      (OriginalCutCalls.count rows repeats n (m + 1) + 1)
      rows repeats (cutSlots p slots) ν q hbranch)).pushforward
        (ExtraCutCall.splitRecord rows repeats p slots)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

def referenceLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Record rows repeats p slots) :=
  ((OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
    (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
      (FiniteDistribution.uniform (H (cutSlots p slots)))

end
end PerfectCompleteness.OriginalExtraCutComparison

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_OriginalCutCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutCollision

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev PairRecord (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  HierarchicalAgreementMean.PairRecord (rows := rows) slots
    (WholeArrayInteriorExterior.upperNode p)

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) := Fintype.ofFinite _

local instance rowSpaceFintype_r92c44a_4 (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (WholeArrayInteriorExterior.upperNode p)) :=
  Fintype.ofFinite _
def oldRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalExtraCutComparison.Record rows repeats p slots) :
    OriginalWholeCut.Record rows repeats p slots :=
  (NumberedUniformCut.numberRecordEquiv rows repeats p slots).symm record.1

def oldArrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalExtraCutComparison.Record rows repeats p slots) : Arrays slots rows :=
  OriginalWholeCut.reconstructRecord rows repeats p slots (oldRecord rows repeats p slots record)

def replacementArrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (direction : BucketSampler.Direction (rows (m + 1)))
    (record : OriginalExtraCutComparison.Record rows repeats p slots) : Arrays slots rows :=
  OriginalWholeCut.reconstructRecord rows repeats p slots
    (OriginalCutBucketReplacement.replaceRecord rows repeats p slots
      (oldRecord rows repeats p slots record) direction record.2)

def pairRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (m + 1)) ×
      OriginalExtraCutComparison.Record rows repeats p slots) : PairRecord rows p slots :=
  (HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
      (oldArrays rows repeats p slots sample.2),
    (NodeEmbedding.matrix (oldArrays rows repeats p slots sample.2)
      (WholeArrayInteriorExterior.upperNode p),
    NodeEmbedding.matrix (replacementArrays rows repeats p slots sample.1 sample.2)
      (WholeArrayInteriorExterior.upperNode p)))

end
end PerfectCompleteness.OriginalCutCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalCutBucketLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev Background (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  HierarchicalMatrixTable.Background (rows := rows) slots (WholeArrayInteriorExterior.upperNode p)

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (Background rows p slots) := Fintype.ofFinite _

abbrev NativeSample (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Background rows p slots ×
    (BucketSampler.Direction (rows (m + 1)) ×
      (OriginalOwnBucketSplit.BucketTape rows p slots × H (cutSlots p slots)))

def read (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (m + 1)) ×
      OriginalExtraCutComparison.Record rows repeats p slots) : NativeSample rows p slots :=
  (HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
      (OriginalCutCollision.oldArrays rows repeats p slots sample.2),
    (sample.1,
      (OriginalCutBucketReplacement.ownValues rows repeats p slots
        (OriginalCutCollision.oldRecord rows repeats p slots sample.2).2.1, sample.2.2)))

def recordRead (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots) :
    OriginalOwnBucketSplit.BucketTape rows p slots × Background rows p slots :=
  ((OriginalOwnBucketSplit.recordEquiv rows repeats p slots record).1,
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
      (OriginalWholeCut.reconstructRecord rows repeats p slots record))

@[simp] theorem oldRecord_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots) (fresh : H (cutSlots p slots)) :
    OriginalCutCollision.oldRecord rows repeats p slots
        (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh) = record :=
  (NumberedUniformCut.numberRecordEquiv rows repeats p slots).symm_apply_apply record

end
end PerfectCompleteness.OriginalCutBucketLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalCutPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m k t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

def transportPair (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : OriginalCutBucketLaw.NativeSample rows p slots) :
    OriginalCutCollision.PairRecord rows p slots :=
  HierarchicalAgreementMean.pairRecord slots (upperNode p)
    (sample.1, CutNodeRows.bucketSampleEquiv rows p slots sample.2)

def directionsLaw (rows : Nat → Nat) (m : Nat) (hrows : 0 < rows (m + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (m + 1))) := by
  letI : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact FiniteDistribution.uniform _

end
end PerfectCompleteness.OriginalCutPairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutErasure
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutErasure

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def assocTapeEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    WholeArraySampler.Tape rows repeats ((p.append r).append q) slots ≃
      WholeArraySampler.Tape rows repeats (p.append (r.append q)) slots :=
  Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots)
    (p.append_assoc r q))

def upperReadRecord (rows repeats : Nat → Nat) :
    {n j i k : Nat} → (p : Path branch n (j + 1)) →
      (r : Path branch (j + 1) (i + 1)) → (chosen : Fin (branch i)) → (q : Path branch i k) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots →
          OriginalWholeCut.Record rows repeats p slots
  | _, _, _, _, p, .refl _, chosen, q, slots, tape =>
      OriginalWholeCut.readRecord rows repeats p chosen q slots tape
  | _, _, _, _, p, .step upperChild tail, chosen, q, slots, tape =>
      OriginalWholeCut.readRecord rows repeats p upperChild (tail.append (.step chosen q)) slots tape

def upperPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p) :=
  OriginalCutCollision.pairRecord rows repeats p slots
    (a, (OriginalWholeCutBridge.numberRecord rows repeats p slots
      (upperReadRecord rows repeats p r chosen q slots tape), fresh))

end
end PerfectCompleteness.UpperScalarCutErasure

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarPairAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarPairAveraging

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i k t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.UpperScalarPairAveraging

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperCutTriangle
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperCutTriangle

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p)) := Fintype.ofFinite _

variable {Z : Prefix branch j i → Fin (branch i) → Type*}
  [∀ pref c, Fintype (Z pref c)]

local instance rowSpaceFintype_r92c44a_5 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
def modifiedPairLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : 0 < rows (j + 1))
    (projected : (pref : Prefix branch j i) → (c : Fin (branch i)) → Z pref c →
      Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ pref c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots) c s a)
      (projected pref c z s a))
    (choiceLaw : (pref : Prefix branch j i) → (c : Fin (branch i)) → FiniteDistribution (Z pref c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :=
  (GeometricCutSplit.prefixLaw hcut hbranch).mixture (fun pref =>
    UpperScalarPairComparison.pairLaw rows repeats p (GeometricCutSplit.prefixPath hcut pref)
      slots (OriginalCutPairLaw.directionsLaw rows j hrows)
      (ProjectedPrefixComparison.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
        (cutSlots (p.append (GeometricCutSplit.prefixPath hcut pref)) slots)
        (projected pref) (projection pref) (choiceLaw pref) β hβ hβ'))

end
end PerfectCompleteness.UpperCutTriangle

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedUpperPairErrorLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedUpperCutTriangle

open FixedParameters FixedRows RecursiveSpaces DescendantSpaces
open TreeSourceSpaces HierarchicalArrays OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (params : Parameters δ hδ)
  {root upper lower : Nat}

theorem rows_positive (height : Nat) : 0 < rows params.plan height :=
  lt_of_lt_of_le Nat.zero_lt_one (params.plan.rows_pos (params.plan.depth - height))

variable (pref : Path (branch params) root (upper + 1))
  (hcut : lower + 1 ≤ upper + 1)
  (slots : Slots (branch params) root → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)

local instance backgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows params.plan) slots (upperNode pref)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype_r92c44a_6 : Fintype (NodeEmbedding.RowSpace slots (upperNode pref)) :=
  Fintype.ofFinite _
def upperReferenceLaw :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows params.plan) slots (upperNode pref)) :=
  HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
    (OriginalOwnBucketSplit.backgroundLaw (rows params.plan) (repeats params.plan) pref slots)
    (by simpa only [upperNode_height] using rows_positive params (upper + 1))

variable {Z : UpperCutTriangle.Prefix (branch params) upper lower → Fin (branch params lower) → Type*}
  [∀ lowerPref child, Fintype (Z lowerPref child)]
  (projected : (lowerPref : UpperCutTriangle.Prefix (branch params) upper lower) →
    (child : Fin (branch params lower)) → Z lowerPref child →
      Slots (branch params) lower → Fin (sourceLength params.plan hδ) → MixedSupport.Slot)
  (projection : ∀ lowerPref child z s a, MixedSupport.Projection
    (childSlots (cutSlots (pref.append (GeometricCutSplit.prefixPath hcut lowerPref)) slots) child s a)
    (projected lowerPref child z s a))
  (choiceLaw : (lowerPref : UpperCutTriangle.Prefix (branch params) upper lower) →
    (child : Fin (branch params lower)) → FiniteDistribution (Z lowerPref child))

def modifiedPairLaw :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows params.plan) slots (upperNode pref)) :=
  UpperCutTriangle.modifiedPairLaw (rows params.plan) (repeats params.plan) pref hcut slots
    (fun k _ => branch_pos params k) (rows_positive params (upper + 1))
    projected projection choiceLaw (projectionProbability params lower : ℝ)
    (by exact_mod_cast (projectionProbability_bounds params lower).1.le)
    (by exact_mod_cast (projectionProbability_bounds params lower).2.le)

def originalReferenceLaw :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows params.plan) slots (upperNode pref)) :=
  HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
    ((modifiedPairLaw params pref hcut slots projected projection choiceLaw).pushforward Prod.fst)
    (by simpa only [upperNode_height] using rows_positive params (upper + 1))

end
end PerfectCompleteness.FixedUpperCutTriangle

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedWholeCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m j t : Nat}
  (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  {Z : Fin (branch m) → Type*} [∀ child, Fintype (Z child)]
  (projected : (child : Fin (branch m)) → Z child → Slots branch m → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots (cutSlots p slots) child s a) (projected child z s a))

def fullSlots (choices : ProjectedCutChoices.Choices (Z := Z)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p slots
    (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)

theorem fill_native : CutSlotAssembly.fill p slots (cutSlots p slots) = slots :=
  CutSlotAssembly.fill_restrict p slots

def fullProjection (choices : ProjectedCutChoices.Choices (Z := Z)) :
    ∀ s a, MixedSupport.Projection (slots s a) (fullSlots p slots projected choices s a) :=
  fun s a => CutProjectionAssembly.castProjection
    (congrFun (congrFun (fill_native p slots) s) a) rfl
    (CutProjectionAssembly.fillProjection p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices) s a)

end
end PerfectCompleteness.ProjectedWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedUpperPair
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedUpperPair

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

variable (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  {Z : Fin (branch i) → Type*} [∀ child, Fintype (Z child)]
  (projected : (child : Fin (branch i)) → Z child → Slots branch i → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots (cutSlots (p.append r) slots) child s a) (projected child z s a))

local instance rowSpaceFintype_r92c44a_7 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
def pairLaw (rows repeats : Nat → Nat) (hproper : i + 1 < j + 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :=
  (ProjectedCutChoices.choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
    (directions.product
      ((WholeArraySampler.tapeLaw rows repeats (p.append r)
        (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)).product
        (RecursiveSampler.law F2 repeats r
          (LeafDomain (cutSlots p
            (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)))))).pushforward
      (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper slots
        (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)
        (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices)))

end
end PerfectCompleteness.ProjectedUpperPair

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

namespace PerfectCompleteness.FixedSourceGlobalCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    path outside placeholder)

abbrev Questions := FixedSourceChildCollision.Questions
  (m := m) parameters (height := height)

abbrev Table (q : Questions (m := m) parameters (height := height)) :=
  SourceQuestionLowerForms.UpperTable (rows := rows parameters.plan)
    path outside clauses upper (height + 1) (adviceRows := adviceRows) q

local instance rowSpaceFintype_r92c44a_8 (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper)

local instance tableFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (Table parameters path outside clauses upper (adviceRows := adviceRows) q) :=
  inferInstanceAs (Fintype (HierarchicalAllDecoderTables.Input (rows := rows parameters.plan)
    (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) adviceRows →
    HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots path outside clauses q) upper))

abbrev TableFamily := (q : Questions (m := m) parameters (height := height)) →
  Table parameters path outside clauses upper (adviceRows := adviceRows) q

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

def flag : Fin (branch parameters height) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli (projectionProbability parameters height : ℝ)
    (by exact_mod_cast (projectionProbability_bounds parameters height).1.le)
    (by exact_mod_cast (projectionProbability_bounds parameters height).2.le)

abbrev Choice := SourceQuestionKernelJoint.ChoiceTuple
  (branch := branch parameters) (n := height) (t := sourceLength parameters.plan hδ)

def nativeProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
    (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
      (SourceProjectedTag.positionLaw (branch := branch parameters) (n := height)
        (t := sourceLength parameters.plan hδ)).expectation (fun choices =>
          (SourceQuestionRawSwap.kernelLaw
            (C := FixedSourceChildCollision.Calls parameters path)
            (rows parameters.plan) clauses designated (flag parameters) q choices).probability (fun raw =>
              let record := SourceChildMarkedLaw.markedBlocks
                (rows parameters.plan) clauses designated q choices raw
              BilinearCollisionTransfer.restrictedCollision
                (FixedSourceLowerCollision.first parameters path outside placeholder clauses
                  upper d hnode A exterior tables q record.2)
                (FixedSourceLowerCollision.second parameters path outside placeholder clauses
                  upper d hnode A exterior tables direction q record.2)
                (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q) record.1))))

def globalProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
    (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
      (SourceProjectedTag.positionLaw (branch := branch parameters) (n := height)
        (t := sourceLength parameters.plan hδ)).expectation (fun choices =>
          (SourceQuestionRawSwap.kernelLaw
            (C := FixedSourceChildCollision.Calls parameters path)
            (rows parameters.plan) clauses designated (flag parameters) q choices).probability
              (fun raw => SourceQuestionCollisionTransport.globalRestricted path outside placeholder
                clauses upper (height + 1) d (FixedLowerRawCollision.branchPositive parameters)
                A exterior tables (cutoff parameters.plan hδ) designated q choices raw direction)))

def localTables (q : Questions (m := m) parameters (height := height))
    (table : Table parameters path outside clauses upper (adviceRows := adviceRows) q) :
    TableFamily parameters path outside clauses upper (adviceRows := adviceRows) :=
  Function.update (fun _ => fun _ => 0) q table

def localProbability (q : Questions (m := m) parameters (height := height))
    (table : Table parameters path outside clauses upper (adviceRows := adviceRows) q)
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (SourceProjectedTag.positionLaw (branch := branch parameters) (n := height)
    (t := sourceLength parameters.plan hδ)).expectation (fun choices =>
      (SourceQuestionRawSwap.kernelLaw
        (C := FixedSourceChildCollision.Calls parameters path)
        (rows parameters.plan) clauses designated (flag parameters) q choices).probability
          (fun raw => SourceQuestionCollisionTransport.globalRestricted path outside placeholder
            clauses upper (height + 1) d (FixedLowerRawCollision.branchPositive parameters)
            A exterior (localTables parameters path outside clauses upper q table)
            (cutoff parameters.plan hδ) designated q choices raw direction))

end
end PerfectCompleteness.FixedSourceGlobalCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedWholeChoices
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedWholeChoices

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))
  (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))

abbrev path :=
  (StoppedProjectedExperiment.upperPath hupper o).append
    (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)

abbrev nativeCutSlots :=
  cutSlots (path hupper hij o lowerPref) (StoppedProjectedExperiment.nativeSlots clauses o)

abbrev projected :=
  SourceProjectedChoices.projected (nativeCutSlots clauses hupper hij o lowerPref)

abbrev projection :=
  SourceProjectedChoices.projection (nativeCutSlots clauses hupper hij o lowerPref)

end
end PerfectCompleteness.SourceProjectedWholeChoices

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedOldRecord
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
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

local instance fixedBackgroundFintype (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := rows) slots upper

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance backgroundFintype : Fintype (HierarchicalMatrixTable.Background (rows := rows)
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  StoppedProjectedBuckets.backgroundFintype clauses rows hupper o

local instance rowSpaceFintype_r92c44a_9 : Fintype (NodeEmbedding.RowSpace
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  StoppedProjectedBuckets.rowSpaceFintype clauses hupper o
def baseProbability
    (event : OldRecord clauses rows hupper o → Bool)
    (base : StoppedProjectedBuckets.Base (branch := branch) (i := i) (j := j) (t := t)) : ℝ :=
  (WholeArraySampler.law rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedBuckets.key (n := n) rows hrows base))
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)).probability
      (fun arrays => event (arrayRecord clauses rows hupper o
        (ChildBlockProjection.arraysPullback rows
          (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
          arrays)))

variable (hbranch : ∀ k < j + 1, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)

abbrev pairLaw :=
  HierarchicalUsefulCollision.pairLaw
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
    (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
    (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
    (StoppedProjectedBuckets.rows_positive rows hupper hrows o)

end
end PerfectCompleteness.StoppedProjectedOldRecord

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedCoarseLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedCoarse

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
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

local notation "O" => StoppedProjectedExperiment.Outer
  (branch := branch) (n := n) (j := j) (t := t) (m := m)

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

local instance fixedBackgroundFintype_r92c44a_1
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := rows) slots upper
local instance backgroundFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype_r92c44a_10 (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) :=
  HierarchicalPairCoarse.rowSpaceFintype (S o)
local instance coarseFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

local instance inputFintype_r92c44a_2 (o : O) (background : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) background) :=
  HierarchicalAdviceExperiment.inputFintype (S o) background
local instance projectedSampleFintype (o : O) :
    Fintype (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)) := by
  letI : (k : StoppedProjectedExperiment.Inner
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) →
      Fintype (WholeArraySampler.Tape rows repeats
        (WholeArrayInteriorOwnInputLaw.fullPath (StoppedProjectedExperiment.upper hupper o)
          (StoppedProjectedExperiment.lower rows hupper hij o k)
          (StoppedProjectedExperiment.cut rows hupper hij o k))
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k)) :=
    fun k => WholeArraySampler.tapeFintype rows repeats
      (WholeArrayInteriorOwnInputLaw.fullPath (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o k)
        (StoppedProjectedExperiment.cut rows hupper hij o k))
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o k)
  exact Sigma.instFintype

local instance adviceFintype (o : O) (r : Nat) :
    Fintype (HierarchicalAdviceExperiment.Advice (S o) r) := linearMapFintype

local instance originalFiberFintype (o : O) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) ×
      HierarchicalAdviceExperiment.Advice (S o) r) := by
  infer_instance

def pairLaw (outer : FiniteDistribution O) :=
  HierarchicalBucketFamily.actualPairLaw S outer
    (fun o => StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
    (fun o => StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
    (fun o => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
    (fun o => StoppedProjectedBuckets.rows_positive rows hupper hrows o)

end
end PerfectCompleteness.StoppedProjectedCoarse

end

section

namespace PerfectCompleteness.StoppedProjectedPairMean

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance rowSpaceFintype_r92c44a_11 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
local instance nativeBackgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _

local instance nativeRowSpaceFintype_r92c44a_1 :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
def fixedPair (base : StoppedProjectedBucketIndex.Base
    (branch := branch) (i := i) (j := j) (t := t)) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)) :=
  ((StoppedUsefulPairLaw.directionLaw rows j (hrows j)).product
    ((WholeArraySampler.tapeLaw rows repeats
      ((StoppedProjectedExperiment.upperPath hupper o).append
        (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base))
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)).product
        (RecursiveSampler.law F2 repeats
          (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base)
          (LeafDomain (cutSlots (StoppedProjectedExperiment.upperPath hupper o)
            (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)))))).pushforward
    (UpperScalarCutProjection.stoppedProjectedPair rows repeats
      (StoppedProjectedExperiment.upperPath hupper o)
      (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base) (Nat.succ_lt_succ hij)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
      (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base))

end
end PerfectCompleteness.StoppedProjectedPairMean

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedUsefulEvent
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
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

abbrev continuation (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  StoppedPathHead.tail hij (StoppedProjectedExperiment.lowerPath rows hij k)

theorem stepPath_eq (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    StoppedProjectedExperiment.stoppedPath rows hupper hij o k =
      (StoppedProjectedExperiment.upperPath hupper o).append
        (.step (chosen rows hij k) (continuation rows hij k)) :=
  congrArg (fun p => (StoppedProjectedExperiment.upperPath hupper o).append p)
    (StoppedPathHead.lowerPath_step_eq rows hij k)

def stepTape (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  StoppedOwnInputGeometry.pathTapeEquiv rows repeats
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (congrArg (fun p : Path branch n (i + 1) =>
      (⟨i + 1, p⟩ : Σ height, Path branch n height))
      (stepPath_eq rows hupper hij o sample.1)) sample.2

def readout (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  StoppedUsefulPairLaw.readout rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen rows hij sample.1) (continuation rows hij sample.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1)
    (stepTape clauses rows repeats hupper hij designated o sample)

def background (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  StoppedUsefulPairLaw.background rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (chosen rows hij sample.1) (continuation rows hij sample.1)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o sample.1)
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o sample.1)
    (readout clauses rows repeats hupper hij designated o sample).1

def buckets (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o) :=
  CutNodeRows.bucketTapeEquiv rows (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (readout clauses rows repeats hupper hij designated o sample).2

def upperDirection (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (direction : PrefixTests.LevelDirection rows (upperLevel hupper)) :=
  PrefixTests.nodeDirection rows (upperLevel hupper)
    ⟨StoppedProjectedExperiment.upper hupper o, StoppedProjectedExperiment.upper_height hupper o⟩
    direction

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment := StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
  hbranch hrows flag σ

def upperEvent (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (x : HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o)) : Bool :=
  PrefixTests.observeAtLevelNode clauses σ o.1
    ((experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).arrays x)
    (upperLevel hupper)
    ⟨StoppedProjectedExperiment.upper hupper o, StoppedProjectedExperiment.upper_height hupper o⟩
    (x.1.2.2 (upperLevel hupper))

end
end PerfectCompleteness.StoppedProjectedUsefulEvent

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedUsefulAverage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulAverage

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
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (κ : ℝ)
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

def bucketEvent
    (base : StoppedProjectedBucketIndex.Base (branch := branch) (i := i) (j := j) (t := t))
    (direction : PrefixTests.LevelDirection rows (StoppedProjectedUsefulEvent.upperLevel hupper))
    (tape : StoppedProjectedBucketIndex.Tape clauses rows repeats hupper hij designated hrows o base) : Bool :=
  let sample : StoppedProjectedExperiment.TapeSample clauses rows repeats hupper hij designated o :=
    ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩
  HierarchicalUsefulCollision.usefulAccepted
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
    (i + 1) (S o).original (S o).arrays (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
    (StoppedProjectedUsefulEvent.background clauses rows repeats hupper hij designated o sample)
    (StoppedProjectedUsefulEvent.upperDirection rows hupper o direction)
    (StoppedProjectedUsefulEvent.buckets clauses rows repeats hupper hij designated o sample)

def mean : ℝ :=
  (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).expectation (fun base =>
    (CanonicalDirections.levelLaw rows hrows (StoppedProjectedUsefulEvent.upperLevel hupper)).expectation
      (fun direction =>
        (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base).probability
          (bucketEvent clauses rows repeats hupper hij designated hbranch hrows flag σ κ o base direction)))

end
end PerfectCompleteness.StoppedProjectedUsefulAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceProducerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceProducer

open Turing UniqueGamesTheorem.Foundations Complexity

noncomputable section

def rawComputation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) SourceOccurrenceEncoding.bits
      PCPSourceMachine.rawSource := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) SourceOccurrenceEncoding.bits
    (fun input => id (PCPSourceMachine.rawSource input))
  exact MachineSequential.composeBits (f := PCPSourceMachine.rawSource) (g := id)
    PCPSourceMachine.rawComputation
    SourceOccurrenceMachine.computableInPolyTime

theorem raw_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet rawComputation.tm :=
  MachineFiniteAlphabet.composeBits PCPSourceMachine.rawComputation
    SourceOccurrenceMachine.computableInPolyTime PCPSourceMachine.raw_finiteAlphabet
    SourceOccurrenceMachine.computation_finiteAlphabet

end
end PerfectCompleteness.SourceOccurrenceProducer


namespace PerfectCompleteness.NormalizedSourceInput


open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

def rawComputation : TM2ComputableInPolyTime (id : List Bool → List Bool) bits raw where
  toTM2ComputableAux := SourceOccurrenceProducer.rawComputation.toTM2ComputableAux
  time := SourceOccurrenceProducer.rawComputation.time
  outputsFun input := SourceOccurrenceProducer.rawComputation.outputsFun input

theorem raw_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet rawComputation.tm :=
  SourceOccurrenceProducer.raw_finiteAlphabet

end
end PerfectCompleteness.NormalizedSourceInput

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizedTargetTapeBound
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.counted_count _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_current _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_extra _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_remaining _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.ready_table _root_.OAI.PerfectCompleteness.NormalizedTargetInitialization.seeded_count _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero
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
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "clauses" => NormalizedSourceInput.clauses input
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "T" => List.length (NormalizedSourceInput.bits input)
local notation "E" => List.length order

theorem count_le : E ≤ D * (T + 1) ^ width := by
  rw [CompletedVisitOrder.completedOrder_length]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left
    ((SourceKeyBounds.clauseCount_le_bits input).trans (Nat.le_succ _)) _

theorem leftStream_length_le :
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens
      (finalData (t := t) rows repeats hn hbranch hrows δ input).leftKeys)).length ≤
        CanonicalDictionaryNames.streamBound width T E := by
  change (BinaryNameSearch.stream (CanonicalVertexNames.tokens
    ((order).map (fun e => CanonicalGame.leftKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)))).length ≤ _
  have h := CanonicalVertexNames.stream_length_le
    ((order).map (fun e => CanonicalGame.leftKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)) T
    (by
      intro key present
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.left_retained_length input rows repeats e.1)
    (by
      intro key present entry member
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.left_entryID_le input rows repeats e.1 entry member)
  simpa only [List.length_map, CanonicalDictionaryNames.streamBound] using h

theorem rightStream_length_le :
    (BinaryNameSearch.stream (CanonicalVertexNames.tokens
      (finalData (t := t) rows repeats hn hbranch hrows δ input).rightKeys)).length ≤
        CanonicalDictionaryNames.streamBound width T E := by
  change (BinaryNameSearch.stream (CanonicalVertexNames.tokens
    ((order).map (fun e => CanonicalGame.rightKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)))).length ≤ _
  have h := CanonicalVertexNames.stream_length_le
    ((order).map (fun e => CanonicalGame.rightKey
      (FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats) e.1)) T
    (by
      intro key present
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.right_retained_length input rows repeats e.1)
    (by
      intro key present entry member
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
      exact SourceKeyBounds.right_entryID_le input rows repeats e.1 entry member)
  simpa only [List.length_map, CanonicalDictionaryNames.streamBound] using h

theorem finalTapes_length_le :
    ∀ k, (finalTapes (t := t) rows repeats hn hbranch hrows δ input k).length ≤
      TargetTapeEnvelope.bound width q T E := by
  have leftBound := leftStream_length_le (t := t) rows repeats hn hbranch hrows δ input
  have rightBound := rightStream_length_le (t := t) rows repeats hn hbranch hrows δ input
  have outputBound := reversedOutput_length_le (t := t) rows repeats hn hbranch hrows δ input
  have countBound := SourceKeyBounds.clauseCount_le_bits input
  have sourceLe : T ≤ TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  have currentLe : 1 ≤ TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  have remainingLe : NormalizedSourceInput.clauseCount input - 1 + 1 ≤
      TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  have leftLe := leftBound.trans (show CanonicalDictionaryNames.streamBound width T E ≤
      TargetTapeEnvelope.bound width q T E by unfold TargetTapeEnvelope.bound; omega)
  have rightLe := rightBound.trans (show CanonicalDictionaryNames.streamBound width T E ≤
      TargetTapeEnvelope.bound width q T E by unfold TargetTapeEnvelope.bound; omega)
  have outputLe := outputBound.trans (show TargetTapeEnvelope.outputBound q E ≤
      TargetTapeEnvelope.bound width q T E by unfold TargetTapeEnvelope.bound; omega)
  have encodedCountLe : E + 1 ≤ TargetTapeEnvelope.bound width q T E := by
    unfold TargetTapeEnvelope.bound
    omega
  intro k
  cases k with
  | source source =>
      cases source with
      | table => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes] using sourceLe
      | digit i => simp [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
      | work j => simp [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
      | variableName i j => simp [finalTapes, ExactTargetOdometer.nativeTapes,
          SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | current i => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes, encodeWord_length] using currentLe
  | remaining i => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes, encodeWord_length] using remainingLe
  | encodedVariable i j => simp [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | adapterScratch => simp [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | edgeCount => simpa [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, finalData, SignedTupleSemantics.dataOfPrefix,
      encodeWord_length] using encodedCountLe
  | extra x => simp [finalTapes, ExactTargetOdometer.nativeTapes,
      SignedTupleBodyMachine.tapes, ExactTargetOdometer.baseTapes]
  | edgeWork j =>
      by_cases one : j = 1
      · subst j
        simpa [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
          using leftLe
      · by_cases eight : j = 8
        · subst j
          simpa [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
            using rightLe
        · by_cases seven : j = 7
          · subst j
            simpa [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes]
              using outputLe
          · simp [finalTapes, ExactTargetOdometer.nativeTapes, SignedTupleBodyMachine.tapes,
              ExactTargetOdometer.baseTapes, one, eight, seven]

theorem finalTapes_length_le_polynomial :
    ∀ k, (finalTapes (t := t) rows repeats hn hbranch hrows δ input k).length ≤
      TargetTapeEnvelope.coeff width q D * (T + 1) ^ (2 * width + 2) := by
  intro k
  exact (finalTapes_length_le (t := t) rows repeats hn hbranch hrows δ input k).trans
    (TargetTapeEnvelope.bound_le width q D T E (count_le (t := t) rows repeats hn hbranch hrows δ input))

end
end PerfectCompleteness.NormalizedTargetTapeBound

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

local notation "width" => TreeCanonical.locationCount branch n t

variable (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "ambient" => initialAmbient (branch := branch) (n := n) (t := t) rows repeats δ

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

local notation "runProgram" => program (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

local notation "tm" => machine (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

local notation "cfg" => configuration (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "finalData" => NormalizedTargetTapeBound.finalData
  (t := t) rows repeats hn hbranch hrows δ
local notation "finalTapes" => NormalizedTargetTapeBound.finalTapes
  (t := t) rows repeats hn hbranch hrows δ
local notation "output" => NormalizedTarget.outputBits (t := t) rows repeats hn hbranch hrows δ

def enumerateInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftDriver nativeEntry)) (NormalizedTargetInitialization.readyTapes input))
      (some (cfg (some (liftDriver .exit)) (finalTapes input)))
      (ExactTargetOdometer.timeBound (t := t) rows repeats hn hbranch hrows δ
        (NormalizedSourceInput.bits input).length) := by
  have run := MachineSubroutine.execution liftDriver (some (liftFinal .reverse))
    nativeProgram runProgram (fun _ => rfl)
    (ExactTargetOdometer.targetInTimePolynomial rows repeats hn hbranch hrows δ input []
      (fun _ : Fin 4 => []))
  rw [NormalizedTargetInitialization.ready_eq_native (branch := branch) (n := n) (t := t) input]
  delta NormalizedTargetInitialization.zeroDigits
  simpa only [configuration, initialControl,
    MachineSubroutine.configuration, MachineSubroutine.label,
    ExactTargetOdometer.configuration, NormalizedTargetInitialization.zeroDigits,
    NormalizedTargetTapeBound.finalTapes, NormalizedTargetTapeBound.finalData,
    SignedTupleSemantics.dataOfPrefix, ExactTargetOnlineEncoding.leftKeys,
    ExactTargetOnlineEncoding.rightKeys, List.map_nil, List.flatMap_nil,
    List.reverse_nil, List.nil_append, List.length_nil] using! run

def finalizeInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftFinal .reverse)) (finalTapes input))
      (some (cfg none (MachineDrainMany.haltTapes (.extra 3) (output input))))
      (finalizeBudget (t := t) rows repeats hn hbranch hrows δ (NormalizedSourceInput.bits input).length) := by
  have run := TargetFinalizeBound.finalizeInTime q (tapeEnumeration branch n t)
    (finalizerTape branch n t) (finalizerTape_injective branch n t) ambient liftFinal
    runProgram (fun _ => rfl) (finalTapes input) ambient none (finalData input).count
    (finalData input).reversedOutput.reverse
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_output, List.reverse_reverse])
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_count])
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_extra])
    (by simp only [finalizerTape, NormalizedTargetTapeBound.finalTapes,
      ExactTargetOdometer.nativeTapes_extra])
    (TargetTapeEnvelope.coeff width q D *
      ((NormalizedSourceInput.bits input).length + 1) ^ (2 * width + 2))
    (NormalizedTargetTapeBound.finalTapes_length_le_polynomial
      rows repeats hn hbranch hrows δ input)
  rw [header_body_eq_outputBits rows repeats hn hbranch hrows δ input] at run
  exact run

def totalInTime (input : NormalizedSourceInput.Input) :
    StateTransition.EvalsToInTime (TM2.step runProgram)
      (cfg (some (liftInit .seed)) (NormalizedTargetInitialization.inputTapes input))
      (some (cfg none (MachineDrainMany.haltTapes (.extra 3) (output input))))
      (totalBudget (t := t) rows repeats hn hbranch hrows δ (NormalizedSourceInput.bits input).length) := by
  have first := StateTransition.EvalsToInTime.trans (TM2.step runProgram) _ _ _ _ _
    (initializeInTime rows repeats hn hbranch hrows δ input)
    (enumerateInTime rows repeats hn hbranch hrows δ input)
  have second := StateTransition.EvalsToInTime.trans (TM2.step runProgram) _ _ _ _ _
    first (returnInTime rows repeats hn hbranch hrows δ (finalTapes input))
  have full := StateTransition.EvalsToInTime.trans (TM2.step runProgram) _ _ _ _ _
    second (finalizeInTime rows repeats hn hbranch hrows δ input)
  simpa only [totalBudget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def outputsInTime (input : NormalizedSourceInput.Input) :
    TM2OutputsInTime tm (NormalizedSourceInput.bits input) (some (output input))
      (totalBudget (t := t) rows repeats hn hbranch hrows δ
        (NormalizedSourceInput.bits input).length) := by
  change StateTransition.EvalsToInTime (TM2.step runProgram)
    (initList tm (NormalizedSourceInput.bits input))
    (some (haltList tm (output input))) _
  rw [initList_eq, haltList_eq]
  exact totalInTime rows repeats hn hbranch hrows δ input

def targetComputation :
    TM2ComputableInPolyTime NormalizedSourceInput.bits Encoding.gameBits
      (NormalizedTarget.construct (t := t) rows repeats hn hbranch hrows δ) where
  «tm» := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time (t := t) rows repeats hn hbranch hrows δ
  outputsFun input := by
    change TM2OutputsInTime tm ((NormalizedSourceInput.bits input).map id)
      (some ((output input).map id))
      ((time (t := t) rows repeats hn hbranch hrows δ).eval
        (NormalizedSourceInput.bits input).length)
    have hi := @List.map_id ((tm).Γ (tm).k₀) (NormalizedSourceInput.bits input)
    have ho := @List.map_id ((tm).Γ (tm).k₁) (output input)
    simpa only [hi, ho, time_eval] using
      outputsInTime (t := t) rows repeats hn hbranch hrows δ input

end
end PerfectCompleteness.NormalizedTargetMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedTarget

open Turing UniqueGamesTheorem.Foundations.Complexity
open FixedParameters FixedRows FixedPreliminaryGame

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem alphabet_pos : 0 < alphabet p :=
  lt_of_lt_of_le (by decide : 0 < 2) (alphabet_ge_two p)

def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
      (construct p) := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) Encoding.gameBits
    (fun input => NormalizedTarget.construct (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ
      (NormalizedSourceInput.raw input))
  exact MachineSequential.composeBits
    NormalizedSourceInput.rawComputation
    (NormalizedTargetMachine.targetComputation (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ)

theorem finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet (computation p).tm :=
  MachineFiniteAlphabet.composeBits
    NormalizedSourceInput.rawComputation
    (NormalizedTargetMachine.targetComputation (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ)
    NormalizedSourceInput.raw_finiteAlphabet
    (NormalizedTargetMachine.finiteAlphabet (branch := branch p) (n := p.plan.depth)
      (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
      (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ)

theorem perfectlyComplete (input : List Bool) (accepted : BinaryLanguage.language input) :
    PerfectlyComplete (construct p input) :=
  NormalizedTarget.perfectlyComplete (branch := branch p) (n := p.plan.depth)
    (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ
    (NormalizedSourceInput.raw input)
    ((NormalizedSourceInput.raw_satisfiable_iff input).mpr accepted)

theorem value_eq_one (input : List Bool) (accepted : BinaryLanguage.language input) :
    (construct p input).value = 1 :=
  ((construct p input).perfectlyComplete_iff_value_eq_one (alphabet_pos p)).mp
    (perfectlyComplete p input accepted)

end
end PerfectCompleteness.FixedTarget

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedTargetValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedTargetValue


open UniqueGamesTheorem.Foundations Target
open FixedParameters FixedRows FixedPreliminaryGame
open scoped Classical

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem value_le (input : List Bool) :
    (FixedTarget.construct p input).value ≤
      FixedPreliminaryGame.value p input + (δ : ℝ) / 3 :=
  packed_value_le (PCPSource.normalizedFormula (BinaryLanguage.totalRename input))
    (PCPSource.normalizedFormula_nonempty (BinaryLanguage.totalRename input))
    (PCPSource.normalizedFormula_distinct (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ hδ

end
end PerfectCompleteness.FixedTargetValue

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FixedBinaryGapReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedBinaryGapReduction

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

def ofPreliminarySoundness
    (soundness : ∀ input, ¬BinaryLanguage.language input →
      FixedPreliminaryGame.value p input ≤ InitialParameters.epsilon δ) :
    BinaryGapReduction δ where
  alphabet := FixedTarget.alphabet p
  alphabet_ge_two := FixedTarget.alphabet_ge_two p
  construct := FixedTarget.construct p
  computation := FixedTarget.computation p
  finiteAlphabet := FixedTarget.finiteAlphabet p
  completeness := FixedTarget.value_eq_one p
  soundness input unsat := by
    have htarget := FixedTargetValue.value_le p input
    have hpreliminary := soundness input unsat
    have hpositive : 0 < (δ : ℝ) := by exact_mod_cast hδ
    unfold InitialParameters.epsilon at hpreliminary
    linarith

end
end PerfectCompleteness.FixedBinaryGapReduction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FixedStoppedNativeTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeTape

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)
open FixedStoppedNativeProjection (physicalSample innerTag path childSample)

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)

local notation "R" => FixedRows.rows parameters.plan
local notation "T" => FixedRows.repeats parameters.plan
local notation "C" => clauses input
local notation "D" => designated parameters i
local notation "hu" => Nat.succ_le_of_lt j.isLt
local notation "P" => physicalSample parameters i j hij input sample

abbrev physicalRead :=
  StoppedProjectedExperiment.physicalRead C R T hu hij D P.1 P.2.1

abbrev experimentRead :=
  StoppedProjectedExperiment.physicalExperimentRead C R T hu hij D P.1 P.2.1

abbrev rawRead :=
  StoppedProjectedPhysicalAdvice.read C R T hu hij D parameters.plan.order P

end
end PerfectCompleteness.FixedStoppedNativeTape

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedSourcePhysicalHighLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourcePhysicalHigh

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (pDown : Path (branch parameters) (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper (height + 1) d))
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    ((Nodes.path upper).append pDown) outside placeholder)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
      upper (height + 1) bg → Prop)
  (density threshold : ℝ)

local instance rowSpaceFintype_r92c44a_12 (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r92c44a_1 (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper)
local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

def tagLaw : FiniteDistribution
    (SourceProjectedTag.Tag (branch := branch parameters) (n := height)
      (t := sourceLength parameters.plan hδ)) :=
  SourceProjectedTag.law (FixedSourceGlobalCollision.flag parameters)

def success (direction : BucketSampler.Direction (rows parameters.plan (height + 1)))
    (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height))
    (tag : SourceProjectedTag.Tag (branch := branch parameters) (n := height)
      (t := sourceLength parameters.plan hδ)) : ℝ :=
  SourceQuestionPhysicalHigh.success outside placeholder clauses designated q tag.1 tag.2 upper pDown
    hproper (height + 1) (FixedLowerRawCollision.branchPositive parameters) d hnode A cut σ (useful q)
    density threshold exterior direction (cutoff parameters.plan hδ)

def probability : ℝ :=
  (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
    (fun direction => (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
      (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
        (tagLaw parameters).expectation
          (success parameters outside placeholder clauses designated upper pDown hproper d hnode A cut
            exterior σ useful density threshold direction q)))

end
end PerfectCompleteness.FixedSourcePhysicalHigh

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedNativeHigh
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedNativeHigh

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  {upper : Nodes (branch parameters) parameters.plan.depth}
  {d : HierarchicalFrozenTables.LowerNodes upper (height + 1)}
  (S : CleanDecoderRate.Setup (branch parameters) (rows parameters.plan) (repeats parameters.plan)
    parameters.plan.depth height (sourceLength parameters.plan hδ) v m upper d)
  (hnode : WholeArrayInteriorExterior.upperNode (CleanDecoderRate.path S) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {Original : OriginalDecoderMark.SlotFamily (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ) → Type*}
  [∀ slots, Fintype (Original slots)]
  (F : OriginalDecoderMark.Family (branch parameters) (rows parameters.plan)
    parameters.plan.depth (sourceLength parameters.plan hδ) Original)
  (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (r : Nat) (density : ℝ)
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) r)
  (threshold : ℝ)

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

def questionUseful
    (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) :=
  OriginalDecoderMark.mark F upper (height + 1) κ
    (SourceQuestionLowerForms.slots (CleanDecoderRate.path S) S.outside S.clauses q)

def probability : ℝ :=
  (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
    (fun direction =>
      (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
        r density A (LinearMap.ker A) (CleanPhysicalHighAverage.nativeDirection S hnode direction)
        threshold (parameters.cubeSize height) (FixedDecoderCleanRate.cubePositive parameters height)).probability
          (fun z => DecoderRankSplit.highAgrees S (FixedLowerRawCollision.branchPositive parameters)
            (cutoff parameters.plan hδ) z.1 z.2))

end
end PerfectCompleteness.FixedNativeHigh

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedDirections
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedStoppedNativeProjection.flags_eq _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedDirections

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j)

abbrev lowerNode (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :=
  HierarchicalLeftDecoder.LowerNode (FixedStoppedDecoderContext.upper parameters i j pref)
    (i.val + 1) (FixedStoppedDecoderContext.lower parameters i j hij pref)

@[simp] theorem lowerNode_height (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    Nodes.height (lowerNode parameters i j hij pref) = i.val + 1 :=
  CleanDecoderContext.lowerHeight (FixedStoppedDecoderContext.upper parameters i j pref)
    (FixedStoppedDecoderContext.lower parameters i j hij pref)

abbrev LowerDirection (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :=
  BucketSampler.Direction
    (FixedRows.rows parameters.plan (Nodes.height (lowerNode parameters i j hij pref)))

instance lowerDirectionNonempty (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    Nonempty (LowerDirection parameters i j hij pref) :=
  PreliminarySampler.directionNonempty _ (by
    rw [lowerNode_height]
    exact parameters.plan.rows_pos (parameters.plan.depth - (i.val + 1)))

def lowerDirectionEquiv (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    PrefixTests.LevelDirection (FixedRows.rows parameters.plan) i ≃
      LowerDirection parameters i j hij pref :=
  (Equiv.cast (congrArg (fun height =>
    BucketSampler.Direction (FixedRows.rows parameters.plan height))
      (lowerNode_height parameters i j hij pref))).symm

def lowerDirection (pref : FixedStoppedDecoderContext.Prefixes parameters i j)
    (directions : FixedStoppedDecoderContext.Directions parameters) :
    LowerDirection parameters i j hij pref :=
  PrefixTests.nodeDirection (FixedRows.rows parameters.plan) i
    ⟨lowerNode parameters i j hij pref, lowerNode_height parameters i j hij pref⟩ (directions i)

def lowerLaw (pref : FixedStoppedDecoderContext.Prefixes parameters i j) :
    FiniteDistribution (LowerDirection parameters i j hij pref) :=
  FiniteDistribution.uniform _

end
end PerfectCompleteness.FixedStoppedDirections

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedHighBound
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedHighBound

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev Prefixes := FixedStoppedDecoderContext.Prefixes parameters i j

def setup (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :=
  FixedDecoderCleanRate.setup parameters
    (StoppedCleanGeometry.geometry parameters input
      (FixedStoppedDecoderContext.upperPath parameters i j pref)
      (FixedStoppedDecoderContext.lowerPath parameters i j hij pref) hij external exterior) input

theorem setup_node (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :
    WholeArrayInteriorExterior.upperNode
        (CleanDecoderRate.path (setup parameters i j hij input pref external exterior)) =
      FixedStoppedDirections.lowerNode parameters i j hij pref := by
  change WholeArrayInteriorExterior.upperNode
      (CleanRecordDecoderInput.path _ _
        (StoppedCleanGeometry.geometry parameters input
          (FixedStoppedDecoderContext.upperPath parameters i j pref)
          (FixedStoppedDecoderContext.lowerPath parameters i j hij pref) hij external exterior).cut) = _
  rw [StoppedCleanGeometry.geometry_path]
  exact (StoppedCleanGeometry.lowerNode_descendant
    (FixedStoppedDecoderContext.upperPath parameters i j pref)
    (FixedStoppedDecoderContext.lowerPath parameters i j hij pref) hij).symm

def highProbability (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)
    (a : Block (FixedRows.rows parameters.plan)
      (FixedStoppedDirections.lowerNode parameters i j hij pref)) : ℝ :=
  (CleanDecoderPairLaw.pairLaw (setup parameters i j hij input pref external exterior)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (CleanPhysicalDecoderLaw.useful (setup parameters i j hij input pref external exterior)
      (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy pref)
      (InitialParameters.useful δ)) parameters.plan.order parameters.plan.density A
    (LinearMap.ker A) a (FixedStoppedDecoderLaw.threshold parameters j)
    (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)).probability
      (fun z => DecoderRankSplit.highAgrees
        (setup parameters i j hij input pref external exterior)
        (FixedDecoderCleanRate.branchPositive parameters)
        (FixedRows.cutoff parameters.plan hδ) z.1 z.2)

def directionMean (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) : ℝ :=
  (FixedStoppedDirections.lowerLaw parameters i j hij pref).expectation
    (fun a => highProbability parameters i j hij input strategy pref external A exterior a.val)

end
end PerfectCompleteness.FixedStoppedHighBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedInverseBound
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedInverseBound

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)

abbrev Outer := StoppedProjectedExperiment.Outer
  (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
  (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
  (m := (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)

abbrev designated := FixedStoppedPhysicalLaw.designated parameters i

abbrev experiment (strategy : FixedPreliminaryGame.Strategy parameters input)
    (o : Outer parameters j input) :=
  StoppedProjectedExperiment.experiment (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy) o

abbrev outerLaw : FiniteDistribution (Outer parameters j input) :=
  StoppedProjectedExperiment.outerLaw (Nat.succ_le_of_lt j.isLt)
    (fun k _ => FixedParameters.branch_pos parameters k)

abbrev externalLaw (o : Outer parameters j input) :=
  StoppedProjectedBuckets.externalLaw (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan) o
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)

abbrev background (o : Outer parameters j input) :=
  StoppedProjectedBuckets.background (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan) o

abbrev scalarLaw (o : Outer parameters j input) :=
  StoppedProjectedBuckets.scalarLaw (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan) o

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

local notation "S" => experiment parameters i j hij input strategy

local instance nativeBackgroundFintype (o : Outer parameters j input) :
    Fintype (HierarchicalMatrixTable.Background (rows := FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)) :=
  HierarchicalUsefulCollision.backgroundFintype (rows := FixedRows.rows parameters.plan)
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)

local instance nativeRowSpaceFintype_r92c44a_2 (o : Outer parameters j input) :
    Fintype (NodeEmbedding.RowSpace
      (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)) :=
  HierarchicalUsefulCollision.rowSpaceFintype
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
abbrev PairFiber (o : Outer parameters j input) :=
  HierarchicalAgreementMean.PairRecord (rows := FixedRows.rows parameters.plan)
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)

abbrev PairSample := (o : Outer parameters j input) × PairFiber parameters j input o

local instance pairFiberFintype (o : Outer parameters j input) :
    Fintype (PairFiber parameters j input o) := by
  unfold PairFiber HierarchicalAgreementMean.PairRecord
  infer_instance

local instance pairSampleFintype : Fintype (PairSample parameters j input) :=
  Sigma.instFintype

local instance backgroundFintype_r92c44a_2 (o : Outer parameters j input) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)
local instance coarseFintype (o : Outer parameters j input) :
    Fintype (HierarchicalAdviceExperiment.Coarse (S o)) :=
  HierarchicalAdviceFamily.coarseFintype S o

local instance inputFintype_r92c44a_3 (o : Outer parameters j input)
    (bg : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) bg) :=
  HierarchicalAdviceExperiment.inputFintype (S o) bg
local instance projectedSampleFintype (o : Outer parameters j input) :
    Fintype (HierarchicalProjectedExperiment.Sample
      (rows := FixedRows.rows parameters.plan) (repeats := FixedRows.repeats parameters.plan)
      (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
      (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)
      (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)) := by
  letI : (k : StoppedProjectedExperiment.Inner
      (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
      (i := i.val) (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
      (FixedRows.rows parameters.plan)) →
      Fintype (WholeArraySampler.Tape (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan)
        (WholeArrayInteriorOwnInputLaw.fullPath
          (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
          (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
            (Nat.succ_le_of_lt j.isLt) hij o k)
          (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
            (Nat.succ_le_of_lt j.isLt) hij o k))
        (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o k)) :=
    fun k => WholeArraySampler.tapeFintype _ _ _ _
  exact Sigma.instFintype

local instance adviceFintype (o : Outer parameters j input) (r : Nat) :
    Fintype (HierarchicalAdviceExperiment.Advice (S o) r) := linearMapFintype

local instance originalFiberFintype_r92c44a_1 (o : Outer parameters j input) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.Sample
      (rows := FixedRows.rows parameters.plan) (repeats := FixedRows.repeats parameters.plan)
      (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
      (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)
      (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o) ×
      HierarchicalAdviceExperiment.Advice (S o) r) := by
  infer_instance
abbrev backgrounds :=
  HierarchicalBucketFamily.actualBackgrounds (experiment parameters i j hij input strategy)
    (externalLaw parameters i j hij input) (background parameters i j hij input)

abbrev usefulMass : ℝ :=
  HierarchicalBucketFamily.usefulMass (experiment parameters i j hij input strategy)
    (InitialParameters.useful δ) (outerLaw parameters j input)
    (externalLaw parameters i j hij input) (background parameters i j hij input)
    (scalarLaw parameters i j hij input)
    (HierarchicalFixedAdviceFamily.rows_positive parameters
      (experiment parameters i j hij input strategy))

abbrev actualPairs : FiniteDistribution (PairSample parameters j input) :=
  HierarchicalBucketFamily.actualPairLaw (experiment parameters i j hij input strategy)
    (outerLaw parameters j input) (externalLaw parameters i j hij input)
    (background parameters i j hij input) (scalarLaw parameters i j hij input)
    (HierarchicalFixedAdviceFamily.rows_positive parameters
      (experiment parameters i j hij input strategy))

abbrev referencePairs : FiniteDistribution (PairSample parameters j input) :=
  HierarchicalBucketFamily.referencePairLaw (experiment parameters i j hij input strategy)
    (outerLaw parameters j input) (backgrounds parameters i j hij input strategy)
    (HierarchicalFixedAdviceFamily.rows_positive parameters
      (experiment parameters i j hij input strategy))

abbrev pairedVariation : ℝ :=
  (actualPairs parameters i j hij input strategy).totalVariation
    (referencePairs parameters i j hij input strategy)

abbrev coarseVariation : ℝ :=
  ((HierarchicalAdviceFamily.originalLaw (experiment parameters i j hij input strategy)
    (outerLaw parameters j input) parameters.plan.order).pushforward
      (HierarchicalAdviceFamily.observe (experiment parameters i j hij input strategy)
        parameters.plan.order)).totalVariation
    ((HierarchicalAdviceFamily.referenceLaw (experiment parameters i j hij input strategy)
      (outerLaw parameters j input) (backgrounds parameters i j hij input strategy)
      parameters.plan.order).pushforward
        (HierarchicalAdviceFamily.referenceObserve
          (experiment parameters i j hij input strategy) parameters.plan.order))

abbrev expectedMeeting : ℝ :=
  StoppedProjectedMeetingLaw.expectedMeeting parameters.plan (clauses input)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)

end
end PerfectCompleteness.FixedStoppedInverseBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedMeetingEquality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedMeetingEquality

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.scalarFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

abbrev OriginalRaw := StoppedProjectedMeetingLaw.RawSample
  (t := FixedRows.sourceLength parameters.plan hδ) parameters.plan
  (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
  (FixedStoppedPhysicalLaw.designated parameters i)

local instance physicalLeftFintype_r92c44a_1 {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def familyMeetingOnRaw (sample : OriginalRaw parameters i j hij input) : ℝ :=
  ProjectedMeetingTransport.familyMeetingProbability parameters.plan
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy
      (sample.1.2, sample.2.2.1.1))
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (StoppedProjectedExperiment.nativeSlots (FixedStoppedPhysicalLaw.clauses input) sample.1)
    (StoppedProjectedExperiment.projectedSlots (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.projection (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) sample.1)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1) (i.val + 1)
    sample.2.1
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2.2.2.2

def nativeMeetingProbability
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) : ℝ :=
  (CleanDecoderPairLaw.pairKernel
    (FixedStoppedDecoderLaw.setups parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedDecoderLaw.useful parameters i j hij input strategy sample.1)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)
    (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
    (FixedStoppedDecoderContext.direction parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2).probability
      (DecoderRankSplit.meeting
        (FixedStoppedDecoderLaw.setups parameters i j hij input sample.1) sample.2)

def physicalMeetingProbability
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) : ℝ :=
  StoppedProjectedMeetingLaw.meetingProbability parameters.plan
    (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedNativeLaw.read parameters i j hij input sample)

def cleanMeetingProbability
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) : ℝ :=
  (CleanPhysicalProjectedMeeting.visiblePairKernel
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy sample.1.1)
    (InitialParameters.useful δ)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)
    (FixedStoppedDecoderContext.direction parameters i j hij input sample.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2).probability
      (fun answer => decide ((ProjectedNodeEmbedding.intoOriginal
        (CleanPhysicalDecoderLaw.physicalProjection
          (FixedStoppedNativeLaw.setup parameters i j hij input sample.1) sample.2)
        (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)).dualMap
          answer.1 = answer.2))

abbrev expectedMeeting : ℝ :=
  StoppedProjectedMeetingLaw.expectedMeeting parameters.plan
    (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)

end
end PerfectCompleteness.FixedStoppedMeetingEquality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedUsefulMass
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUsefulMass

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

abbrev clauses := PCPSource.clauseFamily (BinaryLanguage.totalRename input)

abbrev Outer := StoppedProjectedExperiment.Outer
  (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
  (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
  (m := (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)

abbrev Base := StoppedProjectedExperiment.PhysicalBase
  (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
  (i := i.val) (j := j.val) (t := FixedRows.sourceLength parameters.plan hδ)
  (FixedRows.rows parameters.plan)

def flags : Fin (FixedParameters.branch parameters i.val) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli (FixedParameters.projectionProbability parameters i.val : ℝ)
    (FixedPhysicalStoppedComparison.beta_nonneg parameters)
    (FixedPhysicalStoppedComparison.beta_le_one parameters)

def outerLaw : FiniteDistribution (Outer parameters j input) :=
  StoppedProjectedExperiment.outerLaw (Nat.succ_le_of_lt j.isLt)
    (fun k _ => FixedParameters.branch_pos parameters k)

def baseLaw : FiniteDistribution (Base parameters i j) :=
  StoppedProjectedExperiment.physicalBaseLaw (FixedRows.rows parameters.plan) hij
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1))

def record (o : Outer parameters j input)
    (pref : GeometricCutSplit.Prefix (FixedParameters.branch parameters) (j.val + 1) (i.val + 1))
    (directions : CanonicalDirections.Tuple (FixedRows.rows parameters.plan) parameters.plan.depth)
    (arrays : Arrays (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (FixedRows.rows parameters.plan)) :
    StoppedSharedSampler.Record (clauses input) (FixedParameters.branch parameters)
      parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ) i.val
      (FixedRows.rows parameters.plan) :=
  ⟨(o.1, (GeometricPrefixSplit.joinEquiv (Nat.succ_le_succ hij.le)
      (Nat.succ_le_of_lt j.isLt) (o.2, pref), directions)), arrays⟩

variable (designated : Fin (FixedParameters.branch parameters i.val) →
  Slots (FixedParameters.branch parameters) i.val)

abbrev PhysicalSample := StoppedProjectedPhysicalLaw.Sample
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij designated

abbrev OriginalSample := StoppedProjectedGlobalLaw.ExperimentSample
  (t := FixedRows.sourceLength parameters.plan hδ)
  (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
  (Nat.succ_le_of_lt j.isLt) hij designated

def physicalLaw : FiniteDistribution (PhysicalSample parameters i j hij input designated) :=
  StoppedProjectedPhysicalLaw.law
    (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)

def physicalRecord (sample : PhysicalSample parameters i j hij input designated) :=
  record parameters i j hij input sample.1 sample.2.1.1 sample.2.1.2.2
    (cast (congrArg (fun slots => Arrays slots (FixedRows.rows parameters.plan))
      (StoppedProjectedArrays.nativeSlots_eq (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij designated sample.1 sample.2.1))
      (StoppedProjectedArrays.physicalArrays (clauses input) (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
        sample.1 sample.2))

def referenceMass (event : StoppedSharedSampler.Record (clauses input)
    (FixedParameters.branch parameters) parameters.plan.depth
    (FixedRows.sourceLength parameters.plan hδ) i.val (FixedRows.rows parameters.plan) → Bool) : ℝ :=
  (outerLaw parameters j input).expectation (fun o =>
    (baseLaw parameters i j hij).expectation (fun base =>
      (WholeArraySampler.law (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (StoppedProjectedExperiment.stoppedPath (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij o
          (StoppedProjectedExperiment.baseTag (FixedRows.rows parameters.plan) base))
        (StoppedProjectedExperiment.nativeSlots (clauses input) o)).probability
          (fun arrays => event (record parameters i j hij input o base.1 base.2.2 arrays))))

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

abbrev canonicalStrategy := PreliminaryStrategy.extend (clauses input)
  (FixedParameters.branch parameters) parameters.plan.depth
  (FixedRows.sourceLength parameters.plan hδ) (FixedRows.rows parameters.plan)
  (FixedRows.repeats parameters.plan) strategy

abbrev experiment (o : Outer parameters j input) :=
  StoppedProjectedGlobalLaw.experiment (clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
    (canonicalStrategy parameters input strategy) o

abbrev OriginalFiber (o : Outer parameters j input) :=
  HierarchicalProjectedExperiment.Sample (rows := FixedRows.rows parameters.plan)
    (repeats := FixedRows.repeats parameters.plan)
    (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij designated o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij o)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij o)

def originalLaw : FiniteDistribution (OriginalSample parameters i j hij input designated) :=
  StoppedProjectedGlobalLaw.experimentLaw (clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
    (canonicalStrategy parameters input strategy)

def originalRecord (sample : OriginalSample parameters i j hij input designated) :=
  record parameters i j hij input sample.1 sample.2.1.1 sample.2.1.2.2
    ((experiment parameters i j hij input designated strategy sample.1).arrays sample.2)

def upperEvent (o : Outer parameters j input)
    (x : OriginalFiber parameters i j hij input designated o) : Bool :=
  PrefixTests.observeAtLevelNode (clauses input) (canonicalStrategy parameters input strategy)
    o.1 ((experiment parameters i j hij input designated strategy o).arrays x) j
    ⟨StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o,
      StoppedProjectedExperiment.upper_height (Nat.succ_le_of_lt j.isLt) o⟩
    (x.1.2.2 j)

end
end PerfectCompleteness.FixedStoppedUsefulMass

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedSourcePairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSourcePairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.StoppedSourcePairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FixedSourcePairVariation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourcePairVariation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype
attribute [local instance 2000] HierarchicalUsefulCollision.backgroundFintype
  HierarchicalUsefulCollision.rowSpaceFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  {n i j v m : Nat}

abbrev Outer := StoppedProjectedExperiment.Outer
  (branch := FixedParameters.branch parameters) (n := n) (j := j)
  (t := FixedRows.sourceLength parameters.plan hδ) (m := m)

def flags : Fin (FixedParameters.branch parameters i) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli (FixedParameters.projectionProbability parameters i : ℝ)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).1.le)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).2.le)

abbrev positiveRows (height : Nat) : 0 < FixedRows.rows parameters.plan (height + 1) :=
  FixedUpperCutTriangle.rows_positive parameters (height + 1)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (FixedParameters.branch parameters i) → Slots (FixedParameters.branch parameters) i)

abbrev experiment
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters) n
      (FixedRows.sourceLength parameters.plan hδ)))
    (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.experiment clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o
    (fun k _ => FixedParameters.branch_pos parameters k) (flags (i := i) parameters) σ

abbrev Descriptor (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.Descriptor clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o

def externalLaw (o : Outer (n := n) (j := j) (m := m) parameters) :
    FiniteDistribution (Descriptor parameters clauses hupper hij designated o) :=
  StoppedProjectedBuckets.externalLaw clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o
    (fun k _ => FixedParameters.branch_pos parameters k) (flags (i := i) parameters)

abbrev background (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.background clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o

abbrev scalarLaw (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.scalarLaw clauses (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) hupper hij designated (positiveRows parameters) o

abbrev upperRows (o : Outer (n := n) (j := j) (m := m) parameters) :=
  StoppedProjectedBuckets.rows_positive (FixedRows.rows parameters.plan) hupper (positiveRows parameters) o

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters) n
  (FixedRows.sourceLength parameters.plan hδ)))

local instance backgroundFintype_r92c44a_3 (o : Outer (n := n) (j := j) (m := m) parameters) :
    Fintype (HierarchicalAgreementMean.Background (rows := FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _
local instance rowSpaceFintype_r92c44a_13 (o : Outer (n := n) (j := j) (m := m) parameters) :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _
abbrev PairFiber (o : Outer (n := n) (j := j) (m := m) parameters) :=
  HierarchicalAgreementMean.PairRecord (rows := FixedRows.rows parameters.plan)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedExperiment.upper hupper o)

abbrev PairRecord :=
  (o : Outer (n := n) (j := j) (m := m) parameters) × PairFiber parameters clauses hupper o

def actualLaw (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    FiniteDistribution (PairRecord parameters clauses hupper) :=
  HierarchicalBucketFamily.actualPairLaw (experiment parameters clauses hupper hij designated σ) outer
    (externalLaw parameters clauses hupper hij designated)
    (background parameters clauses hupper hij designated)
    (scalarLaw parameters clauses hupper hij designated) (upperRows parameters hupper)

def referenceLaw (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    FiniteDistribution (PairRecord parameters clauses hupper) :=
  HierarchicalBucketFamily.referencePairLaw (experiment parameters clauses hupper hij designated σ) outer
    (HierarchicalBucketFamily.actualBackgrounds (experiment parameters clauses hupper hij designated σ)
      (externalLaw parameters clauses hupper hij designated)
      (background parameters clauses hupper hij designated)) (upperRows parameters hupper)

end
end PerfectCompleteness.FixedSourcePairVariation

end

end OAI
end


