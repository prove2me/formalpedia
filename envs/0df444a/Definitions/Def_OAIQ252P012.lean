-- Prove2me | Definitions.Def_OAIQ252P012
-- name    : OAIQ252P012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:45:37.595324+00:00
-- url     : https://prove2.me/theorems/48726835-f081-4f3b-9e9f-148695f2ed79
-- title:
--   Definitions bundle OAIQ252P012 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 383 declarations of OpenAI's Lean: 237 definitions, 1 inductive type or structure, 4 instances and 141 theorems. The definitions and types are `OAI.PerfectCompleteness.CleanPhysicalHighAverage.childStatistic`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.nativeDirection`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.questionStatistic`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.sourceStatistic`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.suffix`, `OAI.PerfectCompleteness.CleanPhysicalHighAverage.tapeStatistic`, `OAI.PerfectCompleteness.CleanPhysicalHighEvent.highEvent`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.lower`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.rawSample`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.visible`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.visiblePairKernel`, `OAI.PerfectCompleteness.CleanPhysicalRawChildren.fillChildren`, `OAI.PerfectCompleteness.CleanTreeFactors.allZero`, `OAI.PerfectCompleteness.CleanTreeFactors.rawLaw`, `OAI.PerfectCompleteness.CleanTreeFactors.zeroRaw`, `OAI.PerfectCompleteness.CutBucketTransport.nativeLaw`, `OAI.PerfectCompleteness.CutBucketTransport.rowSpaceFintype`, `OAI.PerfectCompleteness.CutBucketTransportActual.nativeLaw`, `OAI.PerfectCompleteness.CutBucketTransportActual.rowSpaceFintype`, `OAI.PerfectCompleteness.CutChildGrouping.rawLaw`, `OAI.PerfectCompleteness.CutContinuationAveraging.originalArrayLaw`, `OAI.PerfectCompleteness.CutGroupedProjection.cutProjection`, `OAI.PerfectCompleteness.CutGroupedProjection.factorPullback`, `OAI.PerfectCompleteness.CutGroupedProjection.tapePullback`, `OAI.PerfectCompleteness.CutGroupedProjection.terminalPullback`, `OAI.PerfectCompleteness.CutNativeForms.formCast`, `OAI.PerfectCompleteness.CutNativeForms.projectionCast`, `OAI.PerfectCompleteness.CutNativeForms.spaceCast`, `OAI.PerfectCompleteness.CutNodeRows.bucketSampleEquiv`, `OAI.PerfectCompleteness.CutNodeRows.bucketTapeEquiv`, `OAI.PerfectCompleteness.CutNodeRows.cutRowEquiv`, `OAI.PerfectCompleteness.CutNodeRows.directionEquiv`, `OAI.PerfectCompleteness.CutNodeRows.matrixOfRows`, `OAI.PerfectCompleteness.CutNodeRows.nativeEquiv`, `OAI.PerfectCompleteness.CutNodeRows.rowIndexEquiv`, `OAI.PerfectCompleteness.CutNodeRows.transportRows`, `OAI.PerfectCompleteness.CutSamplerRefinement.evaluate`, `OAI.PerfectCompleteness.CutSamplerRefinement.tapeLaw`, `OAI.PerfectCompleteness.CutSamplerReplay.erase`, `OAI.PerfectCompleteness.CutSamplerReplay.evaluate` and 198 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas`, `PerfectCompleteness_Construction_CutBucketTransportLemmas`, `PerfectCompleteness_Construction_CutChildGrouping`, `PerfectCompleteness_Construction_CutNodeRows`, `PerfectCompleteness_Construction_SourcePhysicalChildExpectation`, `PerfectCompleteness_Construction_SourcePhysicalTaggedChildren`, `PerfectCompleteness_Construction_SourceQuestionCutSplit`, `PerfectCompleteness_Construction_SourceQuestionKernelJoint`, `PerfectCompleteness_Construction_SourceQuestionPositionSplit`, `PerfectCompleteness_Construction_SourceQuestionRawSwap`, `PerfectCompleteness_Decoding_CutGroupedProjectionLemmas`, `PerfectCompleteness_Decoding_DecoderFamilyLawLemmas`, `PerfectCompleteness_Decoding_HierarchicalAllDecoderTables`, `PerfectCompleteness_Decoding_HierarchicalDecoderTables`, `PerfectCompleteness_Decoding_LowerCutFiberDisintegrationLemmas`, `PerfectCompleteness_Decoding_LowerCutNodeCoordinates`, `PerfectCompleteness_Decoding_LowerCutPairBackground`, `PerfectCompleteness_Decoding_LowerCutPairLemmas`, `PerfectCompleteness_Decoding_LowerCutRowsLemmas`, `PerfectCompleteness_Decoding_LowerProjectedOriginalSuccessLemmas`, `PerfectCompleteness_Decoding_ProjectedLowerFiber`, `PerfectCompleteness_Foundations_CutContinuationAveraging`, `PerfectCompleteness_Foundations_CutNativeForms`, `PerfectCompleteness_Foundations_CutSlotAssembly`, `PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas`, `PerfectCompleteness_Foundations_NormalizationLemmas`, `PerfectCompleteness_Foundations_OriginalTerminalSplitLemmas`, `PerfectCompleteness_Foundations_OriginalWholeCut`, `PerfectCompleteness_Foundations_PCPSource`, `PerfectCompleteness_Foundations_PCPSourceHardness`, `PerfectCompleteness_Foundations_ProjectedFiberBackground`, `PerfectCompleteness_Foundations_ProjectedFiberRawPair`, `PerfectCompleteness_Foundations_ProjectedFiberSquare`, `PerfectCompleteness_Foundations_SignedTupleLayout`, `PerfectCompleteness_Foundations_SourceProjectedTag`, `PerfectCompleteness_Foundations_SourceTupleData`, `PerfectCompleteness_Foundations_SourceTuplePlacement`, `PerfectCompleteness_Foundations_SourceTupleResetPlacementLemmas`, `PerfectCompleteness_Foundations_WholeCutCallsLemmas`, `PerfectCompleteness_Foundations_WholeReplaySubtreeLemmas`, `PerfectCompleteness_Machines_ExactTargetOdometer`, `PerfectCompleteness_Machines_LowerCutDecoderInput`, `PerfectCompleteness_Machines_LowerCutOwnInput`, `PerfectCompleteness_Machines_OriginalWholeCutTape`, `PerfectCompleteness_Machines_OwnInputAffineSliceLemmas`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Machines_PreprocessingMachineLemmas`, `PerfectCompleteness_Machines_SignedDescriptorStageMachine`, `PerfectCompleteness_Machines_SignedTupleBodyMachine`, `PerfectCompleteness_Machines_SignedTupleCleanupMachineLemmas`, `PerfectCompleteness_Machines_SourceClauseLookupMachine`, `PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas`, `PerfectCompleteness_Machines_SourceClauseSelectMachine`, `PerfectCompleteness_Machines_SourceCoordinateMachine`, `PerfectCompleteness_Machines_SourceOccurrenceProducerLemmas`, `PerfectCompleteness_Machines_SourceTupleMachine`, `PerfectCompleteness_Machines_SourceTupleResetMachine`, `PerfectCompleteness_Machines_WholeArrayInteriorOwnInputLaw`, `PerfectCompleteness_Reduction_FixedRows`, `PerfectCompleteness_Reduction_NormalizedTarget`, `PerfectCompleteness_Repetition_CleanPhysicalHighAverage`, `PerfectCompleteness_Repetition_CleanPhysicalHighEvent`, `PerfectCompleteness_Repetition_CleanPhysicalProjectedMeeting`, `PerfectCompleteness_Repetition_CleanPhysicalRawChildren`, `PerfectCompleteness_Repetition_CleanPhysicalReplay`, `PerfectCompleteness_Repetition_CleanRecordChildBlocks`, `PerfectCompleteness_Repetition_CleanTreeFactors`, `PerfectCompleteness_Repetition_CutChildCleanLawLemmas`, `PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas`, `PerfectCompleteness_Sampling_CutSamplerRefinement`, `PerfectCompleteness_Sampling_CutSamplerReplayGroupingTransport`, `PerfectCompleteness_Sampling_OriginalWholeCutLaw`, `PerfectCompleteness_Sampling_SamplerComposition`, `PerfectCompleteness_Sampling_SourceChildKernelLaw`, `PerfectCompleteness_Sampling_SourceChildKernelMarginalLemmas`, `PerfectCompleteness_Sampling_SourceChildMarkedLaw`, `PerfectCompleteness_Sampling_SourceChildQuestionLaw`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_Machines_MachineRegularTable`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P007`, `OAIQ252P008` and `OAIQ252P009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P016` and `OAIQ252P017`; the statements `OAI.PerfectCompleteness.CleanPhysicalHighEvent.mean_probability_eq`, `OAI.PerfectCompleteness.CleanPhysicalProjectedMeeting.leftLaw_eq_visible`, `OAI.PerfectCompleteness.CleanPhysicalReplayLaw.evaluate_physicalTape_law`, `OAI.PerfectCompleteness.OriginalWholeCutComparison.totalVariation_le`, `OAI.PerfectCompleteness.SourcePhysicalTapeFiber.collapse_physicalTape_law`, `OAI.PerfectCompleteness.WholeArrayInteriorOwnInputLaw.exterior_split` and `OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback`; the proofs of `OAI.PerfectCompleteness.WholeArrayInteriorOwnInputLaw.exterior_split` and `OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback`.
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
import Definitions.Def_OAIQ252P007
import Definitions.Def_OAIQ252P008
import Definitions.Def_OAIQ252P009

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.HierarchicalTensorMatrix

noncomputable section

open scoped BigOperators TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (W : Submodule F2 (Block rows upper))

def visibleMatrix
    (known : HiddenBucketBias.VisibleDirection W → NodeEmbedding.NodeH slots upper) :
    Module.Dual F2 (NodeEmbedding.RowSpace slots upper) →ₗ[F2] Block rows upper :=
  ∑ v : HiddenBucketBias.VisibleDirection W,
    (Module.Dual.eval F2 (NodeEmbedding.RowSpace slots upper)
      (NodeEmbedding.embed slots upper (known v))).smulRight v.val.val

end
end PerfectCompleteness.HierarchicalTensorMatrix



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerRefinement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerRefinement

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def tapeLaw (𝕜 : Type w) [Field 𝕜] [Finite 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (Tape 𝕜 repeats p A) :=
  FiniteProduct.law (fun j => FiniteDistribution.uniform (RefinedSpace 𝕜 repeats p A j))

def evaluate (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) (x : Tape 𝕜 repeats p A) :
    space 𝕜 branch n A :=
  RecursiveSampler.evaluate 𝕜 repeats p A (collapse 𝕜 repeats p A x)

end
end PerfectCompleteness.CutSamplerRefinement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CutSamplerKeyLocality

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open CutSamplerLocality

noncomputable section

universe u

variable {branch : Nat → Nat} {n m t : Nat}

theorem keptLeaf_at_cut (p : Path branch n (m + 1))
    (clean : Fin (branch m) → Prop) (i : Fin (branch m)) (s : Slots branch m) :
    keptLeaf p clean (p.slotEmbedding (i, s)) ↔ ¬ clean i := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl => rfl
      | step j p =>
          change (j ≠ j ∨ keptLeaf p clean (p.slotEmbedding (i, s))) ↔ ¬ clean i
          simpa only [ne_self_iff_false, false_or] using ih p clean i s


end
end PerfectCompleteness.CutSamplerKeyLocality



namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

def erase (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → CutSamplerRefinement.Tape 𝕜 repeats p A →
        Tape 𝕜 repeats p A clean
  | _, _, .refl _, _, _, tape => fun i => tape () i.val
  | _, _, .step i p, A, clean, tape =>
      (fun j => tape (.inl j), fun call => erase 𝕜 repeats p (childFamily A i) clean
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape call.1 call.2))

def evaluate (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) → (A : Slots branch n → Type u) →
      (clean : Fin (branch m) → Prop) → Tape 𝕜 repeats p A clean → Assignment A → 𝕜
  | _, m, .refl _, A, clean, tape, x =>
      ∑ i : {i : Fin (branch m) // ¬ clean i}, (tape i).val (childRestriction A i.val x)
  | n + 1, _, .step i p, A, clean, tape, x =>
      (∑ j : OffPath i, (tape.1 j).val (childRestriction A j.val x)) +
        ∑ h : Fin (repeats (n + 1)),
          evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, false)) (childRestriction A i x) *
            evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, true)) (childRestriction A i x)

end
end PerfectCompleteness.CutSamplerReplay



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SamplerComposition
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
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

def expandedSubTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m) (q : Path branch m k)
    (A : Slots branch (n + 1) → Type u)
    (t : ExpandedTape 𝕜 repeats (.step i p) q A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    ExpandedTape 𝕜 repeats p q (childFamily A i) := fun j => t (.inr ((h, b), j))

def expand (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → RecursiveSampler.Tape 𝕜 repeats (p.append q) A →
        ExpandedTape 𝕜 repeats p q A
  | _, _, _, .refl _, _, _, t => fun _ => t
  | _n + 1, _, _, .step i p, q, A, t => fun j =>
      match j with
      | Sum.inl j => t (.inl j)
      | Sum.inr j => expand 𝕜 repeats p q (childFamily A i)
          (subTape 𝕜 repeats i (p.append q) A t j.1.1 j.1.2) j.2

def flatten (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n m) → (q : Path branch m k) →
      (A : Slots branch n → Type u) → ExpandedTape 𝕜 repeats p q A →
        RecursiveSampler.Tape 𝕜 repeats (p.append q) A
  | _, _, _, .refl _, _, _, t => t ()
  | _n + 1, _, _, .step i p, q, A, t => fun j =>
      match j with
      | Sum.inl j => t (.inl j)
      | Sum.inr j => flatten 𝕜 repeats p q (childFamily A i)
          (expandedSubTape 𝕜 repeats i p q A t j.1.1 j.1.2) j.2

theorem flatten_expand (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (t : RecursiveSampler.Tape 𝕜 repeats (p.append q) A),
      flatten 𝕜 repeats p q A (expand 𝕜 repeats p q A t) = t := by
  induction p with
  | refl n => intro q A t; rfl
  | @step n m i p ih =>
      intro q A t
      funext j
      cases j with
      | inl j => rfl
      | inr j =>
          exact congrFun
            (ih q (childFamily A i) (subTape 𝕜 repeats i (p.append q) A t j.1.1 j.1.2)) j.2

theorem expand_flatten (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (t : ExpandedTape 𝕜 repeats p q A),
      expand 𝕜 repeats p q A (flatten 𝕜 repeats p q A t) = t := by
  induction p with
  | refl n =>
      intro q A t
      funext j
      cases j
      rfl
  | @step n m i p ih =>
      intro q A t
      funext j
      cases j with
      | inl j => rfl
      | inr j =>
          exact congrFun
            (ih q (childFamily A i) (expandedSubTape 𝕜 repeats i p q A t j.1.1 j.1.2)) j.2

def expandEquiv (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u) :
    RecursiveSampler.Tape 𝕜 repeats (p.append q) A ≃ ExpandedTape 𝕜 repeats p q A where
  toFun := expand 𝕜 repeats p q A
  invFun := flatten 𝕜 repeats p q A
  left_inv := flatten_expand 𝕜 repeats p q A
  right_inv := expand_flatten 𝕜 repeats p q A

end
end PerfectCompleteness.SamplerComposition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalTerminalSplitLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalTerminalSplit

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls SamplerComposition
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u)

def splitTape : RecursiveSampler.Tape 𝕜 repeats (p.append q) A ≃
    TerminalTape 𝕜 repeats p q A × ExteriorTape 𝕜 repeats p A :=
  (expandEquiv 𝕜 repeats p q A).trans (splitExpanded 𝕜 repeats p q A)

end
end PerfectCompleteness.OriginalTerminalSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutCallsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OriginalCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

def rootCall (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (origin : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) :
    Index rows repeats (.step i p) := Sum.inl origin

def lowerCall (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (origin : Index rows repeats p) : Index rows repeats (.step i p) := Sum.inr origin

end
end PerfectCompleteness.OriginalCutCalls

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanTreeFactors
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanTreeFactors

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open ProjectedCardinality FiniteProduct CleanConditioning

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

instance rawFintype (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : Fintype (Raw calls rows ids) :=
  Fintype.ofFinite _

def zeroRaw (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : Raw calls rows ids :=
  (fun _ => 0, fun _ _ => 0)

instance rawNonempty (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : Nonempty (Raw calls rows ids) :=
  ⟨zeroRaw calls rows ids⟩

def rawLaw (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) : FiniteDistribution (Raw calls rows ids) :=
  (law (fun j : Index branch n calls rows =>
    FiniteDistribution.uniform (Factors calls rows ids j))).pushforward (rawEquiv calls rows ids)

def allZero (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) (x : Raw calls rows ids) : Bool := by
  classical
  exact decide ((∀ q, x.1 q = 0) ∧ ∀ node row, x.2 node row = 0)

end
end PerfectCompleteness.CleanTreeFactors

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutChildGrouping
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutChildGrouping

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

def rawLaw : FiniteDistribution (Raw (C := C) slots rows) :=
  FiniteProduct.law (fun i => FiniteDistribution.uniform (Child (C := C) slots rows i))

end
end PerfectCompleteness.CutChildGrouping

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OriginalWholeCutTape
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev cutSlots (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Slots branch m → Fin t → MixedSupport.Slot :=
  fun s => slots (p.slotEmbedding s)

def Exterior (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (Slots branch n → Fin t → MixedSupport.Slot) → Type
  | _, _, .refl _, _ => Unit
  | n + 1, _, .step i p, slots =>
      (BucketSampler.Direction (rows (n + 1)) →
        OriginalTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
      (Exterior rows repeats p (childSlots slots i) ×
        ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))

@[instance_reducible] def exteriorFintypeAux (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        Fintype (Exterior rows repeats p slots)
  | _, _, .refl _, _ => inferInstanceAs (Fintype Unit)
  | n + 1, _, .step i p, slots =>
      letI : Fintype (Exterior rows repeats p (childSlots slots i)) :=
        exteriorFintypeAux rows repeats p (childSlots slots i)
      inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) →
          OriginalTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) ×
        (Exterior rows repeats p (childSlots slots i) ×
          ((j : RecursiveSampler.OffPath i) → Arrays (childSlots slots j.val) rows))))

abbrev BelowTape (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :=
  WholeArraySampler.Tape rows repeats q (childSlots slots chosen) ×
    ((j : RecursiveSampler.OffPath chosen) → Arrays (childSlots slots j.val) rows)

abbrev Calls (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalCutCalls.Index rows repeats p →
    RecursiveSampler.Tape F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))

def splitTape (rows repeats : Nat → Nat) :
    {n m k : Nat} → (p : Path branch n (m + 1)) → (chosen : Fin (branch m)) →
      (q : Path branch m k) → (slots : Slots branch n → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots ≃
          Exterior rows repeats p slots ×
            (Calls rows repeats p chosen q slots ×
              BelowTape rows repeats chosen q (cutSlots p slots))
  | _, _, _, .refl _, chosen, q, slots =>
      (WholeCutSampler.stepEquiv chosen
        (WholeArraySampler.RootTape rows repeats (.step chosen q) slots)
        (WholeArraySampler.Tape rows repeats q (childSlots slots chosen))
        (fun j => Arrays (childSlots slots j.val) rows)).symm.trans (prependUnit _)
  | n + 1, _, _, .step i p, chosen, q, slots =>
      (WholeCutSampler.stepEquiv i
        (WholeArraySampler.RootTape rows repeats (.step i (p.append (.step chosen q))) slots)
        (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows)).symm.trans
        ((Equiv.prodCongr
          (Equiv.piCongrRight (fun _ : BucketSampler.Direction (rows (n + 1)) =>
            OriginalTerminalSplit.splitTape F2 repeats (.step i p) (.step chosen q)
              (LeafDomain slots)))
          (Equiv.prodCongr (splitTape rows repeats p chosen q (childSlots slots i))
            (Equiv.refl _))).trans regroupStep)

@[simp] theorem splitTape_refl (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats (.step chosen q) slots) :
    splitTape rows repeats (.refl (m + 1)) chosen q slots ω =
      ((), (ω (.inl ()), (ω (.inr (.inl ())), fun j => ω (.inr (.inr j))))) := rfl

@[simp] theorem splitTape_step_exterior (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots) :
    (splitTape rows repeats (.step i p) chosen q slots ω).1 =
      ((fun v => (OriginalTerminalSplit.splitTape F2 repeats (.step i p) (.step chosen q)
          (LeafDomain slots) (ω (.inl ()) v)).2),
        ((splitTape rows repeats p chosen q (childSlots slots i) (ω (.inr (.inl ())))).1,
          fun j => ω (.inr (.inr j)))) := rfl

@[simp] theorem splitTape_step_rootCall (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots)
    (v : BucketSampler.Direction (rows (n + 1)))
    (terminal : TerminalCalls.TerminalIndex repeats (.step i p)) :
    (splitTape rows repeats (.step i p) chosen q slots ω).2.1
        (OriginalCutCalls.rootCall rows repeats i p (v, terminal)) =
      (OriginalTerminalSplit.splitTape F2 repeats (.step i p) (.step chosen q)
        (LeafDomain slots) (ω (.inl ()) v)).1 terminal := rfl

@[simp] theorem splitTape_step_lowerCall (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots)
    (call : OriginalCutCalls.Index rows repeats p) :
    (splitTape rows repeats (.step i p) chosen q slots ω).2.1
        (OriginalCutCalls.lowerCall rows repeats i p call) =
      (splitTape rows repeats p chosen q (childSlots slots i) (ω (.inr (.inl ())))).2.1 call := rfl

@[simp] theorem splitTape_step_below (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.Tape rows repeats ((Path.step i p).append (.step chosen q)) slots) :
    (splitTape rows repeats (.step i p) chosen q slots ω).2.2 =
      (splitTape rows repeats p chosen q (childSlots slots i) (ω (.inr (.inl ())))).2.2 := rfl

end

end PerfectCompleteness.OriginalWholeCutTape

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutNodeRows
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutNodeRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {N cut t : Nat}

def nativeEquiv : {N cut : Nat} → (p : Path branch N (cut + 1)) →
    (slots : Slots branch N → Fin t → MixedSupport.Slot) →
      H (cutSlots p slots) ≃ₗ[F2] NodeEmbedding.NodeH slots (upperNode p)
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => nativeEquiv p (childSlots slots i)

def cutRowEquiv (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    H (cutSlots p slots) ≃ₗ[F2] NodeEmbedding.RowSpace slots (upperNode p) :=
  (nativeEquiv p slots).trans (NodeEmbedding.equiv slots (upperNode p))

def rowIndexEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1)) :
    Fin (rows (cut + 1)) ≃ Fin (rows (Nodes.height (upperNode p))) :=
  Equiv.cast (congrArg (fun height => Fin (rows height)) (upperNode_height p).symm)

def directionEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1)) :
    BucketSampler.Direction (rows (cut + 1)) ≃
      BucketSampler.Direction (rows (Nodes.height (upperNode p))) :=
  Equiv.cast (congrArg (fun height => BucketSampler.Direction (rows height))
    (upperNode_height p).symm)

def transportRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (fresh : Fin (rows (cut + 1)) → H (cutSlots p slots)) :
    Fin (rows (Nodes.height (upperNode p))) → NodeEmbedding.RowSpace slots (upperNode p) :=
  fun i => cutRowEquiv p slots (fresh ((rowIndexEquiv rows p).symm i))

def matrixOfRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (fresh : Fin (rows (cut + 1)) → H (cutSlots p slots)) :
    HierarchicalMatrixTable.Matrix (rows := rows) slots (upperNode p) :=
  EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots (upperNode p))
    (transportRows rows p slots fresh)

def bucketTapeEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots)) ≃
      BucketSampler.Tape (rows (Nodes.height (upperNode p)))
        (NodeEmbedding.RowSpace slots (upperNode p)) :=
  Equiv.arrowCongr (directionEquiv rows p) (cutRowEquiv p slots).toEquiv

def bucketSampleEquiv (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) :
    (BucketSampler.Direction (rows (cut + 1)) ×
      (BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots)) × H (cutSlots p slots))) ≃
    (BucketSampler.Direction (rows (Nodes.height (upperNode p))) ×
      (BucketSampler.Tape (rows (Nodes.height (upperNode p)))
        (NodeEmbedding.RowSpace slots (upperNode p)) ×
          NodeEmbedding.RowSpace slots (upperNode p))) :=
  (directionEquiv rows p).prodCongr
    ((bucketTapeEquiv rows p slots).prodCongr (cutRowEquiv p slots).toEquiv)

end
end PerfectCompleteness.CutNodeRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutBucketTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutBucketTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

def nativeLaw (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots))) := by
  letI : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).product
    ((BucketSampler.tapeLaw (rows (m + 1))
      (FiniteDistribution.uniform (H (cutSlots p slots)))).product
        (FiniteDistribution.uniform (H (cutSlots p slots))))

end
end PerfectCompleteness.CutBucketTransport

end

section

namespace PerfectCompleteness.CutBucketTransportActual

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

def nativeLaw (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots))) (hrows : 0 < rows (m + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots))) := by
  letI : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).product
    ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)

end
end PerfectCompleteness.CutBucketTransportActual

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CutChildCleanLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays ProjectedCardinality

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (ids : Slots branch n → Fin t → Nat)

instance rawFintype : Fintype (Raw (C := C) rows ids) := Fintype.ofFinite _


end
end PerfectCompleteness.CutChildCleanLaw



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildKernelLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev Physical (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :=
  Σ b : Bool, Block C rows (mixedSlots clauses designated i s b)

def physical (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Physical (C := C) (t := t) rows clauses designated i s :=
  ⟨rawProjected rows clauses designated i raw,
    decodeRight rows clauses designated i s raw⟩

@[simp] theorem physical_inl (i : Fin (branch n))
    (s : Source (m := m) (t := t) designated i)
    (raw : D (C := C) (t := t) rows clauses designated i) :
    physical rows clauses designated i s (.inl raw) =
      (⟨false, decodeNative rows clauses designated i s raw⟩ :
        Physical (C := C) (t := t) rows clauses designated i s) := rfl

@[simp] theorem physical_inr (i : Fin (branch n))
    (s : Source (m := m) (t := t) designated i)
    (raw : UniformLatent.Raw (Factors (C := C) (t := t) rows clauses designated i)) :
    physical rows clauses designated i s (.inr raw) =
      (⟨true, decodeProjected rows clauses designated i s raw⟩ :
        Physical (C := C) (t := t) rows clauses designated i s) := rfl

end
end PerfectCompleteness.SourceChildKernelLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourcePhysicalTaggedChildren
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTaggedChildren

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def slots (sources : Sources (m := m) (t := t) designated)
    (flags : Fin (branch n) → Bool) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf k => mixedSlots clauses designated leaf.1 (sources leaf.1)
    (flags leaf.1) leaf.2 k

def pack (sources : Sources (m := m) (t := t) designated) :
    ((i : Fin (branch n)) →
      SourceChildKernelLaw.Physical (C := C) (t := t) rows clauses designated i (sources i)) ≃
      Σ flags : Fin (branch n) → Bool,
        CutChildGrouping.Raw (C := C) (slots clauses designated sources flags) rows where
  toFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  invFun x i := ⟨x.1 i, x.2 i⟩
  left_inv x := by
    funext i
    exact Sigma.eta (x i)
  right_inv x := by
    cases x
    rfl

def observe (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    Σ flags : Fin (branch n) → Bool,
      CutChildGrouping.Raw (C := C) (slots clauses designated sources flags) rows :=
  pack rows clauses designated sources
    (fun i => SourceChildKernelLaw.physical rows clauses designated i (sources i) (raw i))

@[simp] theorem observe_fst (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    (observe rows clauses designated sources raw).1 =
      fun i => rawProjected rows clauses designated i (raw i) := rfl

@[simp] theorem observe_snd (sources : Sources (m := m) (t := t) designated)
    (raw : (i : Fin (branch n)) → Raw (C := C) (t := t) rows clauses designated i) :
    (observe rows clauses designated sources raw).2 =
      rightChildren rows clauses designated sources raw := rfl

end
end PerfectCompleteness.SourcePhysicalTaggedChildren

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutSlotAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSlotAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces

variable {branch : Nat → Nat} {n m : Nat} {V : Type*}

theorem fill_restrict (p : Path branch n m) (outside : Slots branch n → V) :
    fill p outside (fun s => outside (p.slotEmbedding s)) = outside := by
  induction p with
  | refl _ => rfl
  | step i p ih =>
      funext s
      by_cases hs : s.1 = i
      · obtain ⟨j, s⟩ := s
        dsimp only at hs
        subst j
        simp only [fill]
        exact congrFun (ih (fun j => outside (i, j))) s
      · simp only [fill, ite_eq_right hs]

end
end PerfectCompleteness.CutSlotAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionCutSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionOrder.tupleToQuestion_questionToTuple _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionCutSplit

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t m : Nat}

abbrev OutsideQuestions (p : Path branch root h) (t m : Nat) :=
  OutsideLeaf p → Fin t → Fin m

def restrict (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    PreliminarySampler.Questions branch h t m :=
  fun leaf => q (p.slotEmbedding leaf)

def outside (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) : OutsideQuestions p t m :=
  fun leaf => q leaf.val

def join (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m) :
    PreliminarySampler.Questions branch root t m :=
  fun leaf => if hleaf : leaf ∈ Set.range p.slotEmbedding then
    inside (Classical.choose hleaf) else external ⟨leaf, hleaf⟩

@[simp] theorem join_at_cut (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m)
    (leaf : Slots branch h) :
    join p inside external (p.slotEmbedding leaf) = inside leaf := by
  have hleaf : p.slotEmbedding leaf ∈ Set.range p.slotEmbedding := ⟨leaf, rfl⟩
  have hchoose : Classical.choose hleaf = leaf :=
    p.slotEmbedding_injective (Classical.choose_spec hleaf)
  simp only [join, dite_eq_left hleaf, hchoose]

@[simp] theorem join_outside (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m)
    (leaf : OutsideLeaf p) :
    join p inside external leaf.val = external leaf := by
  simp only [join, dite_eq_right leaf.property]

theorem join_restrict (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    join p (restrict p q) (outside p q) = q := by
  funext leaf
  by_cases hleaf : leaf ∈ Set.range p.slotEmbedding
  · simp only [join, dite_eq_left hleaf, restrict, Classical.choose_spec hleaf]
  · simp only [join, dite_eq_right hleaf, outside]

def splitEquiv (p : Path branch root h) :
    PreliminarySampler.Questions branch root t m ≃
      PreliminarySampler.Questions branch h t m × OutsideQuestions p t m where
  toFun q := (restrict p q, outside p q)
  invFun parts := join p parts.1 parts.2
  left_inv q := join_restrict p q
  right_inv parts := by
    apply Prod.ext
    · funext leaf
      exact join_at_cut p parts.1 parts.2 leaf
    · funext leaf
      exact join_outside p parts.1 parts.2 leaf

@[simp] theorem splitEquiv_apply (p : Path branch root h)
    (q : PreliminarySampler.Questions branch root t m) :
    splitEquiv p q = (restrict p q, outside p q) := rfl

@[simp] theorem splitEquiv_symm_apply (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m) (external : OutsideQuestions p t m) :
    (splitEquiv p).symm (inside, external) = join p inside external := rfl

end
end PerfectCompleteness.SourceQuestionCutSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildKernelMarginalLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

def pullback (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) (b : Bool)
    (block : Block C rows (mixedSlots clauses designated i s b)) :
    Native (C := C) (t := t) rows clauses designated i s :=
  (fun call => ChildBlockProjection.squarePullback (projection clauses designated i s b)
      (block.1 call),
    ChildBlockProjection.arraysPullback rows (projection clauses designated i s b) block.2)

omit [Fintype C] in
@[simp] theorem pullback_false (i : Fin (branch n))
    (s : Source (m := m) (t := t) designated i)
    (block : Native (C := C) (t := t) rows clauses designated i s) :
    pullback rows clauses designated i s false block = block := by
  apply Prod.ext
  · funext call
    apply Subtype.ext
    funext x
    rfl
  · funext node row
    apply Subtype.ext
    funext x
    rfl

def physicalLeft (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (x : SourceChildKernelLaw.Physical (C := C) (t := t) rows clauses designated i s) :
    Native (C := C) (t := t) rows clauses designated i s :=
  pullback rows clauses designated i s x.1 x.2

def decodeLeft (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Native (C := C) (t := t) rows clauses designated i s :=
  physicalLeft rows clauses designated i s
    (SourceChildKernelLaw.physical rows clauses designated i s raw)

end
end PerfectCompleteness.SourceChildNativeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildQuestionLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

def assembleEquiv (designated : Fin (branch n) → Slots branch n) :
    SourceChildKernel.Sources (m := m) (t := t) designated ≃
      (Slots branch (n + 1) → SourceTuple m t) where
  toFun sources leaf := CleanSourceRecord.assemble designated leaf.1
    (sources leaf.1).1 (sources leaf.1).2 leaf.2
  invFun tree i := (Equiv.piSplitAt (designated i) (fun _ : Slots branch n => SourceTuple m t))
    (fun leaf => tree (i, leaf))
  left_inv sources := by
    funext i
    exact (Equiv.piSplitAt (designated i) (fun _ : Slots branch n => SourceTuple m t)).apply_symm_apply
      (sources i)
  right_inv tree := by
    funext leaf
    exact congrFun
      ((Equiv.piSplitAt (designated leaf.1) (fun _ : Slots branch n => SourceTuple m t)).symm_apply_apply
        (fun s => tree (leaf.1, s))) leaf.2

def questions (designated : Fin (branch n) → Slots branch n)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    PreliminarySampler.Questions branch (n + 1) t m :=
  fun leaf k => (assembleEquiv designated sources leaf k).1

theorem parentLeftSlots_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated) :
    SourceChildKernel.parentLeftSlots clauses designated sources =
      HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints (questions designated sources)) := rfl

end
end PerfectCompleteness.SourceChildQuestionLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPositionSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPositionSplit

noncomputable section

open scoped Classical
open RecursiveSpaces SourceQuestionReconstruction TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m : Nat}

abbrev Positions := Slots branch (n + 1) → Fin t → Fin 3
abbrev ChildPositions := Slots branch n → Fin t → Fin 3

def splitTree : (Slots branch (n + 1) → SourceTuple m t) ≃
    Questions (branch := branch) (n := n) (t := t) (m := m) ×
      Positions (branch := branch) (n := n) (t := t) where
  toFun tree := (fun leaf k => (tree leaf k).1, fun leaf k => (tree leaf k).2)
  invFun parts leaf k := (parts.1 leaf k, parts.2 leaf k)
  left_inv _ := rfl
  right_inv _ := rfl

def split (designated : Fin (branch n) → Slots branch n) :
    SourceChildKernel.Sources (m := m) (t := t) designated ≃
      Questions (branch := branch) (n := n) (t := t) (m := m) ×
        Positions (branch := branch) (n := n) (t := t) :=
  (SourceChildQuestionLaw.assembleEquiv (m := m) (t := t) designated).trans splitTree

def join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  (split designated).symm (q, positions)

@[simp] theorem questions_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildQuestionLaw.questions designated (join designated q positions) = q :=
  congrArg Prod.fst ((split designated).apply_symm_apply (q, positions))

def byChild : Positions (branch := branch) (n := n) (t := t) ≃
    (Fin (branch n) → ChildPositions (branch := branch) (n := n) (t := t)) where
  toFun positions i leaf k := positions (i, leaf) k
  invFun positions leaf k := positions leaf.1 leaf.2 k
  left_inv _ := rfl
  right_inv _ := rfl

theorem parentLeftSlots_join {v : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildKernel.parentLeftSlots clauses designated (join designated q positions) =
      HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q) := by
  rw [SourceChildQuestionLaw.parentLeftSlots_eq, questions_join]

end
end PerfectCompleteness.SourceQuestionPositionSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionKernelJoint
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionKernelJoint

open scoped Classical
open RecursiveSpaces SourceQuestionPositionSplit
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat}

abbrev ChoiceTuple :=
  Fin (branch n) → ChildPositions (branch := branch) (n := n) (t := t)

def sourceEquiv (designated : Fin (branch n) → Slots branch n) :
    SourceChildKernel.Sources (m := m) (t := t) designated ≃
      Questions (branch := branch) (n := n) (t := t) (m := m) ×
        ChoiceTuple (branch := branch) (n := n) (t := t) :=
  (SourceQuestionPositionSplit.split designated).trans
    (Equiv.prodCongr (Equiv.refl _) SourceQuestionPositionSplit.byChild)

def sources (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (choices : ChoiceTuple (branch := branch) (n := n) (t := t)) :
    SourceChildKernel.Sources (m := m) (t := t) designated :=
  (sourceEquiv designated).symm (q, choices)

@[simp] theorem sources_eq_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (choices : ChoiceTuple (branch := branch) (n := n) (t := t)) :
    sources designated q choices =
      SourceQuestionPositionSplit.join designated q
        (SourceQuestionPositionSplit.byChild.symm choices) := rfl

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def groupEquiv :
    SourceChildKernel.Sample (C := C) (t := t) rows clauses designated ≃
      (Questions (branch := branch) (n := n) (t := t) (m := m) ×
        ChoiceTuple (branch := branch) (n := n) (t := t)) ×
          SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated :=
  (SourceChildKernelJoint.groupEquiv rows clauses designated).trans
    (Equiv.prodCongr (sourceEquiv designated) (Equiv.refl _))

@[simp] theorem groupEquiv_raw
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (i : Fin (branch n)) :
    (groupEquiv rows clauses designated sample).2 i = (sample i).2.2 := rfl

end
end PerfectCompleteness.SourceQuestionKernelJoint

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedTag
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev Tag :=
  SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) ×
    Flags (branch := branch) (n := n)

def sourceFlagEquiv (designated : Fin (branch n) → Slots branch n) :
    (SourceChildKernel.Sources (m := m) (t := t) designated ×
      Flags (branch := branch) (n := n)) ≃
    SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m) ×
      Tag (branch := branch) (n := n) (t := t) :=
  (Equiv.prodCongr (SourceQuestionKernelJoint.sourceEquiv designated) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

@[simp] theorem sourceFlagEquiv_apply (designated : Fin (branch n) → Slots branch n)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (flags : Flags (branch := branch) (n := n)) :
    sourceFlagEquiv designated (sources, flags) =
      ((SourceQuestionKernelJoint.sourceEquiv designated sources).1,
        ((SourceQuestionKernelJoint.sourceEquiv designated sources).2, flags)) := rfl

@[simp] theorem sourceFlagEquiv_symm_apply (designated : Fin (branch n) → Slots branch n)
    (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
    (tag : Tag (branch := branch) (n := n) (t := t)) :
    (sourceFlagEquiv designated).symm (q, tag) =
      (SourceQuestionKernelJoint.sources designated q tag.1, tag.2) := rfl

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
  (flags : Flags (branch := branch) (n := n))

def originalSlots : Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)

theorem parentLeftSlots_sources :
    SourceChildKernel.parentLeftSlots clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) =
      originalSlots clauses q := by
  rw [SourceQuestionKernelJoint.sources_eq_join,
    SourceQuestionPositionSplit.parentLeftSlots_join]
  rfl

def mixedInside : Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  fun leaf j => SourceChildKernel.mixedSlots clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1) (flags leaf.1) leaf.2 j

def projection : ∀ leaf j, MixedSupport.Projection (originalSlots clauses q leaf j)
    (mixedInside clauses designated q choices flags leaf j) := by
  intro leaf j
  have hslots := congrFun (congrFun (parentLeftSlots_sources clauses designated q choices) leaf) j
  change SourceChildKernel.nativeSlots clauses designated leaf.1
      (SourceQuestionKernelJoint.sources designated q choices leaf.1) leaf.2 j =
    originalSlots clauses q leaf j at hslots
  rw [← hslots]
  exact SourceChildKernel.projection clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1) (flags leaf.1) leaf.2 j

end
end PerfectCompleteness.SourceProjectedTag

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionRawSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

@[simp] theorem restrict_join (p : Path branch root h)
    (inside : PreliminarySampler.Questions branch h t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m) :
    SourceQuestionCutSplit.restrict p (SourceQuestionCutSplit.join p inside external) =
      inside := by
  funext leaf
  exact SourceQuestionCutSplit.join_at_cut p inside external leaf

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def raw
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated :=
  (SourceQuestionKernelJoint.groupEquiv rows clauses designated sample).2

@[simp] theorem raw_apply
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated)
    (child : Fin (branch n)) :
    raw rows clauses designated sample child = (sample child).2.2 := rfl

end
end PerfectCompleteness.SourceQuestionRawSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourcePhysicalChildExpectation
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_reverse _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalChildExpectation

noncomputable section

open scoped Classical
open RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

def observe (q : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
    Σ flags : SourceProjectedTag.Flags (branch := branch) (n := n),
      CutChildGrouping.Raw (C := C)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows :=
  SourcePhysicalTaggedChildren.observe rows clauses designated
    (SourceQuestionKernelJoint.sources designated q choices) raw

@[simp] theorem observe_flags
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
    (observe rows clauses designated q choices raw).1 =
      fun child => SourceChildKernel.rawProjected rows clauses designated child (raw child) := rfl

end
end PerfectCompleteness.SourcePhysicalChildExpectation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayGroupingTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerReplayGroupingTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls CutSamplerKeyLocality
open scoped Classical

noncomputable section

universe u v

variable {branch : Nat → Nat} {n m t : Nat}

theorem outside_kept (p : Path branch n (m + 1)) (clean : Fin (branch m) → Prop) :
    ∀ s, WholeCutExteriorTransport.Outside p s → keptLeaf p clean s := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro s hs
          exact False.elim (hs ⟨s, rfl⟩)
      | step i p =>
          rintro ⟨j, s⟩ hs
          by_cases hji : j = i
          · subst j
            apply Or.inr
            apply ih p clean s
            rintro ⟨z, hz⟩
            exact hs ⟨z, congrArg (fun a => (i, a)) hz⟩
          · exact Or.inl hji

theorem outside_eq (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s) :
    ∀ s, WholeCutExteriorTransport.Outside p s → slots s = target s :=
  fun s hout => hs s (outside_kept p clean s hout)

theorem retainedChildSlots_eq (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (i : {i : Fin (branch m) // ¬ clean i}) :
    childSlots (WholeCutGrouping.cutSlots p slots) i.val =
      childSlots (WholeCutGrouping.cutSlots p target) i.val := by
  funext s
  exact hs (p.slotEmbedding (i.val, s)) ((keptLeaf_at_cut p clean i.val s).mpr i.property)

def castTerminal (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (terminal : CutSamplerReplayGrouping.RetainedTerminal F2 repeats p (LeafDomain slots) clean) :
    CutSamplerReplayGrouping.RetainedTerminal F2 repeats p (LeafDomain target) clean :=
  fun call child => cast (congrArg
    (fun ss : Slots branch m → Fin t → MixedSupport.Slot => (squareSpace (H ss) : Type))
    (retainedChildSlots_eq p slots target clean hs child)) (terminal call child)

end
end PerfectCompleteness.CutSamplerReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutGroupedProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutGroupedProjection

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def cutProjection (p : Path branch n (m + 1))
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) :
    ∀ s k, MixedSupport.Projection
      (WholeCutGrouping.cutSlots p left s k) (WholeCutGrouping.cutSlots p right s k) :=
  fun s k => q (p.slotEmbedding s) k

def terminalPullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    {left right : Slots branch n → Fin t → MixedSupport.Slot}
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (terminal : CutTerminalSplit.TerminalTape F2 repeats p (LeafDomain right)) :
    CutTerminalSplit.TerminalTape F2 repeats p (LeafDomain left) :=
  fun call child => ChildBlockProjection.squarePullback
    (ChildAssemblyProjection.childProjection (cutProjection p q) child) (terminal call child)

def factorPullback (repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (left right : Slots branch n → Fin t → MixedSupport.Slot) →
      (∀ s k, MixedSupport.Projection (left s k) (right s k)) →
      (j : DrawIndex repeats p) →
      CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain right) j →
        CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain left) j
  | _ + 1, _, .refl _, _, _, q, _, x =>
      fun child => ChildBlockProjection.squarePullback
        (ChildAssemblyProjection.childProjection q child) (x child)
  | _ + 1, _, .step i p, left, right, q, j, x =>
      match j with
      | Sum.inl j =>
          ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val) x
      | Sum.inr j =>
          factorPullback repeats p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i) j.2 x

def tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (tape : CutSamplerRefinement.Tape F2 repeats p (LeafDomain right)) :
    CutSamplerRefinement.Tape F2 repeats p (LeafDomain left) :=
  fun j => factorPullback repeats p left right q j (tape j)

end
end PerfectCompleteness.CutGroupedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.Normalization

open UniqueGamesTheorem.Foundations
open Target
open SourceClause

def gadgetClauses (F : Formula) (c : Fin F.clauses.length) :
    List (Clause (outputVariables F)) :=
  (gadget F c).map NormalizedClause.clause

@[simp] theorem gadgetClauses_length (F : Formula) (c : Fin F.clauses.length) :
    (gadgetClauses F c).length = 13 := by simp [gadgetClauses]

def restrictAssignment (F : Formula) (B : Fin (outputVariables F) → Bool) :
    Fin F.variables → Bool := fun v => B (oldVariable F v)

def extendAssignment (F : Formula) (A : Fin F.variables → Bool)
    (v : Fin (outputVariables F)) : Bool :=
  if old : v.val < F.variables then A ⟨v.val, old⟩
  else
    let c : Fin F.clauses.length := ⟨(v.val - F.variables) / 4, by
      have hv := v.isLt
      unfold outputVariables at hv
      omega⟩
    if slot : (v.val - F.variables) % 4 < 3 then
      A (PCP.clauseAt F c)[(⟨(v.val - F.variables) % 4, slot⟩ : Fin 3)].variableIndex
    else false

@[simp] theorem extend_oldVariable (F : Formula) (A : Fin F.variables → Bool)
    (v : Fin F.variables) : extendAssignment F A (oldVariable F v) = A v := by
  simp [extendAssignment, oldVariable, v.isLt]

@[simp] theorem extend_copyVariable (F : Formula) (A : Fin F.variables → Bool)
    (c : Fin F.clauses.length) (i : Fin 3) :
    extendAssignment F A (copyVariable F c i) = A (PCP.clauseAt F c)[i].variableIndex := by
  have hi := i.isLt
  have hold : ¬ F.variables + 4 * c.val + i.val < F.variables := by omega
  have hdiv : (F.variables + 4 * c.val + i.val - F.variables) / 4 = c.val := by omega
  have hmod : (F.variables + 4 * c.val + i.val - F.variables) % 4 = i.val := by omega
  simp [extendAssignment, copyVariable, freshVariable, hold, hdiv, hmod, hi]

@[simp] theorem restrict_extend (F : Formula) (A : Fin F.variables → Bool) :
    restrictAssignment F (extendAssignment F A) = A := by
  funext v
  exact extend_oldVariable F A v

def normalizedClauses (F : Formula) : List (NormalizedClause (outputVariables F)) :=
  (PCP.allIndices F).flatMap (gadget F)

def normalize (F : Formula) : Formula where
  «variables» := outputVariables F
  clauses := (PCP.allIndices F).flatMap (gadgetClauses F)

theorem normalize_clauses_eq_map (F : Formula) :
    (normalize F).clauses = (normalizedClauses F).map NormalizedClause.clause := by
  simp only [normalize, normalizedClauses, List.map_flatMap]
  rfl

theorem normalize_distinct (F : Formula) (c : Clause (normalize F).variables)
    (hc : c ∈ (normalize F).clauses) (i j : Fin 3)
    (same : (c)[i].variableIndex = (c)[j].variableIndex) : i = j := by
  rw [normalize_clauses_eq_map] at hc
  obtain ⟨d, _, hd⟩ := List.mem_map.mp hc
  subst c
  exact d.distinct i j same

@[simp] theorem normalize_variables (F : Formula) :
    (normalize F).variables = F.variables + 4 * F.clauses.length := rfl

@[simp] theorem normalize_clause_count (F : Formula) :
    (normalize F).clauses.length = 13 * F.clauses.length := by
  change ((PCP.allIndices F).flatMap (gadgetClauses F)).length = _
  rw [PCP.VerifierToCNF.length_flatMap_constant _ _ 13
    (fun c _ => gadgetClauses_length F c)]
  simp [PCP.allIndices, Nat.mul_comm]

theorem normalize_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    (normalize F).clauses ≠ [] := by
  have hm : 0 < F.clauses.length := List.length_pos_iff.mpr hne
  have hout : 0 < (normalize F).clauses.length := by
    rw [normalize_clause_count]
    omega
  exact List.ne_nil_of_length_pos hout

end PerfectCompleteness.Normalization



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev FamilyState := MachineExpanderFamily.State Unit MachinePaddedExpanderFamily.fixedDegree

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

def scratch : Tape := .inr 1

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Top

abbrev Body := MachineRegularOriginalBody.Tape

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

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

def rawFormula (F : Formula) : Formula := TableIteration.gapMap baseTable F

def normalizedFormula (F : Formula) : Formula := Normalization.normalize (rawFormula F)

theorem rawFormula_nonempty (F : Formula) : (rawFormula F).clauses ≠ [] :=
  TableIteration.gapMap_nonempty baseTable F

theorem normalizedFormula_nonempty (F : Formula) : (normalizedFormula F).clauses ≠ [] :=
  Normalization.normalize_nonempty (rawFormula F) (rawFormula_nonempty F)

theorem normalizedFormula_distinct (F : Formula)
    (c : Clause (normalizedFormula F).variables) (hc : c ∈ (normalizedFormula F).clauses)
    (i j : Fin 3) (same : (c)[i].variableIndex = (c)[j].variableIndex) : i = j :=
  Normalization.normalize_distinct (rawFormula F) c hc i j same

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

def rawSource (input : List Bool) : Formula :=
  PCPSource.normalizedFormula (BinaryLanguage.totalRename input)

end
end PerfectCompleteness.PCPSourceMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedRows

open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

variable {δ : ℚ} (plan : Plan δ)

def repeats : Nat → Nat := fun height => plan.repeatCount (rows plan height)

end
end PerfectCompleteness.FixedRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

abbrev RawSample (repeats : Nat → Nat) (cut : Cut upper lower) :=
  HiddenBucketBias.HiddenTape W (ScalarSample slots upper lower repeats cut) ×
    (HiddenBucketBias.VisibleTape W (ScalarSample slots upper lower repeats cut) ×
      Exterior slots rows upper lower)

end
end PerfectCompleteness.OwnInputReference



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_WholeArrayInteriorOwnInputLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
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

abbrev fullPath (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower) :=
  (Nodes.path upper).append cut.path

def readExterior (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputReference.Exterior slots rows upper lower where
  otherArrays node := WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω node.val
  lowerRows := WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω lower

def exposedRead (rows repeats : Nat → Nat)
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
    (W : Submodule F2 (Block rows upper))
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputReference.RawSample slots rows upper lower W repeats cut :=
  let parts := WholeArrayPositiveSplit.split rows repeats (Nodes.path upper) cut.path cut.proper slots W ω
  (parts.1, (parts.2.1, readExterior rows repeats slots upper lower cut ω))

end
end PerfectCompleteness.WholeArrayInteriorOwnInputLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeReplaySubtreeLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutSubtree

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit

variable {branch : Nat → Nat} {n k m t : Nat}

def rootBuckets (rows repeats : Nat → Nat) :
    {k m : Nat} → (pDown : Path branch k m) → m < k →
      (slots : Slots branch k → Fin t → MixedSupport.Slot) →
      WholeCutSampler.Tape rows repeats pDown slots →
        BucketSampler.Direction (rows k) → H slots
  | _, _, .refl _, hproper, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step i pDown, _, slots, tape, bucket =>
      CutSamplerRefinement.evaluate F2 repeats (.step i pDown) (LeafDomain slots)
        (tape.1 bucket)

def knownBuckets (rows repeats : Nat → Nat)
    (pUp : Path branch n k) (pDown : Path branch k m) (hproper : m < k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows k) → F2))
    (tape : WholeCutSampler.Tape rows repeats (pUp.append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → H (subtreeSlots pUp slots) :=
  fun v => rootBuckets rows repeats pDown hproper (subtreeSlots pUp slots)
    (extract rows repeats pUp pDown slots tape) v.val

def knownBucketsAtNode (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) m) (hproper : m < Nodes.height upper)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
    (tape : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown) slots) :
    HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper :=
  knownBuckets rows repeats (Nodes.path upper) pDown hproper slots W tape

end
end PerfectCompleteness.WholeCutSubtree

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanRecordChildBlocks
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanRecordChildBlocks

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {h t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

theorem extract_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    extract rows clauses designated record i = x i.val := by
  have obs := CleanSourceRecord.observation_eq designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x hevent i.val
  cases hc : UniformCleanSources.childClean
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      i.val (x i.val).1 (x i.val).2.1 (x i.val).2.2 with
  | false =>
      have hr : record i.val = .inl (x i.val) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false, if_false]
          using obs.symm
      exact Sum.inl.inj ((record_extract rows clauses designated record i).symm.trans hr)
  | true =>
      have hr : record i.val = .inr (x i.val).2.1 := by
        simpa only [SelectedSources.childObservation, hc, ite_true, if_true] using obs.symm
      exact False.elim (i.property (by
        simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord]))

variable [NeZero m]

theorem leftRef_childSlots_event (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    childSlots (leftRef rows clauses designated record) i.val =
      childSlots (SourceChildKernel.parentLeftSlots clauses designated
        (fun j => ((x j).1, (x j).2.1))) i.val :=
  (leftRef_childSlots rows clauses designated record i).trans
    (congrArg (fun y : Row (C := C) (t := t) rows clauses designated i.val =>
      SourceChildKernel.nativeSlots clauses designated i.val (y.1, y.2.1))
      (extract_eq rows clauses designated record x hevent i))

theorem rightRef_childSlots_event (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    childSlots (rightRef rows clauses designated record) i.val =
      childSlots (SourceChildKernel.parentRightSlots rows clauses designated
        (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2)) i.val :=
  (rightRef_childSlots rows clauses designated record i).trans
    (congrArg (fun y : Row (C := C) (t := t) rows clauses designated i.val =>
      SourceChildKernel.mixedSlots clauses designated i.val (y.1, y.2.1)
        (SourceChildKernel.rawProjected rows clauses designated i.val y.2.2))
      (extract_eq rows clauses designated record x hevent i))

end
end PerfectCompleteness.CleanRecordChildBlocks

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalReplay

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)

section Source

variable {v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

theorem leftInside_nonclean (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : ¬ CleanRecordChildBlocks.clean rows clauses designated record i)
    (s : Slots branch h) :
    CleanRecordChildBlocks.leftRef rows clauses designated record (i, s) =
      leftInside rows repeats p clauses designated x (i, s) :=
  congrFun (CleanRecordChildBlocks.leftRef_childSlots_event
    rows clauses designated record x hevent ⟨i, hi⟩) s

theorem rightInside_nonclean (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : ¬ CleanRecordChildBlocks.clean rows clauses designated record i)
    (s : Slots branch h) :
    CleanRecordChildBlocks.rightRef rows clauses designated record (i, s) =
      rightInside rows repeats p clauses designated x (i, s) :=
  congrFun (CleanRecordChildBlocks.rightRef_childSlots_event
    rows clauses designated record x hevent ⟨i, hi⟩) s

end Source

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

local instance rowSpaceFintype_r6b32eb_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_r6b32eb_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype_r6b32eb_1 :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
local instance adviceFintype_r6b32eb_1 (r : Nat) :
    Fintype (Advice slots upper lowerLevel background r) := by
  letI : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background)) :=
    LeftDecoder.dualFintype
  infer_instance
abbrev Answer (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  Module.Dual F2 (squareSpace (LowerH slots upper lowerLevel d))

local instance answerFintype_r6b32eb_1 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype (V := squareSpace (LowerH slots upper lowerLevel d))
def fullRank (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (z : Answer slots upper lowerLevel d) : Nat :=
  OddListExtraction.formRank (LowerH slots upper lowerLevel d)
    (OddListExtraction.multiplicationForm (LowerH slots upper lowerLevel d) z)

end
end PerfectCompleteness.HierarchicalDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalAllDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (background : Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

local instance rowSpaceFintype_r6b32eb_2 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_r6b32eb_2 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAllDecoderTables.upperDualFintype
local instance answerFintype_r6b32eb_2 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype
    (V := squareSpace (HierarchicalDecoderTables.LowerH slots upper lowerLevel d))
def upperKernel (r : Nat) (ρ : ℝ) (input : Input (rows := rows) slots upper lowerLevel r) :
    FiniteDistribution (UpperAnswer slots upper) :=
  HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel input.1 σ (useful input.1)
    r ρ input.2.1 input.2.2

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LowerCutDecoderInput
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutDecoderInput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

def actualInput {r : Nat} (arrays : Arrays slots rows)
    (A : ManyGoodRows.RowMap (Block rows upper) r) :
    HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r :=
  ⟨HierarchicalMatrixTable.backgroundOf slots upper arrays,
    (A, A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays))
      (NodeEmbedding.matrix arrays upper)))⟩

end
end PerfectCompleteness.LowerCutDecoderInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutNodeCoordinates
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
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

def scalarEquiv : {n m : Nat} → (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      H (subtreeSlots p slots) ≃ₗ[F2] H (nodeSlots slots (upperNode p))
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => scalarEquiv p (childSlots slots i)

def rowIndexEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
      Fin (rows (m + 1)) ≃ Fin (rows (Nodes.height (upperNode p)))
  | _, _, .refl _ => Equiv.refl _
  | _, _, .step _ p => rowIndexEquiv rows p

def directionEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
      BucketSampler.Direction (rows (m + 1)) ≃
        BucketSampler.Direction (rows (Nodes.height (upperNode p)))
  | _, _, .refl _ => Equiv.refl _
  | _, _, .step _ p => directionEquiv rows p

end
end PerfectCompleteness.LowerCutNodeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def reconstruct (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) : Arrays slots rows :=
  WholeCutSampler.evaluate rows repeats p slots
    ((splitTape rows repeats p slots).symm (exterior, raw))

end
end PerfectCompleteness.LowerCutRows

end

section

namespace PerfectCompleteness.LowerCutCallSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

@[simp] theorem selectRows_merge (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    LowerCutRows.selectRows rows repeats p slots (merge rows repeats p slots bg fresh) = fresh :=
  congrArg Prod.snd (split_merge rows repeats p slots bg fresh)

end
end PerfectCompleteness.LowerCutCallSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev Calls := WholeCutCalls.Index rows repeats p
abbrev Raw := CutCallExtension.Extended (C := Calls rows repeats p) (cutSlots p slots) rows
abbrev NativeRows := Fin (rows (m + 1)) → H (cutSlots p slots)

def first (exterior : Exterior rows repeats p slots) (raw : Raw rows repeats p slots) :
    Arrays slots rows :=
  LowerCutRows.reconstruct rows repeats p slots exterior
    (CutCallExtension.original (cutSlots p slots) rows raw)

def fresh (raw : Raw rows repeats p slots) : H (cutSlots p slots) :=
  CutCallExtension.fresh (cutSlots p slots) rows raw

def second (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    Arrays slots rows :=
  SelectedArrayReplacement.replace rows p slots (first rows repeats p slots exterior raw)
    (LowerDirectionFiber.replace a
      (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw))
      (fresh rows repeats p slots raw))

@[simp] theorem selected_second (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots) :
    SelectedArrayReplacement.selectedRows rows p slots (second rows repeats p slots exterior a raw) =
      LowerDirectionFiber.replace a
        (SelectedArrayReplacement.selectedRows rows p slots (first rows repeats p slots exterior raw))
        (fresh rows repeats p slots raw) :=
  SelectedArrayReplacement.selectedRows_replace rows p slots _ _

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

def spaceEquiv : H (cutSlots path slots) ≃ₗ[ZMod 2]
    HierarchicalDecoderTables.LowerH slots upper lowerLevel d :=
  (LowerCutNodeCoordinates.scalarEquiv path slots).trans (by
    rw [hnode])

def form (answer : HierarchicalDecoderTables.Answer slots upper lowerLevel d) :
    ChildBilinearCollisionTransfer.ParentForm (cutSlots path slots) where
  toFun f := (OddListExtraction.multiplicationForm
    (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) answer
      (spaceEquiv path slots upper lowerLevel d hnode f)).comp
        (spaceEquiv path slots upper lowerLevel d hnode).toLinearMap
  map_add' f g := by
    ext h
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' c f := by
    ext h
    simp only [LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem form_apply
    (answer : HierarchicalDecoderTables.Answer slots upper lowerLevel d)
    (f g : H (cutSlots path slots)) :
    form path slots upper lowerLevel d hnode answer f g =
      OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) answer
        (spaceEquiv path slots upper lowerLevel d hnode f)
        (spaceEquiv path slots upper lowerLevel d hnode g) := rfl

end
end PerfectCompleteness.LowerCutDecoderForm

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LowerCutOwnInput
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutOwnInput

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior
open scoped Classical TensorProduct

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : Slots branch n → Fin t → MixedSupport.Slot) (rows : Nat → Nat)
  (upper lower : Nodes branch n)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))

def ofArrays (a : Block rows lower)
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (arrays : Arrays slots rows) : OwnInputReference.Input slots rows upper lower W a :=
  OwnInputReference.readInput slots rows upper lower W a id
    (known, OwnInputCanonicalQuery.exteriorOf slots rows upper lower arrays)

end
end PerfectCompleteness.LowerCutOwnInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedLowerFiber
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
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

abbrev lower := HierarchicalLeftDecoder.LowerNode upper level d
abbrev Scalar := H (nodeSlots projected (lower upper level d))
abbrev Direction := BucketSampler.Direction (rows (Nodes.height (lower upper level d)))

end
end PerfectCompleteness.ProjectedLowerFiber

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedFiberSquare
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

local instance rowSpaceFintype_r6b32eb_3 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r6b32eb_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def highMeeting (s : Nat)
    (q : HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper)) : Bool :=
  decide (s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q) ∧
    DecoderSourcePullback.upperTarget projection upper q = right)

end
end PerfectCompleteness.ProjectedFiberSquare

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderFamilyLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DecoderFamilyLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {O : Type*} [Fintype O]
  {upper : O → Nodes branch n}
  {lower : (o : O) → HierarchicalFrozenTables.LowerNodes (upper o) (h + 1)}
  (S : (o : O) → CleanDecoderRate.Setup branch rows repeats n h t v m (upper o) (lower o))

abbrev Fiber (o : O) :=
  Σ x : CleanDecoderRate.Sample (S o), CleanDecoderPairLaw.Pair (S o) x

abbrev Sample := Σ o : O, Fiber S o

def meeting (z : Sample S) : Bool :=
  DecoderRankSplit.meeting (S z.1) z.2.1 z.2.2

variable (hbranch : ∀ k < n, 0 < branch k)

def lowAgreement (s : Nat) (z : Sample S) : Bool :=
  CleanDecoderPairLaw.pairAgrees (S z.1) hbranch s z.2.1 z.2.2

def highAgreement (s : Nat) (z : Sample S) : Bool :=
  DecoderRankSplit.highAgrees (S z.1) hbranch s z.2.1 z.2.2

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (o : O) → (record : CleanDecoderRate.Record (S o)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (S o) record))
      (upper o) (h + 1))
  (r : Nat) (ρ : ℝ)
  (A : (o : O) → ManyGoodRows.RowMap (Block rows (upper o)) r)
  (a : (o : O) → OwnInputReference.LowerVector rows
    (HierarchicalLeftDecoder.LowerNode (upper o) (h + 1) (lower o)))
  (threshold : ℝ)

def fiberLaw (cube : Nat) (hcube : 0 < cube) (o : O) :
    FiniteDistribution (Fiber S o) :=
  CleanDecoderPairLaw.pairLaw (S o) σ (useful o) r ρ (A o)
    (LinearMap.ker (A o)) (a o) threshold cube hcube

def law (outer : FiniteDistribution O) (cube : Nat) (hcube : 0 < cube) :
    FiniteDistribution (Sample S) :=
  CompletionSoundness.sigmaLaw outer
    (fiberLaw S σ useful r ρ A a threshold cube hcube)

end
end PerfectCompleteness.DecoderFamilyLaw

end

section

namespace PerfectCompleteness.DecoderPairHighOutput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev exposed (x : CleanDecoderRate.Sample S) :=
  CleanDecoderContext.leftExposed (CleanDecoderPairLaw.context S x)

abbrev slots (x : CleanDecoderRate.Sample S) :=
  CleanLeftDecoder.slots (exposed S x) (CleanDecoderPairLaw.leftOwn S x)

abbrev Answer (x : CleanDecoderRate.Sample S) :=
  HierarchicalDecoderTables.Answer (slots S x) upper (h + 1) d

variable (hbranch : ∀ k < n, 0 < branch k)

abbrev output (x : CleanDecoderRate.Sample S) (q : CleanDecoderPairLaw.LeftAnswer S x) :
    Answer S x :=
  CleanLeftDecoder.output (exposed S x) upper (h + 1) hbranch d
    (CleanDecoderPairLaw.leftOwn S x) q

end
end PerfectCompleteness.DecoderPairHighOutput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev Complement := LowerCutCallSplit.Complement rows repeats p slots
abbrev NativeRows := LowerCutPair.NativeRows rows p slots

abbrev Observation := Complement rows repeats p slots ×
  (NativeRows rows p slots × H (cutSlots p slots))

def splitObservation :
    (CutChildGrouping.Assembled (C := LowerCutPair.Calls rows repeats p)
      (cutSlots p slots) rows × H (cutSlots p slots)) →ₗ[F2]
      Observation rows repeats p slots where
  toFun z :=
    ((LowerCutCallSplit.splitAssembled rows repeats p slots z.1).1,
      ((LowerCutCallSplit.splitAssembled rows repeats p slots z.1).2, z.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def observe (raw : LowerCutPair.Raw rows repeats p slots) :
    Observation rows repeats p slots :=
  splitObservation rows repeats p slots (CutCallExtension.observe (cutSlots p slots) rows raw)

@[simp] theorem observe_fresh (raw : LowerCutPair.Raw rows repeats p slots) :
    (observe rows repeats p slots raw).2.2 = LowerCutPair.fresh rows repeats p slots raw := rfl

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

end
end PerfectCompleteness.LowerCutPairBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutFiberDisintegrationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev Scalar := H (cutSlots path slots)
abbrev Quotient := LowerDirectionFiber.Complement a (Scalar path slots)
abbrev Background := LowerCutPairBackground.Complement rows repeats path slots ×
  Quotient rows path slots a
abbrev Coordinates := Background rows repeats path slots a ×
  (Scalar path slots × Scalar path slots)

def coordinateEquiv : LowerCutPairBackground.Observation rows repeats path slots ≃
    Coordinates rows repeats path slots a where
  toFun z := ((z.1, LowerDirectionFiber.complement a z.2.1),
    (z.2.1 (LowerDirectionFiber.pivot a), z.2.2))
  invFun z := (z.1.1, (LowerDirectionFiber.restore a z.1.2 z.2.1, z.2.2))
  left_inv z := by
    change (z.1, (LowerDirectionFiber.restore a
      (LowerDirectionFiber.complement a z.2.1) (z.2.1 (LowerDirectionFiber.pivot a)),
      z.2.2)) = z
    exact Prod.ext rfl (Prod.ext (LowerDirectionFiber.restore_complement a z.2.1) rfl)
  right_inv z := by
    apply Prod.ext
    · exact Prod.ext rfl (LowerDirectionFiber.complement_restore a z.1.2 z.2.1)
    · exact Prod.ext (LowerDirectionFiber.restore_pivot a z.1.2 z.2.1) rfl

@[simp] theorem coordinateEquiv_apply (z : LowerCutPairBackground.Observation rows repeats path slots) :
    coordinateEquiv rows repeats path slots a z =
      ((z.1, LowerDirectionFiber.complement a z.2.1),
        (z.2.1 (LowerDirectionFiber.pivot a), z.2.2)) := rfl

end
end PerfectCompleteness.LowerCutFiberDisintegration

end

section

namespace PerfectCompleteness.LowerCutSingleFiberDisintegration

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (a : BucketSampler.Direction (rows (m + 1)))

abbrev Raw := CutChildGrouping.Raw (C := LowerCutPair.Calls rows repeats path)
  (cutSlots path slots) rows

abbrev Coordinates := LowerCutFiberDisintegration.Background rows repeats path slots a ×
  H (cutSlots path slots)

def coordinateEquiv :
    (LowerCutCallSplit.Complement rows repeats path slots ×
      LowerCutCallSplit.NativeRows rows path slots) ≃
        Coordinates rows repeats path slots a where
  toFun z := ((z.1, LowerDirectionFiber.complement a z.2),
    z.2 (LowerDirectionFiber.pivot a))
  invFun z := (z.1.1, LowerDirectionFiber.restore a z.1.2 z.2)
  left_inv z := Prod.ext rfl (LowerDirectionFiber.restore_complement a z.2)
  right_inv z := Prod.ext
    (Prod.ext rfl (LowerDirectionFiber.complement_restore a z.1.2 z.2))
    (LowerDirectionFiber.restore_pivot a z.1.2 z.2)

@[simp] theorem coordinateEquiv_apply
    (z : LowerCutCallSplit.Complement rows repeats path slots ×
      LowerCutCallSplit.NativeRows rows path slots) :
    coordinateEquiv rows repeats path slots a z =
      ((z.1, LowerDirectionFiber.complement a z.2),
        z.2 (LowerDirectionFiber.pivot a)) := rfl

def coordinates (raw : Raw rows repeats path slots) :
    Coordinates rows repeats path slots a :=
  coordinateEquiv rows repeats path slots a
    (LowerCutCallSplit.splitAssembled rows repeats path slots
      (CutChildGrouping.assemble (cutSlots path slots) rows raw))

@[simp] theorem coordinates_complement (raw : Raw rows repeats path slots) :
    (coordinates rows repeats path slots a raw).1.1 =
      LowerCutCallSplit.complement rows repeats path slots
        (CutChildGrouping.assemble (cutSlots path slots) rows raw) := rfl

end
end PerfectCompleteness.LowerCutSingleFiberDisintegration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedFiberRawPair
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberRawPair

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior

variable {branch rows repeats : Nat → Nat} {n m t : Nat}

def castDirection {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node))) :
    BucketSampler.Direction (rows (Nodes.height node')) := by
  cases h
  exact a

def castScalar (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (x : H (nodeSlots projected node)) : H (nodeSlots projected node') := by
  cases h
  exact x

variable (path : Path branch n (m + 1))
  (projected : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : upperNode path = HierarchicalLeftDecoder.LowerNode upper level d)

def direction (a : BucketSampler.Direction (rows (m + 1))) :
    ProjectedLowerFiber.Direction (rows := rows) upper level d :=
  castDirection hnode (LowerCutNodeCoordinates.directionEquiv rows path a)

def scalar (x : H (WholeCutGrouping.cutSlots path projected)) :
    ProjectedLowerFiber.Scalar projected upper level d :=
  castScalar projected hnode (LowerCutNodeCoordinates.scalarEquiv path projected x)

end
end PerfectCompleteness.ProjectedFiberRawPair

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedFiberBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberBackground

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}

def nodeScalarEquiv
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node') :
    H (nodeSlots projected node) ≃ₗ[F2] H (nodeSlots projected node') := by
  cases h
  exact LinearEquiv.refl F2 _

@[simp] theorem nodeScalarEquiv_apply
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (x : H (nodeSlots projected node)) :
    nodeScalarEquiv projected h x = ProjectedFiberRawPair.castScalar projected h x := by
  cases h
  rfl

variable (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  (projected : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : upperNode path = HierarchicalLeftDecoder.LowerNode upper level d)

def scalarEquiv : H (WholeCutGrouping.cutSlots path projected) ≃ₗ[F2]
    ProjectedLowerFiber.Scalar projected upper level d :=
  (LowerCutNodeCoordinates.scalarEquiv path projected).trans
    (nodeScalarEquiv projected hnode)

@[simp] theorem scalarEquiv_apply (x : H (WholeCutGrouping.cutSlots path projected)) :
    scalarEquiv path projected upper level d hnode x =
      ProjectedFiberRawPair.scalar path projected upper level d hnode x := by
  exact nodeScalarEquiv_apply projected hnode
    (LowerCutNodeCoordinates.scalarEquiv path projected x)

end
end PerfectCompleteness.ProjectedFiberBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerProjectedOriginalSuccessLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
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

local instance rowSpaceFintype_r6b32eb_4 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r6b32eb_2 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
def kernelSuccess (s : Nat)
    (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)
    (arrays : Arrays projected rows) : ℝ :=
  ((HierarchicalAllDecoderTables.upperKernel slots upper level σ useful r ρ
    (LowerCutDecoderInput.actualInput slots upper level
      (ChildBlockProjection.arraysPullback rows projection arrays) A)).product
    (RightDecoder.law projected rows upper (ProjectedLowerFiber.lower upper level d)
      (LinearMap.ker A) (ProjectedFiberRawPair.direction path upper level d hnode a).val
      repeats cut σ
      (LowerCutOwnInput.ofArrays projected rows upper (ProjectedLowerFiber.lower upper level d)
        (LinearMap.ker A) (ProjectedFiberRawPair.direction path upper level d hnode a).val
        known arrays) threshold)).probability
      (fun pair => ProjectedFiberSquare.highMeeting slots projected projection upper level hbranch d
        s pair.1 pair.2)

end
end PerfectCompleteness.LowerProjectedOriginalSuccess

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
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

abbrev Values (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalCutCalls.Index rows repeats p → H (cutSlots p slots)

abbrev ChildArrays (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :=
  (child : Fin (branch m)) → Arrays (childSlots slots child) rows

abbrev BelowArrays (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  ChildArrays rows (cutSlots p slots)

end
end PerfectCompleteness.OriginalWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalWholeCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

@[instance_reducible] def valuesBelowFintype (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (OriginalWholeCut.Values rows repeats p slots ×
      OriginalWholeCut.BelowArrays rows p slots) :=
  @instFintypeProd (OriginalWholeCut.Values rows repeats p slots)
    (OriginalWholeCut.BelowArrays rows p slots) inferInstance inferInstance

attribute [local instance 2000] valuesBelowFintype

end
end PerfectCompleteness.OriginalWholeCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutContinuationAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutContinuationAveraging

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def originalArrayLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) : FiniteDistribution (Arrays slots rows) :=
  (GeometricPath.law (m + 1) hbranch).mixture (fun leaf =>
    WholeArraySampler.law rows repeats (p.append (GeometricPath.leafPath leaf)) slots)

end
end PerfectCompleteness.CutContinuationAveraging

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutNativeForms
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutNativeForms

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces

variable {branch : Nat → Nat} {n k t : Nat}

section Equality

variable {a b c d : Slots branch k → Fin t → MixedSupport.Slot}

def spaceCast (hab : a = b) : H a ≃ₗ[F2] H b := by
  cases hab
  exact LinearEquiv.refl F2 (H a)

def formCast (hab : a = b) (F : SourceLocalOddLists.Form a) : SourceLocalOddLists.Form b := by
  cases hab
  exact F

@[simp] theorem formCast_apply (hab : a = b) (F : SourceLocalOddLists.Form a)
    (f g : H a) : formCast hab F (spaceCast hab f) (spaceCast hab g) = F f g := by
  cases hab
  rfl

def projectionCast (hab : a = b) (hcd : c = d)
    (p : ∀ s j, MixedSupport.Projection (a s j) (c s j)) :
    ∀ s j, MixedSupport.Projection (b s j) (d s j) := by
  cases hab
  cases hcd
  exact p

end Equality

end
end PerfectCompleteness.CutNativeForms

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype
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

abbrev VisibleSample (repeats : Nat → Nat) (cut : Cut upper lower) :=
  HiddenBucketBias.VisibleTape W (ScalarSample slots upper lower repeats cut) ×
    Exterior slots rows upper lower

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

def exteriorBackground (external : OwnInputReference.Exterior slots rows upper lower) :
    HierarchicalMatrixTable.Background (rows := rows) slots upper :=
  HierarchicalMatrixTable.backgroundOf slots upper
    (OwnInputCanonicalQuery.assemble slots rows upper lower 0 external)

variable (W : Submodule F2 (UpperVector rows upper))
  (repeats : Nat → Nat) (cut : Cut upper lower)

def knownVisible (visible : OwnInputAffineSlice.VisibleSample slots rows upper lower W repeats cut) :
    HiddenBucketBias.VisibleDirection W → UpperSpace slots upper :=
  fun v => scalarEval slots upper lower repeats cut (visible.1 v)

end
end PerfectCompleteness.OwnInputRawAssembly

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
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

local instance rowSpaceFintype_r6b32eb_5 : Fintype (NodeEmbedding.RowSpace originalSlots upper) :=
  Fintype.ofFinite _
local instance valueFintype_r6b32eb_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
abbrev visibleMatrix := HierarchicalTensorMatrix.visibleMatrix originalSlots upper (LinearMap.ker A)
  (fun v => ProjectedNodeEmbedding.nativePullback projection upper (known v))

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.HierarchicalProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalProjectedSlice
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projected upper)

local instance rowSpaceFintype_r6b32eb_6 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance valueFintype_r6b32eb_2 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedMeeting.upperDualFintype
def useful (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) : Prop :=
  HierarchicalUsefulness.mark slots upper lowerLevel original arrays lowerEvent κ
    ⟨background, X⟩ = true

def leftLaw : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel background σ
    (useful slots upper lowerLevel background original arrays lowerEvent κ) r ρ A
    (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (visibleMatrix slots projected projection upper A known)))

end
end PerfectCompleteness.HierarchicalProjectedMeeting


namespace PerfectCompleteness.ProjectedRawAssembly

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (originalSlots s k) (projectedSlots s k))
  (rows : Nat → Nat) (upper lower : Nodes branch n)

def exteriorBackground
    (external : OwnInputReference.Exterior projectedSlots rows upper lower) :
    HierarchicalMatrixTable.Background (rows := rows) originalSlots upper :=
  fun node row => ProjectedNodeEmbedding.nativePullback projection node.val
    (OwnInputRawAssembly.exteriorBackground projectedSlots rows upper lower external node row)

variable (W : Submodule F2 (Block rows upper))
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

def background
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.Background (rows := rows) originalSlots upper :=
  exteriorBackground originalSlots projectedSlots projection rows upper lower visible.2

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

local instance rowSpaceFintype_r6b32eb_7 : Fintype (NodeEmbedding.RowSpace originalSlots upper) :=
  Fintype.ofFinite _
local instance valueFintype_r6b32eb_3 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
abbrev Visible := OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower (LinearMap.ker A) repeats cut

abbrev visibleBackground (v : Visible projectedSlots rows upper lower A repeats cut) :=
  ProjectedRawAssembly.background originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut v

abbrev known (v : Visible projectedSlots rows upper lower A repeats cut) :=
  OwnInputRawAssembly.knownVisible projectedSlots rows upper lower (LinearMap.ker A) repeats cut v

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PCPSourceHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PCPSourceHardness

open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

def formula {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) : Formula :=
  PCPSource.normalizedFormula (source.reduce input)

end
end PerfectCompleteness.PCPSourceHardness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseReaderMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def steps {n : Nat} (clause : Target.Clause n) : Nat :=
  clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 7

section Placement

variable {K Λ A : Type} [DecidableEq K]

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (save : A → CanonicalKeyShape.Shape → A)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ label, program (labels label) = instruction tape labels done rejected save label)
variable (base : K → List Bool) (ambient : A)

include atLabels in
theorem publishStep (signs : Signs) (register : Option Bool) (tapeValues : K → List Bool) :
    TM2.step program ⟨some (labels .publish), ((ambient, signs), register), tapeValues⟩ =
      some ⟨done, clean (save ambient (shape signs)) signs, tapeValues⟩ := by
  change some (TM2.stepAux (program (labels .publish)) _ _) = _
  rw [atLabels .publish]
  cases done <;> rfl

include distinct atLabels

theorem readTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (signs : Signs) (register : Option Bool) :
    (advance (TM2.step program))^[steps clause]
      (some ⟨some (labels main), ((ambient, signs), register),
        NormalizationReadMachine.tapes tape base
          (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩) =
      some ⟨done, clean (save ambient (clauseShape clause))
        (NormalizationReadMachine.clauseSigns clause),
        NormalizationReadMachine.tapes tape base suffix
          (NormalizationReadMachine.clauseCounters clause)⟩ := by
  have first := NormalizationReadMachine.clauseTrace tape distinct
    (fun label => labels (.read label)) (some (labels .publish)) rejected program
    (fun label => atLabels (.read label)) base ambient clause suffix signs register
  have second := publishStep tape labels done rejected save program atLabels ambient
    (NormalizationReadMachine.clauseSigns clause) none
    (NormalizationReadMachine.tapes tape base suffix
      (NormalizationReadMachine.clauseCounters clause))
  rw [show steps clause =
      (clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val + 6) + 1 by
        unfold steps
        omega,
    Function.iterate_succ_apply']
  change advance (TM2.step program)
    ((advance (TM2.step program))^[clause[0].variableIndex.val +
      clause[1].variableIndex.val + clause[2].variableIndex.val + 6]
      (some ⟨some (labels (.read (.field 0))), ((ambient, signs), register),
        NormalizationReadMachine.tapes tape base
          (encodeWords (clauseWords clause) ++ suffix) (fun _ => [])⟩)) = _
  rw [first, advance_some]
  exact second

end Placement

theorem steps_le_encoded_length {n : Nat} (clause : Target.Clause n) :
    steps clause ≤ (encodeWords (clauseWords clause)).length + 1 := by
  have bound := NormalizationReadMachine.steps_le_encoded_length clause
  unfold steps
  omega

end PerfectCompleteness.SourceClauseReaderMachine


namespace PerfectCompleteness.SourceOccurrenceEncoding

open UniqueGamesTheorem.Foundations Complexity Target

def recordBits {n : Nat} (index : Nat) (clause : Clause n) : List Bool :=
  encodeWords (recordWords index clause)

theorem body_cons {n : Nat} (first : Nat) (clause : Clause n) (clauses : List (Clause n)) :
    body first (clause :: clauses) = recordBits first clause ++ body (first + 1) clauses := by
  exact encodeWords_append _ _

theorem recordBits_eq {n : Nat} (index : Nat) (clause : Clause n) :
    recordBits index clause = encodeWord index ++ encodeWords (clauseWords clause) := rfl

end PerfectCompleteness.SourceOccurrenceEncoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseSelectMachine
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseSelectMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def steps {n : Nat} (first : Nat) : List (Target.Clause n) → Nat → Nat
  | [], _ => 0
  | clause :: _, 0 => 1 + (SourceOccurrenceEncoding.recordBits first clause).length
  | clause :: clauses, offset + 1 =>
      1 + (SourceOccurrenceEncoding.recordBits first clause).length + steps (first + 1) clauses offset

theorem steps_le {n : Nat} (clauses : List (Target.Clause n)) (first offset : Nat)
    (bound : offset < clauses.length) :
    steps first clauses offset ≤ (SourceOccurrenceEncoding.body first clauses).length + offset + 1 := by
  induction offset generalizing clauses first with
  | zero =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          simp only [steps, SourceOccurrenceEncoding.body_cons, List.length_append]
          omega
  | succ offset ih =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          have tail := ih clauses (first + 1) (by
            simp only [List.length_cons] at bound
            omega)
          simp only [steps, SourceOccurrenceEncoding.body_cons, List.length_append]
          omega

section Program

variable {K Λ A : Type} [DecidableEq K]

variable (tape : Fin 3 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem skipTrace {n : Nat} (first : Nat) (clause : Target.Clause n)
    (suffix : List Bool) (offset : Nat) (output : List Bool) :
    (advance (TM2.step program))^[1 + (SourceOccurrenceEncoding.recordBits first clause).length]
      (some ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.recordBits first clause ++ suffix)
          (offset + 1) output⟩) =
      some ⟨some (labels .guard), clean ambient, selectTapes tape base suffix offset output⟩ := by
  let input := SourceOccurrenceEncoding.recordBits first clause ++ suffix
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), clean ambient, selectTapes tape base input (offset + 1) output⟩) =
      some ⟨some (labels (.skip 0)), clean ambient, selectTapes tape base input offset output⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      guardStep tape distinct labels done rejected program atLabels base ambient input offset output
  have skip := UnaryBlockSkipMachine.listTrace (count := 6) (tape 0)
    (fun slot => labels (.skip slot)) (some (labels .guard)) rejected program
    (fun slot => atLabels (.skip slot)) (selectTapes tape base input offset output) ambient
    (SourceOccurrenceEncoding.recordWords first clause) (by simp) suffix none
  simp only [update_input tape distinct] at skip
  exact joinTrace guard skip

theorem zeroTrace {n : Nat} (first : Nat) (clause : Target.Clause n)
    (suffix output : List Bool) :
    (advance (TM2.step program))^[1 + (SourceOccurrenceEncoding.recordBits first clause).length]
      (some ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.recordBits first clause ++ suffix) 0 output⟩) =
      some ⟨done, clean ambient, selectTapes tape base suffix 0
        ((encodeWords (clauseWords clause)).reverse ++ output)⟩ := by
  have hd : tape 0 ≠ tape 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (distinct h)
  let input := SourceOccurrenceEncoding.recordBits first clause ++ suffix
  let clauseInput := encodeWords (clauseWords clause) ++ suffix
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), clean ambient, selectTapes tape base input 0 output⟩) =
      some ⟨some (labels (.index 0)), clean ambient, selectTapes tape base input 0 output⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      zeroStep tape distinct labels done rejected program atLabels base ambient input output
  have index : (advance (TM2.step program))^[(encodeWord first).length]
      (some ⟨some (labels (.index 0)), clean ambient, selectTapes tape base input 0 output⟩) =
      some ⟨some (labels (.copy 0)), clean ambient, selectTapes tape base clauseInput 0 output⟩ := by
    have h := UnaryBlockSkipMachine.listTrace (count := 0) (tape 0)
      (fun slot => labels (.index slot)) (some (labels (.copy 0))) rejected program
      (fun slot => atLabels (.index slot)) (selectTapes tape base input 0 output) ambient
      [first] (by simp) clauseInput none
    simpa only [encodeWords, List.append_nil, update_input tape distinct, input, clauseInput,
      SourceOccurrenceEncoding.recordBits_eq, List.append_assoc, clean] using h
  have copy : (advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
      (some ⟨some (labels (.copy 0)), clean ambient, selectTapes tape base clauseInput 0 output⟩) =
      some ⟨done, clean ambient, selectTapes tape base suffix 0
        ((encodeWords (clauseWords clause)).reverse ++ output)⟩ := by
    have h := UnaryBlockCopyMachine.listTrace (tape 0) (tape 2) hd
      (fun slot => labels (.copy slot)) done rejected program
      (fun slot => atLabels (.copy slot)) (selectTapes tape base clauseInput 0 output) ambient
      (clauseWords clause) (by simp) suffix output none
    simpa only [tapesAt_select tape distinct, clauseInput, clean] using h
  have full := joinTrace (joinTrace guard index) copy
  simpa only [input, SourceOccurrenceEncoding.recordBits_eq, List.length_append,
    List.append_assoc, Nat.add_assoc] using full

theorem selectTrace {n : Nat} (clauses : List (Target.Clause n)) (first offset : Nat)
    (bound : offset < clauses.length) (suffix output : List Bool) :
    (advance (TM2.step program))^[steps first clauses offset]
      (some ⟨some (labels .guard), clean ambient,
        selectTapes tape base (SourceOccurrenceEncoding.body first clauses ++ suffix) offset output⟩) =
      some ⟨done, clean ambient,
        selectTapes tape base
          (SourceOccurrenceEncoding.body (first + offset + 1) (clauses.drop (offset + 1)) ++ suffix) 0
          ((encodeWords (clauseWords clauses[offset])).reverse ++ output)⟩ := by
  induction offset generalizing clauses first with
  | zero =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          have h := zeroTrace tape distinct labels done rejected program atLabels base ambient
            first clause (SourceOccurrenceEncoding.body (first + 1) clauses ++ suffix) output
          simpa only [steps, SourceOccurrenceEncoding.body_cons, List.append_assoc,
            Nat.add_zero, List.drop_succ_cons, List.drop_zero, List.getElem_cons_zero] using h
  | succ offset ih =>
      cases clauses with
      | nil => simp at bound
      | cons clause clauses =>
          have tailBound : offset < clauses.length := by
            simp only [List.length_cons] at bound
            omega
          have skip := skipTrace tape distinct labels done rejected program atLabels base ambient
            first clause (SourceOccurrenceEncoding.body (first + 1) clauses ++ suffix) offset output
          have tail := ih clauses (first + 1) tailBound
          have full := joinTrace skip tail
          have address : first + 1 + offset + 1 = first + (offset + 1) + 1 := by omega
          simpa only [steps, SourceOccurrenceEncoding.body_cons, List.append_assoc,
            List.drop_succ_cons, List.getElem_cons_succ, address] using full

end Program

end PerfectCompleteness.SourceClauseSelectMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseLookupMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseLookupMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

theorem body_drop_length_le {n : Nat} (clauses : List (Clause n)) (first k : Nat) :
    (SourceOccurrenceEncoding.body (first + k) (clauses.drop k)).length ≤
      (SourceOccurrenceEncoding.body first clauses).length := by
  induction clauses generalizing first k with
  | nil => simp
  | cons clause clauses ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [List.drop_succ_cons, SourceOccurrenceEncoding.body_cons, List.length_append]
          have tail := ih (first + 1) k
          have indexEq : first + (k + 1) = first + 1 + k := by omega
          rw [indexEq]
          omega

def steps (formula : Formula) (k : Nat) : Nat :=
  2 * ((SourceOccurrenceEncoding.bits formula).length + 1) + 2 * (k + 1) +
    (formula.variables + formula.clauses.length + 2) +
    SourceClauseSelectMachine.steps 0 formula.clauses k + (suffix formula k).length + 1

theorem steps_le (formula : Formula) (k : Nat) (bound : k < formula.clauses.length) :
    steps formula k ≤ 10 * ((SourceOccurrenceEncoding.bits formula).length + k + 1) := by
  have tableLength : (SourceOccurrenceEncoding.bits formula).length =
      formula.variables + formula.clauses.length + 2 +
        (SourceOccurrenceEncoding.body 0 formula.clauses).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  have selectBound := SourceClauseSelectMachine.steps_le formula.clauses 0 k bound
  have suffixBound : (suffix formula k).length ≤
      (SourceOccurrenceEncoding.body 0 formula.clauses).length := by
    simpa only [suffix, Nat.zero_add] using body_drop_length_le formula.clauses 0 (k + 1)
  unfold steps
  omega

variable {K Λ A : Type} [DecidableEq K]

variable (tape : Fin 6 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem headerTrace (formula : Formula) (k : Nat) (output : List Bool) :
    (advance (TM2.step program))^[formula.variables + formula.clauses.length + 2]
      (some ⟨some (labels (.header 0)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.bits formula) (List.replicate k true) output⟩) =
      some ⟨some (labels (.select .guard)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.body 0 formula.clauses)
          (List.replicate k true) output⟩ := by
  have run := UnaryBlockSkipMachine.listTrace (tape 2) (fun slot => labels (.header slot))
    (some (labels (.select .guard))) rejected program (fun slot => atLabels (.header slot))
    (workTapes tape base [] (List.replicate k true) output) ambient
    [formula.variables, formula.clauses.length] rfl
    (SourceOccurrenceEncoding.body 0 formula.clauses) none
  have headerLength : (encodeWords [formula.variables, formula.clauses.length]).length =
      formula.variables + formula.clauses.length + 2 := by
    simp [encodeWords_length]
  have headerInput : encodeWords [formula.variables, formula.clauses.length] ++
      SourceOccurrenceEncoding.body 0 formula.clauses = SourceOccurrenceEncoding.bits formula := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp [encodeWords, List.append_assoc]
  rw [headerLength, headerInput, update_input tape distinct, update_input tape distinct] at run
  exact run

theorem selectTrace (formula : Formula) (k : Nat) (bound : k < formula.clauses.length)
    (output : List Bool) :
    (advance (TM2.step program))^[SourceClauseSelectMachine.steps 0 formula.clauses k]
      (some ⟨some (labels (.select .guard)), clean ambient,
        workTapes tape base (SourceOccurrenceEncoding.body 0 formula.clauses)
          (List.replicate k true) output⟩) =
      some ⟨some (labels .drain), clean ambient,
        workTapes tape base (suffix formula k) []
          ((encodeWords (clauseWords formula.clauses[k])).reverse ++ output)⟩ := by
  have updated (input : List Bool) (index : Nat) (out : List Bool) :
      SourceClauseSelectMachine.selectTapes (selectTapes tape) base input index out =
        workTapes tape base input (List.replicate index true) out := rfl
  have run := SourceClauseSelectMachine.selectTrace (selectTapes tape)
    (selectTapes_injective tape distinct) (fun label => labels (.select label))
    (some (labels .drain)) rejected program (fun label => atLabels (.select label))
    base ambient formula.clauses 0 k bound [] output
  simp only [updated, List.append_nil, List.replicate_zero, Nat.zero_add] at run
  exact run

theorem lookupTrace (formula : Formula) (k : Nat) (bound : k < formula.clauses.length)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (indexWord : base (tape 1) = List.replicate k true)
    (tableCopyEmpty : base (tape 2) = []) (indexCopyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps formula k]
      (some ⟨some (labels main), clean ambient, base⟩) =
      some ⟨done, clean ambient, Function.update base (tape 5)
        ((encodeWords (clauseWords formula.clauses[k])).reverse ++ base (tape 5))⟩ := by
  have first := copyTableTrace tape distinct labels done rejected program atLabels base ambient
    (SourceOccurrenceEncoding.bits formula) (base (tape 5)) tableWord scratchEmpty
  have second := copyIndexTrace tape distinct labels done rejected program atLabels base ambient
    (SourceOccurrenceEncoding.bits formula) (base (tape 5)) k indexWord scratchEmpty
  have third := headerTrace tape distinct labels done rejected program atLabels base ambient
    formula k (base (tape 5))
  have fourth := selectTrace tape distinct labels done rejected program atLabels base ambient
    formula k bound (base (tape 5))
  have fifth := drainTrace tape distinct labels done rejected program atLabels base ambient
    (suffix formula k) ((encodeWords (clauseWords formula.clauses[k])).reverse ++ base (tape 5))
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third) fourth) fifth
  have count :
      ((2 * ((SourceOccurrenceEncoding.bits formula).length + 1) + 2 * (k + 1) +
          (formula.variables + formula.clauses.length + 2)) +
        SourceClauseSelectMachine.steps 0 formula.clauses k) +
          ((suffix formula k).length + 1) = steps formula k := by
    unfold steps
    omega
  have empty (output : List Bool) :
      workTapes tape base [] [] output = Function.update base (tape 5) output :=
    workTapes_empty tape base output tableCopyEmpty indexCopyEmpty
  simpa only [count, main, empty, Function.update_eq_self] using full

end PerfectCompleteness.SourceClauseLookupMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceCoordinateMachine
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceCoordinateMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def resultTapes {n : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (clause : Clause n) : K → List Bool :=
  NormalizationReadMachine.tapes (readerTapes tape) base []
    (NormalizationReadMachine.clauseCounters clause)

def steps (formula : Formula) (index : Fin formula.clauses.length) : Nat :=
  SourceClauseLookupMachine.steps formula index.val +
    ((encodeWords (clauseWords formula.clauses[index.val])).length + 1) +
    SourceClauseReaderMachine.steps formula.clauses[index.val]

theorem steps_le (formula : Formula) (index : Fin formula.clauses.length) :
    steps formula index ≤
      30 * ((SourceOccurrenceEncoding.bits formula).length + index.val + 1) := by
  have lookupBound := SourceClauseLookupMachine.steps_le formula index.val index.isLt
  have readerBound := SourceClauseReaderMachine.steps_le_encoded_length formula.clauses[index.val]
  have clauseBound := clauseBits_length_le formula.clauses[index.val]
  have variableBound : formula.variables ≤ (SourceOccurrenceEncoding.bits formula).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  unfold steps
  omega

variable (tape : Fin 10 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (save : A → CanonicalKeyShape.Shape → A)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected save l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem coordinateTrace (formula : Formula) (index : Fin formula.clauses.length)
    (signs : Signs)
    (tableWord : base (tape 0) = SourceOccurrenceEncoding.bits formula)
    (indexWord : base (tape 1) = List.replicate index.val true)
    (empty : ∀ i : Fin 10, 2 ≤ i.val → base (tape i) = []) :
    (advance (TM2.step program))^[steps formula index]
      (some ⟨some (labels main), SourceClauseReaderMachine.clean ambient signs, base⟩) =
      some ⟨done,
        SourceClauseReaderMachine.clean
          (save ambient (SourceClauseReaderMachine.clauseShape formula.clauses[index.val]))
          (NormalizationReadMachine.clauseSigns formula.clauses[index.val]),
        resultTapes tape base formula.clauses[index.val]⟩ := by
  have hd (i j : Fin 10) (different : i ≠ j) : tape i ≠ tape j :=
    fun same => different (distinct same)
  let clause := formula.clauses[index.val]
  let word := encodeWords (clauseWords clause)
  let reversed := Function.update base (tape 5) word.reverse
  let forward := Function.update base (tape 6) word
  have looked := SourceClauseLookupMachine.lookupTrace (lookupTapes tape)
    (lookupTapes_injective tape distinct) (fun l => labels (.lookup l))
    (some (labels .restore)) rejected program (fun l => atLabels (.lookup l))
    base (ambient, signs) formula index.val index.isLt tableWord indexWord
    (empty 2 (by decide)) (empty 3 (by decide)) (empty 4 (by decide))
  change (advance (TM2.step program))^[SourceClauseLookupMachine.steps formula index.val]
    (some ⟨some (labels main), SourceClauseReaderMachine.clean ambient signs, base⟩) =
    some ⟨some (labels .restore), SourceClauseReaderMachine.clean ambient signs,
      Function.update base (tape 5) (word.reverse ++ base (tape 5))⟩ at looked
  rw [empty 5 (by decide), List.append_nil] at looked
  have restored : (advance (TM2.step program))^[word.length + 1]
      (some ⟨some (labels .restore), SourceClauseReaderMachine.clean ambient signs, reversed⟩) =
      some ⟨some (labels (.read SourceClauseReaderMachine.main)),
        SourceClauseReaderMachine.clean ambient signs, forward⟩ := by
    change (nextAt (tape 6) program)^[word.length + 1]
      (some ⟨some (labels .restore), ((ambient, signs), none), reversed⟩) =
      some ⟨some (labels (.read SourceClauseReaderMachine.main)),
        ((ambient, signs), none), forward⟩
    have source : reversed (tape 5) = word.reverse := by simp [reversed]
    have dest : reversed (tape 6) = [] := by simp [reversed, hd, empty 6 (by decide)]
    have updated : tapesAt (tape 5) (tape 6) reversed [] word = forward := by
      funext k
      by_cases h5 : k = tape 5
      · subst k; simp [tapesAt, reversed, forward, hd, empty 5 (by decide)]
      · by_cases h6 : k = tape 6
        · subst k; simp [tapesAt, reversed, forward]
        · simp [tapesAt, reversed, forward, h5, h6]
    have native := transferAt_fromTapes (Γ := Alphabet (K := K)) (tape 5) (tape 6)
      (hd 5 6 (by decide)) id false (labels .restore)
      (some (labels (.read SourceClauseReaderMachine.main))) program (atLabels .restore)
      reversed (ambient, signs) none
    rw [source, dest, List.length_reverse, List.reverse_reverse, List.map_id_fun,
      List.append_nil, id_eq, updated] at native
    exact native
  have initialReader : NormalizationReadMachine.tapes (readerTapes tape) base word
      (fun _ => []) = forward := by
    funext k
    by_cases h7 : k = tape 7
    · subst k; simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward, hd,
        empty 7 (by decide)]
    · by_cases h8 : k = tape 8
      · subst k; simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward, hd,
          empty 8 (by decide)]
      · by_cases h9 : k = tape 9
        · subst k; simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward, hd,
            empty 9 (by decide)]
        · simp [NormalizationReadMachine.tapes, readerTapes, readerMap, forward,
            Function.update_apply, h7, h8, h9]
  have read := SourceClauseReaderMachine.readTrace (readerTapes tape)
    (readerTapes_injective tape distinct) (fun l => labels (.read l)) done rejected save
    program (fun l => atLabels (.read l)) base ambient clause [] signs none
  simp only [List.append_nil] at read
  change (advance (TM2.step program))^[SourceClauseReaderMachine.steps clause]
    (some ⟨some (labels (.read SourceClauseReaderMachine.main)),
      SourceClauseReaderMachine.clean ambient signs,
      NormalizationReadMachine.tapes (readerTapes tape) base word (fun _ => [])⟩) =
    some ⟨done,
      SourceClauseReaderMachine.clean (save ambient (SourceClauseReaderMachine.clauseShape clause))
        (NormalizationReadMachine.clauseSigns clause),
      resultTapes tape base clause⟩ at read
  rw [initialReader] at read
  exact joinTrace (joinTrace looked restored) read

end PerfectCompleteness.SourceCoordinateMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleData
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleLayout.sourceView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleData


open UniqueGamesTheorem.Foundations Target

variable {width : Nat}

theorem coordinate_initial_empty (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) (fresh : prepared position = false)
    (slot : Fin 10) (work : 2 ≤ slot.val) :
    «stacks» formula indices prepared (localTape position slot) = [] := by
  fin_cases slot <;> simp [localTape, «stacks», fresh] at work ⊢

theorem resultTapes_eq (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) (_fresh : prepared position = false) :
    SourceCoordinateMachine.resultTapes (localTape position) («stacks» formula indices prepared)
        (selectedClause formula indices position) =
      «stacks» formula indices (Function.update prepared position true) := by
  funext key
  cases key with
  | table =>
      simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
        SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap, localTape, «stacks»]
  | digit other =>
      simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
        SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap, localTape, «stacks»]
  | work slot =>
      fin_cases slot <;>
        simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
          SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap, localTape, «stacks»]
  | variableName other slot =>
      by_cases same : other = position
      · subst other
        fin_cases slot <;>
          simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
            SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap,
            localTape, «stacks»]
      · simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
          SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap,
          localTape, «stacks», same]

end PerfectCompleteness.SourceTupleData

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceTupleMachine
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleLayout.sourceView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.baseAccepts_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_ClauseContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.card_VariableContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.localConsistent_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContexts.validJ_eq_true_iff _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_sameName _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_selected _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.ofContext_signs _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature.signatureSatisfies_ofContext _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open SourceTupleData

def cost {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width) : Nat :=
  SourceCoordinateMachine.steps formula (indices position)

def steps {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width)) : Nat :=
  (positions.map (cost formula indices)).sum

theorem result_prepared {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width))
    (data : Data width) (position : Fin width) :
    (result formula indices positions data).prepared position =
      if position ∈ positions then true else data.prepared position := by
  induction positions generalizing data with
  | nil => rfl
  | cons first positions ih =>
      rw [result, ih]
      by_cases here : position = first
      · subst position
        simp [update]
      · simp [update, here]

theorem result_shapes {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width))
    (data : Data width) (position : Fin width) :
    (result formula indices positions data).shapes position =
      if position ∈ positions then
        SourceClauseReaderMachine.clauseShape (selectedClause formula indices position)
      else data.shapes position := by
  induction positions generalizing data with
  | nil => rfl
  | cons first positions ih =>
      rw [result, ih]
      by_cases here : position = first
      · subst position
        simp [update]
      · simp [update, here]

theorem result_finRange_prepared {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (data : Data width) :
    (result formula indices (List.finRange width) data).prepared = fun _ => true := by
  funext position
  simp [result_prepared]

theorem result_finRange_shapes {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (data : Data width) :
    (result formula indices (List.finRange width) data).shapes =
      fun position => SourceClauseReaderMachine.clauseShape
        (selectedClause formula indices position) := by
  funext position
  simp [result_shapes]

theorem cost_le {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width) :
    cost formula indices position ≤ 60 * ((SourceOccurrenceEncoding.bits formula).length + 1) := by
  have bound := SourceCoordinateMachine.steps_le formula (indices position)
  have indexBound := (indices position).isLt
  have countBound : formula.clauses.length ≤ (SourceOccurrenceEncoding.bits formula).length := by
    rw [SourceOccurrenceEncoding.bits_eq]
    simp only [List.length_append, encodeWord_length]
    omega
  unfold cost
  omega

theorem steps_le {width : Nat} (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width)) :
    steps formula indices positions ≤
      positions.length * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1)) := by
  induction positions with
  | nil => simp [steps]
  | cons position positions ih =>
      have head := cost_le formula indices position
      simp only [steps, List.map_cons, List.sum_cons, List.length_cons] at *
      calc
        _ ≤ 60 * ((SourceOccurrenceEncoding.bits formula).length + 1) +
            positions.length * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1)) :=
          Nat.add_le_add head ih
        _ = _ := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

variable {width : Nat} {Λ A : Type}

theorem sequenceTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (positions : List (Fin width))
    (nodup : positions.Nodup) (labels : Label positions → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) = instruction positions labels done rejected label)
    (ambient : A) (data : Data width)
    (fresh : ∀ position ∈ positions, data.prepared position = false) :
    (advance (TM2.step program))^[steps formula indices positions]
      (some ⟨entry positions labels done, state ambient data,
        «stacks» formula indices data.prepared⟩) =
      some ⟨done, state ambient (result formula indices positions data),
        «stacks» formula indices (result formula indices positions data).prepared⟩ := by
  induction positions generalizing data with
  | nil => rfl
  | cons position positions ih =>
      have distinct := List.nodup_cons.mp nodup
      have headFresh := fresh position (by simp)
      let tailEntry := entry positions (fun label => labels (.inr label)) done
      have first := SourceCoordinateMachine.coordinateTrace (localTape position)
        (localTape_injective position) (fun label => labels (.inl label)) tailEntry rejected
        (save position) program (fun label => atLabels (.inl label))
        («stacks» formula indices data.prepared) (ambient, data.shapes)
        formula (indices position) data.signs rfl rfl
        (coordinate_initial_empty formula indices data.prepared position headFresh)
      have outputTapes := resultTapes_eq formula indices data.prepared position headFresh
      dsimp only [selectedClause] at outputTapes
      rw [outputTapes] at first
      change (advance (TM2.step program))^[cost formula indices position]
        (some ⟨some (labels (.inl SourceCoordinateMachine.main)), state ambient data,
          «stacks» formula indices data.prepared⟩) =
        some ⟨tailEntry, state ambient (update formula indices position data),
          «stacks» formula indices (update formula indices position data).prepared⟩ at first
      have tailFresh : ∀ next ∈ positions,
          (update formula indices position data).prepared next = false := by
        intro next member
        have different : next ≠ position := by
          intro same
          subst next
          exact distinct.1 member
        simpa only [update, Function.update_of_ne different] using
          fresh next (List.mem_cons_of_mem position member)
      have rest := ih distinct.2 (fun label => labels (.inr label))
        (fun label => atLabels (.inr label)) (update formula indices position data) tailFresh
      rw [steps, List.map_cons, List.sum_cons, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps formula indices positions]
        ((advance (TM2.step program))^[cost formula indices position]
          (some ⟨some (labels (.inl SourceCoordinateMachine.main)), state ambient data,
            «stacks» formula indices data.prepared⟩)) = _
      rw [first]
      exact rest

theorem tupleTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (labels : Label (List.finRange width) → Λ) (done rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width)) Λ (State width A))
    (atLabels : ∀ label, program (labels label) =
      instruction (List.finRange width) labels done rejected label)
    (ambient : A) (shapes : Fin width → Shape) (signs : Signs) :
    (advance (TM2.step program))^[steps formula indices (List.finRange width)]
      (some ⟨entry (List.finRange width) labels done, state ambient (initial shapes signs),
        «stacks» formula indices (fun _ => false)⟩) =
      some ⟨done,
        SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (selectedClause formula indices position))
          (result formula indices (List.finRange width) (initial shapes signs)).signs,
        «stacks» formula indices (fun _ => true)⟩ := by
  have traced := sequenceTrace formula indices (List.finRange width) (List.nodup_finRange width)
    labels done rejected program atLabels ambient (initial shapes signs) (by intros; rfl)
  simpa only [state, initial, result_finRange_prepared, result_finRange_shapes] using traced

end PerfectCompleteness.SourceTupleMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTuplePlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTuplePlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition

open MachineCloudPadding

variable {width : Nat} {K Λ A : Type}

def tapes (view : K → Option (Tape width)) (extra : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool) : K → List Bool :=
  Placement.tapes view (SourceTupleData.stacks formula indices prepared) extra

theorem tapes_eq_base (tape : Tape width → K) (view : K → Option (Tape width))
    (right : ∀ j k, view j = some k → tape k = j) (base : K → List Bool)
    (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool)
    (contents : ∀ k, base (tape k) = SourceTupleData.stacks formula indices prepared k) :
    tapes view base formula indices prepared = base := by
  funext j
  cases viewed : view j with
  | none => simp only [tapes, Placement.tapes, viewed]
  | some k =>
      simp only [tapes, Placement.tapes, viewed]
      rw [← right j k viewed]
      exact (contents k).symm

end PerfectCompleteness.SourceTuplePlacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceTupleResetMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleResetMachine


open Turing
open UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open SourceTupleData

theorem variable_count_le_table (formula : Formula) :
    formula.variables ≤ (SourceOccurrenceEncoding.bits formula).length := by
  rw [SourceOccurrenceEncoding.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

end PerfectCompleteness.SourceTupleResetMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleResetPlacementLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleBodyPlacement


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding

variable {width : Nat} {K Λ U D : Type}

variable [DecidableEq K]

theorem tupleTrace (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width U D))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) (shapes : Fin width → Shape) (signs : Signs) (frame : Frame D) :
    (advance (TM2.step program))^[SourceTupleMachine.steps formula indices (List.finRange width)]
      (some ⟨SourceTuplePlacement.entry labels exit,
        registers (SourceTupleMachine.state ambient (SourceTupleMachine.initial shapes signs), frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩) =
      some ⟨exit,
        registers (SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (SourceTupleData.selectedClause formula indices position))
          (SourceTupleMachine.result formula indices (List.finRange width)
            (SourceTupleMachine.initial shapes signs)).signs, frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩ := by
  have native := SourceTupleMachine.tupleTrace formula indices id none none
    (SourceTuplePlacement.nativeProgram (width := width) (A := U)) (fun _ => rfl)
    ambient shapes signs
  have lifted := MachineRegularTable.Lift.trace tape view left right labels exit registers frame extra
    (SourceTuplePlacement.nativeProgram (width := width) (A := U)) program atLabels _ _ _ native
  simpa only [MachineRegularTable.Lift.configuration, Placement.label,
    SourceTuplePlacement.entry, SourceTuplePlacement.tapes] using lifted

def tupleInTime (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State width U D))
    (atLabels : ∀ label, program (labels label) = instruction tape labels exit label)
    (extra : K → List Bool) (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) (shapes : Fin width → Shape) (signs : Signs) (frame : Frame D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨SourceTuplePlacement.entry labels exit,
        registers (SourceTupleMachine.state ambient (SourceTupleMachine.initial shapes signs), frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => false)⟩
      (some ⟨exit,
        registers (SourceClauseReaderMachine.clean
          (ambient, fun position => SourceClauseReaderMachine.clauseShape
            (SourceTupleData.selectedClause formula indices position))
          (SourceTupleMachine.result formula indices (List.finRange width)
            (SourceTupleMachine.initial shapes signs)).signs, frame),
        SourceTuplePlacement.tapes view extra formula indices (fun _ => true)⟩)
      (width * (60 * ((SourceOccurrenceEncoding.bits formula).length + 1))) where
  steps := SourceTupleMachine.steps formula indices (List.finRange width)
  evals_in_steps := tupleTrace tape view left right labels exit program atLabels extra
    formula indices ambient shapes signs frame
  steps_le_m := by
    simpa only [List.length_finRange] using
      SourceTupleMachine.steps_le formula indices (List.finRange width)

end PerfectCompleteness.SourceTupleBodyPlacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedTupleLayout
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SignedTupleLayout

open UniqueGamesTheorem.Foundations Complexity Target
open scoped Classical

noncomputable section

variable {width : Nat} {Extra U Desc : Type}

theorem sourceView_right (tape : Tape width Extra) (source : SourceTupleData.Tape width)
    (h : sourceView tape = some source) : Tape.source source = tape := by
  cases tape <;> simp_all [sourceView]

theorem metadata_injective (position : Fin width) :
    Function.Injective (metadata (Extra := Extra) position) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [metadata] at h ⊢

def digitTapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .source (.digit i) => List.replicate (indices i).val true
  | tape => base tape

def rawTapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .source (.digit i) => List.replicate (indices i).val true
  | .source (.variableName i j) => List.replicate (vars formula indices i j) true
  | tape => base tape

theorem prepared_metadata (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (input : Input formula indices base) (i : Fin width) (field : Fin 4) :
    preparedTapes formula indices base (KeyMetadataMachine.idTape (metadata i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids formula indices i) (vars formula indices i) field) := by
  fin_cases field <;>
    simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, metadata, preparedTapes,
      KeyMetadataMachine.fieldValue, ids, input.current] <;> rfl

end
end PerfectCompleteness.SignedTupleLayout

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedDescriptorStageMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedDescriptorStageMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys MetadataFreeSampler
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

local notation "width" => TreeCanonical.locationCount branch n t

variable (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "StageLabel" => Label (Descriptor (rows := rows) (repeats := repeats) hq large) width

variable {K Λ A : Type} [DecidableEq K]

variable [Fintype A] [DecidableEq A]

def stageInTimeForDescriptor (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (descriptor : Descriptor (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ j, Function.Injective (source j))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ j, source j 4 = work 5) (sharedOutput : ∀ j, source j 5 = work 9)
    (sourceAvoid : ∀ j field k, KeyMetadataMachine.idTape (source j) field ≠ work k)
    (count : K) (labels : StageLabel → Λ) (exit rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A))
    (atLabels : ∀ label, program (labels label) =
      instruction (branch := branch) (n := n) (t := t) (q := q)
        (rows := rows) (repeats := repeats) hq large hn hbranch hrows
        selectSigns i source work count labels exit rejected label)
    (base : K → List Bool) (ambient : A) (leftPrefix rightPrefix : List (Key width))
    (sourceWords : ∀ j field, base (KeyMetadataMachine.idTape (source j) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids j) (vars j) field))
    (leftDictionary : base (work 1) = BinaryNameSearch.stream (CanonicalVertexNames.tokens leftPrefix))
    (rightDictionary : base (work 8) = BinaryNameSearch.stream (CanonicalVertexNames.tokens rightPrefix))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = [])
    (selectedEq : SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i = descriptor) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨exit, clean hq large ambient,
        finalTapes hq large descriptor work count base leftPrefix rightPrefix ids vars⟩)
      (CompletedEdgeMachine.budget (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large descriptor source base leftPrefix rightPrefix ids vars + 3) := by
  let edgeTapes : K → List Bool := CompletedEdgeMachine.finalTapes
    (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats)
    hq large descriptor work base
    leftPrefix rightPrefix ids vars
  have loadRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨some (labels .dispatch), loaded hq large ambient descriptor, base⟩) 1 := by
    have run := SignedScheduleIndex.inTime (branch := branch) (n := n) (t := t) (q := q)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows
      (fun state : State (rows := rows) (repeats := repeats) hq large A => selectSigns state.1.1.1)
      (save hq large) i (labels .dispatch) program (labels .load)
      (atLabels .load) (clean hq large ambient) base
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨some (labels .dispatch), loaded hq large ambient
        (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
          (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i),
        base⟩) 1 at run
    rw [selectedEq] at run
    exact run
  have dispatchRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .dispatch), loaded hq large ambient descriptor, base⟩
      (some ⟨some (labels (.edge descriptor (CompletedEdgeMachine.main width))),
        loaded hq large ambient descriptor, base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .dispatch))
      (loaded hq large ambient descriptor) base) = _
    rw [atLabels .dispatch]
    rfl
  have edgeRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.edge descriptor (CompletedEdgeMachine.main width))),
        loaded hq large ambient descriptor, base⟩
      (some ⟨some (labels .finish), loaded hq large ambient descriptor, edgeTapes⟩)
      (CompletedEdgeMachine.budget (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large descriptor
        source base leftPrefix rightPrefix ids vars) :=
    CompletedEdgeMachine.edgeInTime (branch := branch) (n := n) (t := t) (q := q)
      (rows := rows) (repeats := repeats) hq large descriptor ids vars source sourceDistinct
      work workDistinct sharedScratch sharedOutput sourceAvoid
      (fun l => labels (.edge descriptor l)) (labels .finish) rejected program
      (fun l => atLabels (.edge descriptor l)) base (ambient, some descriptor)
      leftPrefix rightPrefix sourceWords leftDictionary rightDictionary empty
  have finishRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .finish), loaded hq large ambient descriptor, edgeTapes⟩
      (some ⟨exit, clean hq large ambient,
        finalTapes hq large descriptor work count base leftPrefix rightPrefix ids vars⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .finish))
      (loaded hq large ambient descriptor) edgeTapes) = _
    rw [atLabels .finish]
    change some (TM2.stepAux (finish hq large count exit)
      (loaded hq large ambient descriptor) edgeTapes) = _
    rw [finish_trace]
    rfl
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ loadRun dispatchRun)
      edgeRun) finishRun
  exact
    { steps := joined.steps
      evals_in_steps := joined.evals_in_steps
      steps_le_m := joined.steps_le_m.trans (stageBudget _) }

def stageInTime (selectSigns : A → SignTuple branch n t) (i : Fin D)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ j, Function.Injective (source j))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ j, source j 4 = work 5) (sharedOutput : ∀ j, source j 5 = work 9)
    (sourceAvoid : ∀ j field k, KeyMetadataMachine.idTape (source j) field ≠ work k)
    (count : K) (labels : StageLabel → Λ) (exit rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (rows := rows) (repeats := repeats) hq large A))
    (atLabels : ∀ label, program (labels label) =
      instruction (branch := branch) (n := n) (t := t) (q := q)
        (rows := rows) (repeats := repeats) hq large hn hbranch hrows
        selectSigns i source work count labels exit rejected label)
    (base : K → List Bool) (ambient : A) (leftPrefix rightPrefix : List (Key width))
    (sourceWords : ∀ j field, base (KeyMetadataMachine.idTape (source j) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids j) (vars j) field))
    (leftDictionary : base (work 1) = BinaryNameSearch.stream (CanonicalVertexNames.tokens leftPrefix))
    (rightDictionary : base (work 8) = BinaryNameSearch.stream (CanonicalVertexNames.tokens rightPrefix))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .load), clean hq large ambient, base⟩
      (some ⟨exit, clean hq large ambient,
        finalTapes hq large
          (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
            (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i)
          work count base leftPrefix rightPrefix ids vars⟩)
      (CompletedEdgeMachine.budget (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats) hq large
        (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
          (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i)
        source base leftPrefix rightPrefix ids vars + 3) :=
  stageInTimeForDescriptor (branch := branch) (n := n) (t := t) (q := q)
    (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns i
    (SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i)
    ids vars source sourceDistinct work workDistinct sharedScratch sharedOutput sourceAvoid
    count labels exit rejected program atLabels base ambient leftPrefix rightPrefix
    sourceWords leftDictionary rightDictionary empty rfl

end
end PerfectCompleteness.SignedDescriptorStageMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedTupleCleanupMachineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTupleCleanupMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition
open scoped Classical

noncomputable section

variable {width : Nat} {Extra U Desc Λ : Type}

theorem selected_length_le (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (tape : Tape width Extra) (h : selected tape = true) :
    (SignedTupleLayout.preparedTapes formula indices base tape).length ≤
      (SourceOccurrenceEncoding.bits formula).length + 1 := by
  cases tape with
  | source source =>
      cases source with
      | table => simp [selected] at h
      | digit position =>
          have bounded := (indices position).isLt
          have tableBound := SourceTupleResetMachine.clause_count_le_table formula
          simp only [SignedTupleLayout.preparedTapes, List.length_replicate]
          omega
      | work slot => simp [selected] at h
      | variableName position slot =>
          have bounded :=
            (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.isLt
          have tableBound := SourceTupleResetMachine.variable_count_le_table formula
          simp only [SignedTupleLayout.preparedTapes, List.length_replicate,
            SignedTupleLayout.vars]
          omega
  | encodedVariable position slot =>
      have bounded :=
        (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.isLt
      have tableBound := SourceTupleResetMachine.variable_count_le_table formula
      simp only [SignedTupleLayout.preparedTapes, encodeWord_length, SignedTupleLayout.vars]
      omega
  | current position => simp [selected] at h
  | remaining position => simp [selected] at h
  | adapterScratch => simp [selected] at h
  | edgeWork slot => simp [selected] at h
  | edgeCount => simp [selected] at h
  | extra value => simp [selected] at h

theorem steps_le (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) :
    steps formula indices base ≤
      7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2) := by
  let tapes := SignedTupleLayout.preparedTapes formula indices base
  let bound := (SourceOccurrenceEncoding.bits formula).length + 1
  have sumBound : ∀ keys : List (Tape width Extra),
      (∀ tape ∈ keys, (tapes tape).length ≤ bound) →
      MachineDrainMany.lengthSum keys tapes ≤ keys.length * bound := by
    intro keys
    induction keys with
    | nil => intro _; simp [MachineDrainMany.lengthSum]
    | cons tape keys ih =>
        intro bounded
        have first := bounded tape (by simp)
        have rest := ih (fun other member => bounded other (List.mem_cons_of_mem tape member))
        simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
          List.length_cons, Nat.add_mul, Nat.one_mul] at rest ⊢
        omega
  have bounded := sumBound (chosen width Extra) (fun tape member =>
    selected_length_le formula indices base tape ((mem_chosen tape).mp member))
  have drains := MachineDrainMany.steps_le (chosen width Extra) tapes
  rw [chosen_length] at bounded drains
  change MachineDrainMany.steps (chosen width Extra) tapes ≤ _
  dsimp only [bound] at bounded
  calc
    MachineDrainMany.steps (chosen width Extra) tapes ≤
        7 * width * ((SourceOccurrenceEncoding.bits formula).length + 1) + 7 * width := by omega
    _ = 7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega

theorem cleanupTrace (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (ambient : U)
    (labels : Label width Extra → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ
      (State width U Desc))
    (atLabels : ∀ label, program (labels label) =
      instruction (width := width) (Extra := Extra) labels exit label) :
    (advance (TM2.step program))^[steps formula indices base]
      (some ⟨entry (width := width) (Extra := Extra) labels exit,
        SignedTupleLayout.preparedState formula indices ambient,
        SignedTupleLayout.preparedTapes formula indices base⟩) =
      some ⟨exit, SignedTupleLayout.preparedState formula indices ambient, base⟩ := by
  have run := MachineDrainMany.trace (chosen width Extra) labels exit program atLabels
    (SignedTupleLayout.preparedTapes formula indices base)
    (SignedTupleLayout.preparedState (Desc := Desc) formula indices ambient).1 none
  rw [MachineDrainMany.finalRegister_none, finalTapes_eq formula indices base input.toClear] at run
  exact run

def cleanupInTime (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (ambient : U)
    (labels : Label width Extra → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ
      (State width U Desc))
    (atLabels : ∀ label, program (labels label) =
      instruction (width := width) (Extra := Extra) labels exit label) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry (width := width) (Extra := Extra) labels exit,
        SignedTupleLayout.preparedState formula indices ambient,
        SignedTupleLayout.preparedTapes formula indices base⟩
      (some ⟨exit, SignedTupleLayout.preparedState formula indices ambient, base⟩)
      (7 * width * ((SourceOccurrenceEncoding.bits formula).length + 2)) where
  steps := steps formula indices base
  evals_in_steps := cleanupTrace formula indices base input ambient labels exit program atLabels
  steps_le_m := steps_le formula indices base

end
end PerfectCompleteness.SignedTupleCleanupMachine


namespace PerfectCompleteness.SignedTuplePreparationMachine


open Turing UniqueGamesTheorem.Foundations Complexity Target
open MachineComposition MachineCloudPadding
open SignedTupleLayout
open scoped Classical

noncomputable section

variable {width : Nat} {Extra U Desc Λ : Type}

def digitView : Tape width Extra → Option (FixedUnaryRepresentationPlacement.Tape width)
  | .current i => some (.source i)
  | .source (.digit i) => some (.destination i)
  | .adapterScratch => some .scratch
  | _ => none

theorem digitView_left (k : FixedUnaryRepresentationPlacement.Tape width) :
    digitView (digitTape (Extra := Extra) k) = some k := by
  cases k <;> rfl

theorem digitView_right (j : Tape width Extra) (k : FixedUnaryRepresentationPlacement.Tape width)
    (h : digitView j = some k) : digitTape k = j := by
  cases j with
  | source localTape =>
      cases localTape <;> simp_all [digitView, digitTape]
      subst k
      rfl
  | current i =>
      simp only [digitView, Option.some.injEq] at h
      subst k
      rfl
  | remaining i => simp_all [digitView]
  | encodedVariable i s => simp_all [digitView]
  | adapterScratch =>
      simp only [digitView, Option.some.injEq] at h
      subst k
      rfl
  | edgeWork s => simp_all [digitView]
  | edgeCount => simp_all [digitView]
  | extra v => simp_all [digitView]

def variableView : Tape width Extra → Option (FixedUnaryRepresentationPlacement.Tape (width * 3))
  | .source (.variableName i s) => some (.source ((variableEquiv width).symm (i, s)))
  | .encodedVariable i s => some (.destination ((variableEquiv width).symm (i, s)))
  | .adapterScratch => some .scratch
  | _ => none

theorem variableView_left (k : FixedUnaryRepresentationPlacement.Tape (width * 3)) :
    variableView (variableTape (Extra := Extra) k) = some k := by
  cases k <;> simp [variableView, variableTape]

theorem variableView_right (j : Tape width Extra)
    (k : FixedUnaryRepresentationPlacement.Tape (width * 3))
    (h : variableView j = some k) : variableTape k = j := by
  cases j with
  | source localTape =>
      cases localTape <;> simp_all [variableView, variableTape]
      subst k
      simp
  | current i => simp_all [variableView]
  | remaining i => simp_all [variableView]
  | encodedVariable i s =>
      simp only [variableView, Option.some.injEq] at h
      subst k
      simp [variableTape]
  | adapterScratch =>
      simp only [variableView, Option.some.injEq] at h
      subst k
      rfl
  | edgeWork s => simp_all [variableView]
  | edgeCount => simp_all [variableView]
  | extra v => simp_all [variableView]

def variableValues (formula : Formula) (indices : Fin width → Fin formula.clauses.length) :
    Fin (width * 3) → Nat :=
  fun i => vars formula indices ((variableEquiv width) i).1 ((variableEquiv width) i).2

theorem digit_initial_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes digitView base .encodedToRaw
      (ids formula indices) (fun _ => []) = base := by
  apply FixedUnaryRepresentationPlacement.tapes_eq_base digitTape digitView digitView_right
  intro k
  cases k with
  | source i => exact input.current i
  | destination i => exact input.rawDigits i
  | scratch => exact input.scratch

theorem digit_final_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes digitView base .encodedToRaw
      (ids formula indices)
      (fun i => FixedUnaryRepresentationMachine.targetWord .encodedToRaw (ids formula indices i) ++ []) =
      digitTapes formula indices base := by
  funext k
  cases k with
  | source localTape => cases localTape <;> simp [FixedUnaryRepresentationPlacement.tapes,
      Placement.tapes, digitView, FixedUnaryRepresentationMachine.stacks,
      FixedUnaryRepresentationMachine.targetWord, digitTapes, ids]
  | current i => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes, digitView,
      FixedUnaryRepresentationMachine.stacks, FixedUnaryRepresentationMachine.sourceWord,
      digitTapes, ids, input.current]
  | remaining i => rfl
  | encodedVariable i s => rfl
  | adapterScratch => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes, digitView,
      FixedUnaryRepresentationMachine.stacks, digitTapes, input.scratch]
  | edgeWork s => rfl
  | edgeCount => rfl
  | extra v => rfl

theorem source_initial_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    SourceTuplePlacement.tapes sourceView (digitTapes formula indices base)
      formula indices (fun _ => false) = digitTapes formula indices base := by
  apply SourceTuplePlacement.tapes_eq_base SignedTupleLayout.Tape.source sourceView sourceView_right
  intro k
  cases k with
  | table => exact input.table
  | digit i => rfl
  | work s => exact input.sourceWork s
  | variableName i s => exact input.rawVariables i s

theorem source_final_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    SourceTuplePlacement.tapes sourceView (digitTapes formula indices base)
      formula indices (fun _ => true) = rawTapes formula indices base := by
  funext k
  cases k with
  | source localTape => cases localTape <;> simp [SourceTuplePlacement.tapes, Placement.tapes,
      sourceView, SourceTupleData.stacks, NormalizationReadMachine.clauseCounters,
      rawTapes, vars, input.table, input.sourceWork]
  | current i => rfl
  | remaining i => rfl
  | encodedVariable i s => rfl
  | adapterScratch => rfl
  | edgeWork s => rfl
  | edgeCount => rfl
  | extra v => rfl

theorem variable_initial_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes variableView (rawTapes formula indices base) .rawToEncoded
      (variableValues formula indices) (fun _ => []) = rawTapes formula indices base := by
  apply FixedUnaryRepresentationPlacement.tapes_eq_base variableTape variableView variableView_right
  intro k
  cases k <;> simp [variableTape, FixedUnaryRepresentationMachine.stacks,
    FixedUnaryRepresentationMachine.sourceWord, rawTapes, variableValues,
    input.encodedVariables, input.scratch]

theorem variable_final_eq (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) :
    FixedUnaryRepresentationPlacement.tapes variableView (rawTapes formula indices base) .rawToEncoded
      (variableValues formula indices)
      (fun i => FixedUnaryRepresentationMachine.targetWord .rawToEncoded
        (variableValues formula indices i) ++ []) = preparedTapes formula indices base := by
  funext k
  cases k with
  | source localTape => cases localTape <;> simp [FixedUnaryRepresentationPlacement.tapes,
      Placement.tapes, variableView, FixedUnaryRepresentationMachine.stacks,
      FixedUnaryRepresentationMachine.sourceWord, variableValues, rawTapes, preparedTapes]
  | current i => rfl
  | remaining i => rfl
  | encodedVariable i s => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes,
      variableView, FixedUnaryRepresentationMachine.stacks, FixedUnaryRepresentationMachine.targetWord,
      variableValues, preparedTapes]
  | adapterScratch => simp [FixedUnaryRepresentationPlacement.tapes, Placement.tapes,
      variableView, FixedUnaryRepresentationMachine.stacks, preparedTapes, input.scratch]
  | edgeWork s => rfl
  | edgeCount => rfl
  | extra v => rfl

variable [DecidableEq Extra]

def prepareInTime (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) (input : Input formula indices base) (ambient : U)
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (width := width) (Extra := Extra)) Λ (State width U Desc))
    (atLabels : ∀ l, program (labels l) = instruction labels exit l) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry labels exit, clean ambient, base⟩
      (some ⟨exit, preparedState formula indices ambient, preparedTapes formula indices base⟩)
      (budget width (SourceOccurrenceEncoding.bits formula).length) := by
  have idsBound (i : Fin width) : ids formula indices i ≤ (SourceOccurrenceEncoding.bits formula).length :=
    Nat.le_trans (Nat.le_of_lt (indices i).isLt) (SourceTupleResetMachine.clause_count_le_table formula)
  have varsBound (i : Fin (width * 3)) :
      variableValues formula indices i ≤ (SourceOccurrenceEncoding.bits formula).length := by
    let position := ((variableEquiv width) i).1
    let slot := ((variableEquiv width) i).2
    have bounded := (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.isLt
    exact Nat.le_trans (Nat.le_of_lt bounded)
      (SourceTupleResetMachine.variable_count_le_table formula)
  have digitsRun := FixedUnaryRepresentationPlacement.familyInTime .encodedToRaw
    (digitTape (Extra := Extra)) digitView digitView_left digitView_right
    (fun l => labels (.digits l)) (sourceEntry labels exit) program (fun l => atLabels (.digits l))
    base (ids formula indices) (fun _ => []) (clean (Desc := Desc) ambient).1
    (SourceOccurrenceEncoding.bits formula).length idsBound
  rw [digit_initial_eq formula indices base input, digit_final_eq formula indices base input] at digitsRun
  have sourceRun := SourceTupleBodyPlacement.tupleInTime (SignedTupleLayout.Tape.source (Extra := Extra)) sourceView
    sourceView_left sourceView_right (fun l => labels (.extract l)) (variableEntry labels exit)
    program (fun l => atLabels (.extract l)) (digitTapes formula indices base) formula indices ambient
    (fun _ => CanonicalKeyShape.Shape.bit) (fun _ => false) (frame Desc)
  rw [source_initial_eq formula indices base input, source_final_eq formula indices base input] at sourceRun
  have variablesRun := FixedUnaryRepresentationPlacement.familyInTime .rawToEncoded
    (variableTape (Extra := Extra)) variableView variableView_left variableView_right
    (fun l => labels (.variableCopies l)) exit program (fun l => atLabels (.variableCopies l))
    (rawTapes formula indices base) (variableValues formula indices) (fun _ => [])
    (preparedState (Desc := Desc) formula indices ambient).1
    (SourceOccurrenceEncoding.bits formula).length varsBound
  rw [variable_initial_eq formula indices base input, variable_final_eq formula indices base input] at variablesRun
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ digitsRun sourceRun) variablesRun
  have cleanEta : ((clean (width := width) (Desc := Desc) ambient).1, (none : Option Bool)) =
      clean (width := width) (Desc := Desc) ambient := rfl
  have preparedEta : ((preparedState (Desc := Desc) formula indices ambient).1, (none : Option Bool)) =
      preparedState (Desc := Desc) formula indices ambient := rfl
  simpa only [entry, sourceEntry, variableEntry, cleanEta, preparedEta,
    budget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

end
end PerfectCompleteness.SignedTuplePreparationMachine


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedTupleBodyMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTupleBodyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition CanonicalKeys MetadataFreeSampler
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "width" => TreeCanonical.locationCount branch n t
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "Desc" => SignedDescriptorStageMachine.Descriptor
  (rows := rows) (repeats := repeats) hq large

variable {K Λ A : Type} [DecidableEq K]

variable [Fintype A] [DecidableEq A]

def sequenceInTime (selectSigns : A → SignTuple branch n t)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ i, Function.Injective (source i))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ i, source i 4 = work 5) (sharedOutput : ∀ i, source i 5 = work 9)
    (sourceAvoid : ∀ i field j, KeyMetadataMachine.idTape (source i) field ≠ work j)
    (countTape : K) (countAvoid : ∀ j, countTape ≠ work j)
    (sourceCount : ∀ i field, KeyMetadataMachine.idTape (source i) field ≠ countTape)
    (indices : List (Fin D))
    (labels : Label (repeats := repeats) hq large hn hbranch hrows indices → Λ)
    (exit rejected : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State (rows := rows) (repeats := repeats) (A := A) hq large))
    (atLabels : ∀ l, program (labels l) =
      instruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns source work countTape
        indices labels exit rejected l)
    (base : K → List Bool) (ambient : A)
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (source i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids i) (vars i) field))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = [])
    (data : Data width) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows indices labels exit,
        SignedDescriptorStageMachine.clean hq large ambient, tapes work countTape base data⟩
      (some ⟨exit, SignedDescriptorStageMachine.clean hq large ambient,
        tapes work countTape base
          (result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) ids vars indices data)⟩)
      (budget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) ids vars source work countTape base
        indices data) := by
  induction indices generalizing data with
  | nil =>
    exact {
      steps := 0
      evals_in_steps := rfl
      steps_le_m := Nat.le_refl _
    }
  | cons i indices ih =>
    let descriptor := SignedScheduleIndex.atIndex (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient) i
    have hd (j k : Fin 10) (hne : j ≠ k) : work j ≠ work k :=
      fun h => hne (workDistinct h)
    have currentSource (position : Fin width) (field : Fin 4) :
        tapes work countTape base data (KeyMetadataMachine.idTape (source position) field) =
          encodeWord (KeyMetadataMachine.fieldValue (ids position) (vars position) field) := by
      rw [tapes_frame work countTape base data _ (sourceCount position field)
        (sourceAvoid position field 1) (sourceAvoid position field 8) (sourceAvoid position field 7)]
      exact sourceWords position field
    have currentEmpty (j : Fin 10) (h1 : j ≠ 1) (h7 : j ≠ 7) (h8 : j ≠ 8) :
        tapes work countTape base data (work j) = [] := by
      rw [tapes_frame work countTape base data _ (Ne.symm (countAvoid j))
        (hd j 1 h1) (hd j 8 h8) (hd j 7 h7)]
      exact empty j h1 h7 h8
    have leftDictionary : tapes work countTape base data (work 1) =
        BinaryNameSearch.stream (CanonicalVertexNames.tokens data.leftKeys) := by
      simp [tapes, Ne.symm (countAvoid 1), hd 1 8 (by decide), hd 1 7 (by decide)]
    have rightDictionary : tapes work countTape base data (work 8) =
        BinaryNameSearch.stream (CanonicalVertexNames.tokens data.rightKeys) := by
      simp [tapes, Ne.symm (countAvoid 8), hd 8 7 (by decide)]
    have first := SignedDescriptorStageMachine.stageInTime (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows selectSigns i
      ids vars source sourceDistinct work workDistinct sharedScratch sharedOutput sourceAvoid
      countTape (fun l => labels (.inl l))
      (entry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows indices (fun l => labels (.inr l)) exit) rejected
      program (fun l => atLabels (.inl l)) (tapes work countTape base data) ambient
      data.leftKeys data.rightKeys currentSource leftDictionary rightDictionary currentEmpty
    rw [finalTapes_eq hq large descriptor ids vars work workDistinct countTape countAvoid base data]
      at first
    have rest := ih (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
      (next hq large descriptor ids vars data)
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ first rest
    refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
    · simpa only [entry, MachineFiniteSequence.entry, localMain, result]
        using joined.evals_in_steps
    · change joined.steps ≤
        (CompletedEdgeMachine.budget hq large descriptor source (tapes work countTape base data)
          data.leftKeys data.rightKeys ids vars + 3) +
        budget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows (selectSigns ambient)
          ids vars source work countTape base indices (next hq large descriptor ids vars data)
      exact joined.steps_le_m.trans (Nat.le_of_eq (Nat.add_comm _ _))

section WholeBody

variable {Extra U : Type} [DecidableEq Extra] [Fintype U] [DecidableEq U]

local notation "Arena" => Tape width Extra
local notation "Control" => BodyState (rows := rows) (repeats := repeats) hq large U
local notation "WholeLabel" => BodyLabel width D Desc Extra

def bodyInTime (formula : UniqueGamesTheorem.Foundations.Target.Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Arena → List Bool)
    (input : SignedTupleLayout.Input formula indices base) (ambient : U) (data : Data width)
    (labels : WholeLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Arena => Bool) Λ Control)
    (atLabels : ∀ label, program (labels label) = bodyInstruction (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels exit label)
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (.edgeWork j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (bodyMain (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows)), SignedTupleLayout.clean ambient,
        tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data⟩
      (some ⟨exit, SignedTupleLayout.clean ambient,
        tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base (tupleResult (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows formula indices data)⟩)
      (bodyBudget (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows formula indices base data) := by
  let initialTapes := tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base data
  let finalData := tupleResult (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows formula indices data
  let finalTapes := tapes SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount base finalData
  let prepared := SignedTupleLayout.preparedTapes formula indices base
  let sourceControl := SignedTupleLayout.preparedSource formula indices ambient
  have startRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .start), SignedTupleLayout.clean ambient, initialTapes⟩
      (some ⟨SignedTuplePreparationMachine.entry (fun l => labels (.prepare l))
        (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels),
        SignedTupleLayout.clean ambient, initialTapes⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .start)) (SignedTupleLayout.clean ambient) initialTapes) = _
    rw [atLabels .start]
    change some (TM2.stepAux (bodyExit hq large _) (SignedTupleLayout.clean ambient) initialTapes) = _
    cases SignedTuplePreparationMachine.entry (fun l => labels (.prepare l))
      (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) <;> rfl
  have prepareRun := SignedTuplePreparationMachine.prepareInTime formula indices initialTapes
    (tapes_input formula indices base input data) ambient
    (fun l => labels (.prepare l)) (edgesEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels)
    program (fun l => atLabels (.prepare l))
  dsimp only [initialTapes] at prepareRun
  rw [prepared_tapes_commute] at prepareRun
  have sourceAvoid : ∀ (i : Fin width) (field : Fin 4) (j : Fin 10),
      KeyMetadataMachine.idTape (SignedTupleLayout.metadata (Extra := Extra) i) field ≠ SignedTupleLayout.Tape.edgeWork j := by
    intro i field j
    fin_cases field <;> simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, SignedTupleLayout.metadata]
  have sourceCount : ∀ (i : Fin width) (field : Fin 4),
      KeyMetadataMachine.idTape (SignedTupleLayout.metadata (Extra := Extra) i) field ≠ SignedTupleLayout.Tape.edgeCount := by
    intro i field
    fin_cases field <;> simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, SignedTupleLayout.metadata]
  have edgesRun := sequenceInTime (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows bodySigns
    (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
    SignedTupleLayout.metadata SignedTupleLayout.metadata_injective
    SignedTupleLayout.Tape.edgeWork (by intro i j h; cases h; rfl) (fun _ => rfl) (fun _ => rfl) sourceAvoid
    SignedTupleLayout.Tape.edgeCount (by intro j; simp) sourceCount
    (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hn hbranch hrows) (fun l => labels (.edges l))
    (cleanupEntry (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats) hq large hn hbranch hrows labels) none program
    (fun l => atLabels (.edges l)) prepared sourceControl
    (SignedTupleLayout.prepared_metadata formula indices base input)
    (by intro j h1 h7 h8; exact empty j h1 h7 h8) data
  have signsEq : bodySigns (branch := branch) (n := n) (t := t) sourceControl =
      SourceTupleScheduleMachine.sourceSigns (branch := branch) (n := n) (t := t) formula indices :=
    bodySigns_prepared (branch := branch) (n := n) (t := t) formula indices ambient
  have resultEq :
      result (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows (bodySigns sourceControl)
        (SignedTupleLayout.ids formula indices) (SignedTupleLayout.vars formula indices)
        (allStages (branch := branch) (n := n) (t := t) (q := q) (rows := rows) (repeats := repeats)
          hn hbranch hrows) data = finalData := by
    rw [signsEq]
    rfl
  have stateEq : SignedDescriptorStageMachine.clean (branch := branch) (n := n) (t := t)
      (q := q) (rows := rows) (repeats := repeats) hq large sourceControl =
      SignedTupleLayout.preparedState («Desc» := Desc) formula indices ambient := rfl
  rw [stateEq, resultEq] at edgesRun
  have cleanupRun := SignedTupleCleanupMachine.cleanupInTime formula indices finalTapes
    (tapes_input formula indices base input finalData) ambient
    (fun l => labels (.cleanup l)) (some (labels .reset)) program (fun l => atLabels (.cleanup l))
  have cleanupDecider : (fun a b : Extra => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq Extra) := Subsingleton.elim _ _
  rw [cleanupDecider] at cleanupRun
  dsimp only [finalTapes] at cleanupRun
  rw [prepared_tapes_commute] at cleanupRun
  have resetRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reset), SignedTupleLayout.preparedState formula indices ambient, finalTapes⟩
      (some ⟨exit, SignedTupleLayout.clean ambient, finalTapes⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    change some (TM2.stepAux (program (labels .reset))
      (SignedTupleLayout.preparedState formula indices ambient) finalTapes) = _
    rw [atLabels .reset]
    cases exit <;> rfl
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
        (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ startRun prepareRun)
        edgesRun) cleanupRun) resetRun
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [bodyMain, tupleResult, finalData, finalTapes, initialTapes,
      prepared, sourceControl, bodySigns_prepared] using joined.evals_in_steps
  · have bounded := joined.steps_le_m.trans (bodyBudgetOrder _ _ _)
    simpa only [bodyBudget, prepared, sourceControl, bodySigns_prepared] using bounded

end WholeBody

end
end PerfectCompleteness.SignedTupleBodyMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceProducerLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedSourceInput


open Turing UniqueGamesTheorem.Foundations Complexity Target

structure Input where
  formula : Formula
  nonempty : formula.clauses ≠ []
  distinct : ∀ clause ∈ formula.clauses, ∀ i j : Fin 3,
    clause[i].variableIndex = clause[j].variableIndex → i = j

def bits (input : Input) : List Bool := SourceOccurrenceEncoding.bits input.formula

def variableCount (input : Input) : Nat := input.formula.variables
def clauseCount (input : Input) : Nat := input.formula.clauses.length

theorem clauseCount_positive (input : Input) : 0 < clauseCount input :=
  List.length_pos_iff.mpr input.nonempty

instance clauseCount_neZero (input : Input) : NeZero (clauseCount input) :=
  ⟨Nat.ne_of_gt (clauseCount_positive input)⟩

def clauses (input : Input) : Fin (clauseCount input) → SourceClause.NormalizedClause (variableCount input) :=
  fun index =>
    { clause := input.formula.clauses[index.val]
      distinct := input.distinct _ (List.getElem_mem index.isLt) }

@[simp] theorem clause_eq (input : Input) (index : Fin (clauseCount input)) :
    (clauses input index).clause = input.formula.clauses[index.val] := rfl

@[simp] theorem variable_eq (input : Input) (index : Fin (clauseCount input)) (slot : Fin 3) :
    (clauses input index).variable slot = input.formula.clauses[index.val][slot].variableIndex := rfl

@[simp] theorem signs_eq (input : Input) (index : Fin (clauseCount input)) :
    (clauses input index).signs =
      (input.formula.clauses[index.val][0].positive,
       input.formula.clauses[index.val][1].positive,
       input.formula.clauses[index.val][2].positive) := rfl

theorem bits_eq (input : Input) :
    bits input = encodeWord (variableCount input) ++ encodeWord (clauseCount input) ++
      SourceOccurrenceEncoding.body 0 input.formula.clauses :=
  SourceOccurrenceEncoding.bits_eq input.formula

noncomputable section

def normalized (formula : Formula) : Input where
  formula := PCPSource.normalizedFormula formula
  nonempty := PCPSource.normalizedFormula_nonempty formula
  distinct := PCPSource.normalizedFormula_distinct formula

@[simp] theorem normalized_formula (formula : Formula) :
    (normalized formula).formula = PCPSource.normalizedFormula formula := rfl

@[simp] theorem normalized_bits (formula : Formula) :
    bits (normalized formula) = SourceOccurrenceEncoding.bits (PCPSource.normalizedFormula formula) := rfl

def raw (input : List Bool) : Input := normalized (BinaryLanguage.totalRename input)

@[simp] theorem raw_formula (input : List Bool) :
    (raw input).formula = PCPSourceMachine.rawSource input := rfl

def fromReduction {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) : Input :=
  normalized (source.reduce input)

@[simp] theorem fromReduction_formula {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) (input : List Bool) :
    (fromReduction source input).formula = PCPSourceHardness.formula source input := rfl

end
end PerfectCompleteness.NormalizedSourceInput

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_NormalizedTarget
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple
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

def inputBits (input : NormalizedSourceInput.Input) : List Bool :=
  NormalizedSourceInput.bits input

@[simp] theorem inputBits_eq (input : NormalizedSourceInput.Input) :
    inputBits input = SourceOccurrenceEncoding.bits input.formula := rfl

abbrev SourceTuple (input : NormalizedSourceInput.Input) :=
  Fin (TreeCanonical.locationCount branch n t) →
    Fin (NormalizedSourceInput.clauseCount input)

def tupleQuestion (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input) :=
  SourceQuestionOrder.tupleToQuestion indices

@[simp] theorem tupleQuestion_digits (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    SourceQuestionOrder.questionToTuple (tupleQuestion input indices) = indices :=
  SourceQuestionOrder.questionToTuple_tupleToQuestion indices

def parsedVariableIDs (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) (slot : Fin 3) : Nat :=
  (SourceTupleData.selectedClause input.formula indices position)[slot].variableIndex.val

@[simp] theorem parsedVariableIDs_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) (slot : Fin 3) :
    parsedVariableIDs input indices position slot =
      ((NormalizedSourceInput.clauses input (indices position)).variable slot).val := rfl

theorem sourceSigns_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    SourceTupleScheduleMachine.sourceSigns input.formula indices =
      MetadataFreeSampler.sourceSigns (NormalizedSourceInput.clauses input)
        (tupleQuestion input indices) := by
  funext leaf coordinate
  rfl

variable (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ

def construct (input : NormalizedSourceInput.Input) : Instance q :=
  ExactPreliminaryTarget.construct (t := t) (NormalizedSourceInput.clauses input)
    rows repeats hn hbranch hrows δ

@[simp] theorem construct_eq (input : NormalizedSourceInput.Input) :
    construct (t := t) rows repeats hn hbranch hrows δ input =
      ExactPreliminaryTarget.construct (t := t) (NormalizedSourceInput.clauses input)
        rows repeats hn hbranch hrows δ := rfl

end
end PerfectCompleteness.NormalizedTarget

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOdometer
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ExactTargetOdometer


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {width radix : Nat}

variable {branch : Nat → Nat} {n t v m : Nat}

theorem visits_sourceOrder
    (digits : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    (visits (TreeCanonical.locationCount branch n t) digits).map
        SourceQuestionOrder.tupleToQuestion = SourceVisitOrder.visitOrder branch n t m := by
  rw [visits_all, SourceVisitOrder.visitOrder_eq_tupleOrder]

variable (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
  [NeZero m] (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

theorem visits_completedOrder
    (digits : Fin (TreeCanonical.locationCount branch n t) → Fin m) :
    (visits (TreeCanonical.locationCount branch n t) digits).flatMap
        (fun tuple => CompletedVisitOrder.localOrder clauses rows repeats hn hbranch hrows δ
          (SourceQuestionOrder.tupleToQuestion tuple)) =
      CompletedVisitOrder.completedOrder (t := t) clauses rows repeats hn hbranch hrows δ := by
  rw [CompletedVisitOrder.completedOrder, ← visits_sourceOrder digits, List.flatMap_map]

end

noncomputable section

variable {width : Nat} {Extra : Type}

def baseTapes (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) : SignedTupleLayout.Tape width Extra → List Bool
  | .source .table => NormalizedSourceInput.bits input
  | .current i => encodeWord (indices i).val
  | .remaining i => encodeWord (NormalizedSourceInput.clauseCount input - 1 - (indices i).val)
  | .extra x => extra x
  | _ => []

theorem baseTapes_input (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) :
    SignedTupleLayout.Input input.formula indices (baseTapes input indices extra) where
  toClear := {
    rawDigits := fun _ => rfl
    rawVariables := fun _ _ => rfl
    sourceWork := fun _ => rfl
    encodedVariables := fun _ _ => rfl
    scratch := rfl
  }
  table := rfl
  current := fun _ => rfl

@[simp] theorem baseTapes_edgeWork (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) (j : Fin 10) :
    baseTapes input indices extra (.edgeWork j) = [] := rfl

theorem baseTapes_emptyWork (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (extra : Extra → List Bool) :
    ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 →
      baseTapes input indices extra (.edgeWork j) = [] := by
  intro j _ _ _
  rfl


variable {branch : Nat → Nat} {n t : Nat} [DecidableEq Extra]

local notation "W" => TreeCanonical.locationCount branch n t

def nativeTapes (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    SignedTupleLayout.Tape W Extra → List Bool :=
  SignedTupleBodyMachine.tapes (branch := branch) (n := n) (t := t)
    SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount
    (baseTapes input indices extra) data

@[simp] theorem nativeTapes_table (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    nativeTapes input indices data extra (.source .table) = NormalizedSourceInput.bits input := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

@[simp] theorem nativeTapes_current (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) (i : Fin W) :
    nativeTapes input indices data extra (.current i) = encodeWord (indices i).val := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

@[simp] theorem nativeTapes_remaining (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) (i : Fin W) :
    nativeTapes input indices data extra (.remaining i) =
      encodeWord (NormalizedSourceInput.clauseCount input - 1 - (indices i).val) := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

@[simp] theorem nativeTapes_output (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    nativeTapes input indices data extra (.edgeWork 7) = data.reversedOutput := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes]

@[simp] theorem nativeTapes_count (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) :
    nativeTapes input indices data extra .edgeCount = encodeWord data.count := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes]

@[simp] theorem nativeTapes_extra (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool) (x : Extra) :
    nativeTapes input indices data extra (.extra x) = extra x := by
  simp [nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

theorem digitTapes_nativeTapes (input : NormalizedSourceInput.Input)
    (indices : Fin W → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data W) (extra : Extra → List Bool)
    (coordinate : Fin W) (value : Fin (NormalizedSourceInput.clauseCount input)) :
    MachineTupleOdometer.digitTapes
        (SignedTupleLayout.Tape.current coordinate)
        (SignedTupleLayout.Tape.remaining coordinate)
        (nativeTapes input indices data extra)
        value.val (NormalizedSourceInput.clauseCount input - 1 - value.val) [] [] =
      nativeTapes input (Function.update indices coordinate value) data extra := by
  funext tape
  cases tape with
  | source source =>
      cases source <;>
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
  | current position =>
      by_cases same : position = coordinate
      · subst position
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
      · simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, same]
  | remaining position =>
      by_cases same : position = coordinate
      · subst position
        simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
      · simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
          UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
          nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, same]
  | encodedVariable position slot =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
  | adapterScratch =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]
  | edgeWork j =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes, Function.update_apply]
  | edgeCount =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes]
  | extra x =>
      simp [MachineTupleOdometer.digitTapes, MachineUnaryAddAt.unaryTapes,
        UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt,
        nativeTapes, SignedTupleBodyMachine.tapes, baseTapes]

end

noncomputable section Native

variable {branch : Nat → Nat} {n t : Nat}
  (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "hq" => CanonicalLocalCompletion.alphabet_positive width δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet width δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "Desc" => SignedCompletionSchedule.Descriptor (rows := rows) (repeats := repeats) hq large

abbrev Control := SignedTupleLayout.State width Unit Desc
abbrev Ambient := (SourceTupleMachine.State width Unit × Option Desc) × (Bool × Option Bool)
abbrev NativeLabel (Extra : Type) := Label width D Desc Extra

variable {Extra : Type} [DecidableEq Extra]

local notation "Arena" => SignedTupleLayout.Tape width Extra
local notation "Labels" => NativeLabel (branch := branch) (n := n) (t := t)
  rows repeats hn hbranch hrows δ Extra
local notation "Registers" => Control (branch := branch) (n := n) (t := t) rows repeats δ

def checkAt (depth : Nat) : Labels :=
  if h : depth < width then .check ⟨depth, h⟩ else .exit

def resetAt (depth : Nat) : Labels :=
  if h : depth < width then .reset ⟨depth, h⟩ else .exit

def currentAt (depth : Nat) : Arena :=
  if h : depth < width then .current ⟨depth, h⟩ else .adapterScratch

def remainingAt (depth : Nat) : Arena :=
  if h : depth < width then .remaining ⟨depth, h⟩ else .edgeCount

def body : Labels := .body .start

def program : Labels → Turing.TM2.Stmt (fun _ : Arena => Bool) Labels Registers
  | .body label => SignedTupleBodyMachine.bodyInstruction (branch := branch) (n := n) (t := t)
      (rows := rows) (repeats := repeats) hq large hn hbranch hrows
      Label.body (some (checkAt (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ 0)) label
  | .check i => MachineTupleOdometer.increment (.current i) (.remaining i)
      (body (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ) (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.remaining i) (.reset i)
      (checkAt (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ (i.val + 1))
  | .exit => .halt

def tupleStep (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) : SignedTupleBodyMachine.Data width :=
  SignedTupleBodyMachine.result (branch := branch) (n := n) (t := t)
    (rows := rows) (repeats := repeats) hq large hn hbranch hrows
    (MetadataFreeSampler.sourceSigns (NormalizedSourceInput.clauses input)
      (SourceQuestionOrder.tupleToQuestion indices))
    (fun i => (indices i).val)
    (fun i slot => ((NormalizedSourceInput.clauses input) (indices i)).variable slot |>.val)
    (List.ofFn (fun i : Fin D => i)) data

theorem tupleStep_eq (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) :
    tupleStep rows repeats hn hbranch hrows δ input indices data =
      SignedTupleBodyMachine.tupleResult (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows input.formula indices data := rfl

local notation "runProgram" => program (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "entry" => body (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "atCheck" => checkAt (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "atReset" => resetAt (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "atCurrent" => currentAt (branch := branch) (n := n) (t := t) (Extra := Extra)
local notation "atRemaining" => remainingAt (branch := branch) (n := n) (t := t) (Extra := Extra)

def configuration (label : Labels) (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) :
    Turing.TM2.Cfg (fun _ : Arena => Bool) Labels Registers :=
  ⟨some label, SignedTupleLayout.clean (), nativeTapes input indices data extra⟩

local notation "cfg" => configuration rows repeats hn hbranch hrows δ

def leafBudget (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) : Nat :=
  SignedTupleBodyMachine.bodyBudget (branch := branch) (n := n) (t := t)
    (rows := rows) (repeats := repeats)
    hq large hn hbranch hrows
    input.formula indices (baseTapes input indices extra) data

def leafInTime (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime (Turing.TM2.step runProgram)
      (cfg entry input indices data extra)
      (some (cfg (atCheck 0) input indices
        (tupleStep rows repeats hn hbranch hrows δ input indices data) extra))
      (leafBudget rows repeats hn hbranch hrows δ input indices data extra) := by
  have run := SignedTupleBodyMachine.bodyInTime (branch := branch) (n := n) (t := t)
    (rows := rows) (repeats := repeats) hq large hn hbranch hrows
    input.formula indices (baseTapes input indices extra) (baseTapes_input input indices extra)
    () data Label.body (some (atCheck 0)) runProgram (fun _ => rfl)
    (baseTapes_emptyWork input indices extra)
  simpa only [configuration, body, SignedTupleBodyMachine.bodyMain, nativeTapes,
    tupleStep_eq, leafBudget] using run

def maxLeafBudget (input : NormalizedSourceInput.Input) (extra : Extra → List Bool) :
    Nat → (Fin width → Fin (NormalizedSourceInput.clauseCount input)) →
      SignedTupleBodyMachine.Data width → Nat
  | 0, indices, data => leafBudget rows repeats hn hbranch hrows δ input indices data extra
  | depth + 1, indices, data => Finset.univ.sup fun value =>
      maxLeafBudget input extra depth (setCoordinate indices depth value)
        (blockPrefix (tupleStep rows repeats hn hbranch hrows δ input) depth indices value.val data)

def CostsAtMost (input : NormalizedSourceInput.Input) (extra : Extra → List Bool) (B : Nat) :
    Nat → (Fin width → Fin (NormalizedSourceInput.clauseCount input)) →
      SignedTupleBodyMachine.Data width → Prop
  | 0, indices, data => leafBudget rows repeats hn hbranch hrows δ input indices data extra ≤ B
  | depth + 1, indices, data => ∀ value,
      CostsAtMost input extra B depth (setCoordinate indices depth value)
        (blockPrefix (tupleStep rows repeats hn hbranch hrows δ input) depth indices value.val data)

theorem digitTapes_at (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool)
    (depth remainder : Nat) (inside : depth < width)
    (remainingBound : remainder ≤ NormalizedSourceInput.clauseCount input - 1) :
    MachineTupleOdometer.digitTapes (atCurrent depth) (atRemaining depth)
        (nativeTapes input indices data extra)
        (NormalizedSourceInput.clauseCount input - 1 - remainder) remainder [] [] =
      nativeTapes input (setCoordinate indices depth
        ⟨NormalizedSourceInput.clauseCount input - 1 - remainder,
          by have := NormalizedSourceInput.clauseCount_positive input; omega⟩) data extra := by
  have positive := NormalizedSourceInput.clauseCount_positive input
  have valueBound : NormalizedSourceInput.clauseCount input - 1 - remainder <
      NormalizedSourceInput.clauseCount input := by omega
  have complement : NormalizedSourceInput.clauseCount input - 1 -
      (NormalizedSourceInput.clauseCount input - 1 - remainder) = remainder := by omega
  have h := digitTapes_nativeTapes input indices data extra ⟨depth, inside⟩
    ⟨NormalizedSourceInput.clauseCount input - 1 - remainder, valueBound⟩
  simpa only [currentAt, remainingAt, dite_eq_left inside, complement,
    ← setCoordinate_eq_update] using h

theorem existsTree (input : NormalizedSourceInput.Input) (extra : Extra → List Bool)
    (B depth : Nat) (inside : depth ≤ width)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (zero : ∀ i, i.val < depth → (indices i).val = 0)
    (data : SignedTupleBodyMachine.Data width)
    (costs : CostsAtMost rows repeats hn hbranch hrows δ input extra B depth indices data) :
    ∃ tree : MachineTupleOdometer.NestedCycle (NormalizedSourceInput.clauseCount input)
      atCurrent atRemaining entry atCheck atReset runProgram depth (atCheck depth)
      (cfg entry input indices data extra)
      (cfg (atCheck depth) input indices
        (foldVisits (tupleStep rows repeats hn hbranch hrows δ input) depth indices data) extra),
      tree.LeafBound B := by
  let m := NormalizedSourceInput.clauseCount input
  have positive : 0 < m := NormalizedSourceInput.clauseCount_positive input
  let step := tupleStep (branch := branch) (n := n) (t := t) rows repeats hn hbranch hrows δ input
  induction depth generalizing indices data with
  | zero =>
      let run := leafInTime rows repeats hn hbranch hrows δ input indices data extra
      refine ⟨.leaf (atCheck 0) (cfg entry input indices data extra)
        (cfg (atCheck 0) input indices (foldVisits step 0 indices data) extra)
        run.steps rfl rfl run.evals_in_steps, ?_⟩
      unfold MachineTupleOdometer.NestedCycle.LeafBound
      exact run.steps_le_m.trans costs
  | succ depth ih =>
      have hlt : depth < width := by omega
      let accumulated := blockPrefix step depth indices
      let schedule : MachineTupleOdometer.CycleSchedule Arena (Ambient (branch := branch) (n := n) (t := t) rows repeats δ) :=
        { currentSuffix := []
          remainingSuffix := []
          ambient := fun _ => (SignedTupleLayout.clean («width» := width) («Desc» := Desc) ()).1
          register := fun _ => none
          base := fun remainder => nativeTapes input indices (accumulated (m - remainder) data) extra }
      have children : ∀ r : Fin m,
          ∃ tree : MachineTupleOdometer.NestedCycle m atCurrent atRemaining entry atCheck
            atReset runProgram depth (atCheck depth)
            (MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
              entry (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base)
            (MachineTupleOdometer.checkConfiguration (atCurrent depth) (atRemaining depth)
              (atCheck depth) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
        intro r
        have hr : r.val ≤ m - 1 := by omega
        let value : Fin m := ⟨m - 1 - r.val, by omega⟩
        have before : m - (r.val + 1) = value.val := by dsimp [value]; omega
        have after : m - r.val = value.val + 1 := by dsimp [value]; omega
        have childZero : ∀ i, i.val < depth →
            (setCoordinate indices depth value i).val = 0 := by
          intro i hi
          simp only [setCoordinate, ite_eq_right (by omega : i.val ≠ depth)]
          exact zero i (by omega)
        have childCosts : CostsAtMost rows repeats hn hbranch hrows δ input extra B depth
            (setCoordinate indices depth value) (accumulated (m - (r.val + 1)) data) := by
          rw [before]
          exact costs value
        obtain ⟨child, bounded⟩ := ih (by omega) (setCoordinate indices depth value)
          childZero (accumulated (m - (r.val + 1)) data) childCosts
        have outputData : foldVisits step depth (setCoordinate indices depth value)
            (accumulated (m - (r.val + 1)) data) = accumulated (m - r.val) data := by
          rw [before, after]
          exact (blockPrefix_succ step depth indices value data).symm
        have childExists :
            ∃ child : MachineTupleOdometer.NestedCycle m atCurrent atRemaining entry atCheck
              atReset runProgram depth (atCheck depth)
              (cfg entry input (setCoordinate indices depth value)
                (accumulated (m - (r.val + 1)) data) extra)
              (cfg (atCheck depth) input (setCoordinate indices depth value)
                (foldVisits step depth (setCoordinate indices depth value)
                  (accumulated (m - (r.val + 1)) data)) extra), child.LeafBound B :=
          ⟨child, bounded⟩
        rw [outputData] at childExists
        have childStart :
            cfg entry input (setCoordinate indices depth value)
                (accumulated (m - (r.val + 1)) data) extra =
              MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
                entry (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
                schedule.ambient schedule.base := by
          dsimp only [MachineTupleOdometer.bodyConfiguration, schedule, configuration]
          rw [digitTapes_at input indices _ extra depth r.val hlt hr]
          rfl
        have childFinish :
            cfg (atCheck depth) input (setCoordinate indices depth value)
                (accumulated (m - r.val) data) extra =
              MachineTupleOdometer.checkConfiguration (atCurrent depth) (atRemaining depth)
                (atCheck depth) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
                schedule.ambient schedule.register schedule.base := by
          dsimp only [MachineTupleOdometer.checkConfiguration, schedule, configuration]
          rw [digitTapes_at input indices _ extra depth r.val hlt hr]
          rfl
        rw [childStart, childFinish] at childExists
        exact childExists
      let chosen := fun r => Classical.choose (children r)
      have chosenBound : ∀ r, (chosen r).LeafBound B :=
        fun r => Classical.choose_spec (children r)
      have distinct : atCurrent depth ≠ atRemaining depth := by
        simp [currentAt, remainingAt, hlt]
      have checkInstruction : runProgram (atCheck depth) =
          MachineTupleOdometer.increment (atCurrent depth) (atRemaining depth) entry (atReset depth) := by
        simp [program, checkAt, currentAt, remainingAt, resetAt, hlt]
      have resetInstruction : runProgram (atReset depth) =
          MachineTupleOdometer.reset (atCurrent depth) (atRemaining depth)
            (atReset depth) (atCheck (depth + 1)) := by
        simp [program, resetAt, currentAt, remainingAt, hlt]
      let tree := MachineTupleOdometer.NestedCycle.node depth (atCheck (depth + 1))
        positive distinct checkInstruction resetInstruction schedule chosen
      have treeBound : tree.LeafBound B := by
        simpa only [tree, MachineTupleOdometer.NestedCycle.LeafBound] using chosenBound
      have unchanged : setCoordinate indices depth ⟨0, positive⟩ = indices :=
        setCoordinate_zero indices depth positive (fun i hi => zero i (by omega))
      have startTapes : MachineTupleOdometer.digitTapes (atCurrent depth) (atRemaining depth)
          (nativeTapes input indices (accumulated (m - ((m - 1) + 1)) data) extra)
          (m - 1 - (m - 1)) (m - 1) [] [] = nativeTapes input indices data extra := by
        rw [digitTapes_at input indices _ extra depth (m - 1) hlt (Nat.le_refl _)]
        have full : m - 1 + 1 = m := by omega
        dsimp only [m] at full unchanged ⊢
        simp only [Nat.sub_self, unchanged, full, accumulated, blockPrefix_zero]
      have finishTapes : MachineTupleOdometer.digitTapes (atCurrent depth) (atRemaining depth)
          (nativeTapes input indices (accumulated (m - 0) data) extra) 0 (m - 1) [] [] =
          nativeTapes input indices (foldVisits step (depth + 1) indices data) extra := by
        have h := digitTapes_at input indices (accumulated m data) extra depth (m - 1)
          hlt (Nat.le_refl _)
        dsimp only [m] at h unchanged ⊢
        simpa only [Nat.sub_self, Nat.sub_zero, unchanged, accumulated, blockPrefix_all] using h
      have nodeExists :
          ∃ node : MachineTupleOdometer.NestedCycle m atCurrent atRemaining entry atCheck
            atReset runProgram (depth + 1) (atCheck (depth + 1))
            (MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
              entry (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base)
            (MachineTupleOdometer.cycleExit (atCurrent depth) (atRemaining depth)
              (atCheck (depth + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base), node.LeafBound B := ⟨tree, treeBound⟩
      have nodeStart :
          MachineTupleOdometer.bodyConfiguration (atCurrent depth) (atRemaining depth)
              entry (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base = cfg entry input indices data extra := by
        dsimp only [MachineTupleOdometer.bodyConfiguration, schedule, configuration]
        rw [startTapes]
        rfl
      have nodeFinish :
          MachineTupleOdometer.cycleExit (atCurrent depth) (atRemaining depth)
              (atCheck (depth + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.base =
            cfg (atCheck (depth + 1)) input indices (foldVisits step (depth + 1) indices data) extra := by
        dsimp only [MachineTupleOdometer.cycleExit, schedule, configuration]
        rw [finishTapes]
        rfl
      rw [nodeStart, nodeFinish] at nodeExists
      exact nodeExists

def result (input : NormalizedSourceInput.Input) (data : SignedTupleBodyMachine.Data width) :
    SignedTupleBodyMachine.Data width :=
  foldVisits (tupleStep rows repeats hn hbranch hrows δ input) width
    (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data

end Native

noncomputable section Semantics

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
    (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "C" => CompletedSignedLaw.Completed (t := t) (NormalizedSourceInput.clauses input)
  rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "pack" => SignedTupleSemantics.dataOfPrefix
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ

theorem tupleStep_dataOfPrefix
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++
      localOrder (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) ++
        suffix) :
    ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input indices
        (pack earlier tail) =
      pack (earlier ++ localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) tail := by
  simpa only [ExactTargetOdometer.tupleStep, List.finRange,
    SignedTupleSemantics.sourceIDs_tuple, SignedTupleSemantics.sourceVariables_tuple] using
      SignedTupleSemantics.full_result_eq (t := t)
        (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)
        earlier suffix tail split

theorem fold_tupleSteps_dataOfPrefix
    (xs : List (Fin width → Fin (NormalizedSourceInput.clauseCount input)))
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ xs.flatMap
      (fun indices => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) ++ suffix) :
    xs.foldl
        (fun data indices =>
          ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input indices data)
        (pack earlier tail) =
      pack (earlier ++ xs.flatMap
        (fun indices => localOrder
          (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices))) tail := by
  exact foldl_chunks_eq_prefix order
    (fun indices : Fin width → Fin (NormalizedSourceInput.clauseCount input) =>
      localOrder (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices))
    (ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input)
    (fun before => pack before tail)
    (fun indices before after hsplit =>
      tupleStep_dataOfPrefix rows repeats hn hbranch hrows δ input indices before after tail hsplit)
    xs earlier suffix split

end Semantics

noncomputable section ChronologicalCosts

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
    (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "Digits" => Fin width → Fin (NormalizedSourceInput.clauseCount input)
local notation "C" => CompletedSignedLaw.Completed (t := t) (NormalizedSourceInput.clauses input)
  rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "pack" => SignedTupleSemantics.dataOfPrefix
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "step" => ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input

variable {Extra : Type} [DecidableEq Extra]

theorem costsAtMost_of_chronological (extra : Extra → List Bool) (B : Nat) (tail : List Bool)
    (bounded : ∀ (indices : Digits) (before after : List C),
      order = before ++ localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) ++ after →
      ExactTargetOdometer.leafBudget rows repeats hn hbranch hrows δ input indices
        (pack before tail) extra ≤ B)
    (depth : Nat) (indices : Digits) (earlier suffix : List C)
    (split : order = earlier ++ (ExactTargetOdometer.visits depth indices).flatMap
      (fun tuple => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) tuple)) ++ suffix) :
    ExactTargetOdometer.CostsAtMost rows repeats hn hbranch hrows δ input extra B
      depth indices (pack earlier tail) := by
  let chunk : Digits → List C := fun tuple => localOrder
    (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) tuple)
  change order = earlier ++ (ExactTargetOdometer.visits depth indices).flatMap chunk ++ suffix at split
  induction depth generalizing indices earlier suffix with
  | zero =>
      change ExactTargetOdometer.leafBudget rows repeats hn hbranch hrows δ input indices
        (pack earlier tail) extra ≤ B
      apply bounded indices earlier suffix
      simpa only [ExactTargetOdometer.visits, List.flatMap_singleton, chunk] using split
  | succ depth ih =>
      intro value
      let beforeTuples : List Digits :=
        ((List.ofFn (fun a : Fin (NormalizedSourceInput.clauseCount input) => a)).take value.val).flatMap
          (fun a => ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth a))
      let afterTuples : List Digits :=
        ((List.ofFn (fun a : Fin (NormalizedSourceInput.clauseCount input) => a)).drop
          (value.val + 1)).flatMap
          (fun a => ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth a))
      have decomposition : ExactTargetOdometer.visits (depth + 1) indices =
          beforeTuples ++ ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth value) ++ afterTuples :=
        visits_split_at depth indices value
      have beforeSplit : order = earlier ++ beforeTuples.flatMap chunk ++
          ((ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth value)).flatMap chunk ++
              afterTuples.flatMap chunk ++ suffix) := by
        simpa only [decomposition, List.flatMap_append, List.append_assoc] using split
      have prefixState :
          ExactTargetOdometer.blockPrefix step depth indices value.val (pack earlier tail) =
            pack (earlier ++ beforeTuples.flatMap chunk) tail := by
        have folded := ExactTargetOdometer.fold_tupleSteps_dataOfPrefix
          rows repeats hn hbranch hrows δ input beforeTuples earlier
          ((ExactTargetOdometer.visits depth
            (ExactTargetOdometer.setCoordinate indices depth value)).flatMap chunk ++
              afterTuples.flatMap chunk ++ suffix) tail beforeSplit
        simpa only [beforeTuples, ExactTargetOdometer.blockPrefix,
          ExactTargetOdometer.foldVisits, List.foldl_flatMap] using folded
      rw [prefixState]
      apply ih (ExactTargetOdometer.setCoordinate indices depth value)
        (earlier ++ beforeTuples.flatMap chunk) (afterTuples.flatMap chunk ++ suffix)
      simpa only [decomposition, List.flatMap_append, List.append_assoc] using split

theorem costsAtMost_full (extra : Extra → List Bool) (B : Nat) (tail : List Bool)
    (bounded : ∀ (indices : Digits) (before after : List C),
      order = before ++ localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices) ++ after →
      ExactTargetOdometer.leafBudget rows repeats hn hbranch hrows δ input indices
        (pack before tail) extra ≤ B) :
    ExactTargetOdometer.CostsAtMost rows repeats hn hbranch hrows δ input extra B width
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) := by
  apply costsAtMost_of_chronological rows repeats hn hbranch hrows δ input extra B tail bounded
    width (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) [] []
  simpa only [List.nil_append, List.append_nil] using
    (ExactTargetOdometer.visits_completedOrder (t := t)
      (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)).symm

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

def timeBound (size : Nat) : Nat :=
  (SignedCostEnvelope.bodyCoeff width D + 2 * width) *
    (size + 1) ^ (SignedCostEnvelope.degree width + width)

end ChronologicalCosts
end PerfectCompleteness.ExactTargetOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildMarkedLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
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

abbrev Questions := SourceQuestionPositionSplit.Questions
  (branch := branch) (n := n) (t := t) (m := m)

abbrev Choice := SourceQuestionPositionSplit.ChildPositions (branch := branch) (n := n) (t := t)

def childSource (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    Source (m := m) (t := t) designated i :=
  SourceQuestionPositionSplit.join designated q (fun leaf k => z leaf.2 k) i

def questionSlots (q : Questions (branch := branch) (n := n) (t := t) (m := m)) :
    Slots branch (n + 1) → Fin t → MixedSupport.Slot :=
  sourceSlots clauses (PreliminarySampler.endpoints q)

theorem nativeSlots_childSource
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    nativeSlots clauses designated i (childSource designated q i z) =
      childSlots (questionSlots clauses q) i :=
  congrArg (fun slots => childSlots slots i)
    (SourceQuestionPositionSplit.parentLeftSlots_join clauses designated q (fun leaf k => z leaf.2 k))

def nativeEquiv (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    Native (C := C) (t := t) rows clauses designated i (childSource designated q i z) ≃
      CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
  Equiv.cast (congrArg (Block C rows) (nativeSlots_childSource clauses designated q i z))

def questionMarkedChild
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t))
    (raw : Raw (C := C) (t := t) rows clauses designated i) :
    Bool × CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
  (rawProjected rows clauses designated i raw,
    nativeEquiv rows clauses designated q i z
      (SourceChildNativeLaw.decodeLeft rows clauses designated i (childSource designated q i z) raw))

abbrev Marked (q : Questions (branch := branch) (n := n) (t := t) (m := m)) :=
  (Fin (branch n) → Bool) × CutChildGrouping.Raw (C := C) (questionSlots clauses q) rows

def markedBlocks (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (zs : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (raw : SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) :
    Marked (C := C) rows clauses q :=
  MarkedKernelProduct.markEquiv (fun i => questionMarkedChild rows clauses designated q i (zs i) (raw i))

abbrev Observation :=
  Σ q : Questions (branch := branch) (n := n) (t := t) (m := m),
    Marked (C := C) rows clauses q

def observe (sample : Sample (C := C) (t := t) rows clauses designated) :
    Observation (branch := branch) (n := n) (C := C) (t := t) rows clauses :=
  let grouped := SourceQuestionKernelJoint.groupEquiv rows clauses designated sample
  ⟨grouped.1.1, markedBlocks rows clauses designated grouped.1.1 grouped.1.2 grouped.2⟩

@[simp] theorem observe_mask
    (sample : Sample (C := C) (t := t) rows clauses designated) (i : Fin (branch n)) :
    (observe rows clauses designated sample).2.1 i =
      rawProjected rows clauses designated i (sample i).2.2 := rfl

end
end PerfectCompleteness.SourceChildMarkedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalHighEvent
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalHighEvent

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)
  (hbranch : ∀ k < n, 0 < branch k)

def highEvent (s : Nat) (x : CleanDecoderRate.Sample S)
    (answer : CleanPhysicalDecoderLaw.Answers
      (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x) upper) : Bool :=
  ProjectedFiberSquare.highMeeting
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
    (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1) hbranch d s
    answer.1 answer.2

end
end PerfectCompleteness.CleanPhysicalHighEvent

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalRawChildren
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalRawChildren

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

def fillChildren
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows :=
  fun i => CleanPhysicalReplay.fillChild rows repeats p outside inside i (children i)

end
end PerfectCompleteness.CleanPhysicalRawChildren

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalHighAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalHighAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev suffix := CleanRightDecoder.suffix upper (CleanPhysicalDecoderLaw.lower S)
  S.cut (CleanDecoderContext.lowerHeight upper d)

include S in
theorem suffix_proper : h + 1 < Nodes.height upper :=
  CleanRightDecoder.suffix_proper upper (CleanPhysicalDecoderLaw.lower S)
    S.cut (CleanDecoderContext.lowerHeight upper d)

variable (hbranch : ∀ k < n, 0 < branch k)
  (hnode : WholeArrayInteriorExterior.upperNode (CleanDecoderRate.path S) =
    HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  {Original : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Original slots)]
  (F : OriginalDecoderMark.Family branch rows n t Original) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (direction : BucketSampler.Direction (rows (h + 1))) (threshold : ℝ) (s : Nat)

abbrev nativeDirection :=
  (ProjectedFiberRawPair.direction (CleanDecoderRate.path S) upper (h + 1) d hnode direction).val

def tapeStatistic
    (left right : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (projection : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (tape : WholeCutSampler.Tape rows repeats (CleanDecoderRate.path S)
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right)) : ℝ :=
  LowerProjectedOriginalSuccess.kernelSuccess (repeats := repeats) (CleanDecoderRate.path S)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside left)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right)
    (CutProjectionAssembly.fillProjection (CleanDecoderRate.path S) S.outside left right projection)
    upper (h + 1) hbranch d hnode direction A S.cut σ
    (OriginalDecoderMark.mark F upper (h + 1) κ
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside left)) ρ threshold s
    (WholeCutSubtree.knownBucketsAtNode rows repeats
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right)
      upper (suffix S) (suffix_proper S) (LinearMap.ker A) tape)
    (WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S)
      (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside right) tape)

def childStatistic
    (left right : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (projection : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (children : CutChildGrouping.Raw (C := CleanDecoderRate.Calls S) right rows) : ℝ :=
  tapeStatistic S hbranch hnode F κ σ r ρ A direction threshold s left right projection
    (CleanPhysicalReplay.physicalTape rows repeats (CleanDecoderRate.path S)
      S.outside S.placeholder right S.exterior children)

def sourceStatistic
    (sources : SourceChildKernel.Sources (m := m) (t := t) S.designated)
    (observed : Σ flags : SourceProjectedTag.Flags (branch := branch) (n := h),
      CutChildGrouping.Raw (C := CleanDecoderRate.Calls S)
        (SourcePhysicalTaggedChildren.slots S.clauses S.designated sources flags) rows) : ℝ :=
  childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
    (SourceChildKernel.parentLeftSlots S.clauses S.designated sources)
    (SourcePhysicalTaggedChildren.slots S.clauses S.designated sources observed.1)
    (fun leaf k => SourceChildKernel.projection S.clauses S.designated leaf.1
      (sources leaf.1) (observed.1 leaf.1) leaf.2 k) observed.2

def questionStatistic
    (q : PreliminarySampler.Questions branch (h + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := h))
    (children : CutChildGrouping.Raw (C := CleanDecoderRate.Calls S)
      (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags) rows) : ℝ :=
  childStatistic S hbranch hnode F κ σ r ρ A direction threshold s
    (SourceProjectedTag.originalSlots S.clauses q)
    (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags)
    (SourceProjectedTag.projection S.clauses S.designated q choices flags) children

end
end PerfectCompleteness.CleanPhysicalHighAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalProjectedMeeting
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalProjectedMeeting

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] CleanPhysicalDecoderLaw.nativeLeftFintype RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev lower := CleanPhysicalDecoderLaw.lower S

def rawSample (W : Submodule F2 (Block rows upper)) (x : CleanDecoderRate.Sample S) :
    OwnInputReference.RawSample (CleanNativeReplay.rightSlots S x) rows upper (lower S) W repeats S.cut :=
  WholeArrayInteriorOwnInputLaw.exposedRead rows repeats (CleanNativeReplay.rightSlots S x)
    upper (lower S) S.cut W
    (CleanPhysicalDecoderLaw.uncastTape (CleanNativeReplay.rightSlots S x) upper (lower S) S.cut
      (CleanDecoderContext.lowerHeight upper d) (CleanPhysicalDecoderLaw.rightWholeTape S x))

abbrev visible (W : Submodule F2 (Block rows upper)) (x : CleanDecoderRate.Sample S) :=
  (rawSample S W x).2

variable {Sample : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch rows n t Sample) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Block rows (lower S)) (threshold : ℝ)

def visiblePairKernel (x : CleanDecoderRate.Sample S) :=
  (HierarchicalProjectedMeeting.leftLaw
    (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
    (CleanPhysicalDecoderLaw.physicalProjection S x) upper (h + 1)
    (HierarchicalProjectedRawPrediction.visibleBackground
      (CleanNativeReplay.leftSlots S x) (CleanNativeReplay.rightSlots S x)
      (CleanPhysicalDecoderLaw.physicalProjection S x) rows upper (lower S) A repeats S.cut
      (visible S (LinearMap.ker A) x))
    (F.original (CleanNativeReplay.leftSlots S x))
    (F.arrays (CleanNativeReplay.leftSlots S x))
    (F.lowerEvent (CleanNativeReplay.leftSlots S x)) κ σ ρ A
    (HierarchicalProjectedRawPrediction.known (CleanNativeReplay.rightSlots S x)
      rows upper (lower S) A repeats S.cut (visible S (LinearMap.ker A) x))).product
    (RightDecoder.law (CleanNativeReplay.rightSlots S x) rows upper (lower S)
      (LinearMap.ker A) a repeats S.cut σ
      (OwnInputReference.readInput (CleanNativeReplay.rightSlots S x) rows upper (lower S)
        (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval (CleanNativeReplay.rightSlots S x) upper (lower S)
          repeats S.cut) (visible S (LinearMap.ker A) x)) threshold)

end
end PerfectCompleteness.CleanPhysicalProjectedMeeting

end

end OAI
end


