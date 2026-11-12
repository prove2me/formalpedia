-- Prove2me | Definitions.Def_OAIQ252P002
-- name    : OAIQ252P002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:30:37.268132+00:00
-- url     : https://prove2.me/theorems/d0d86998-fb21-433f-b6c8-3eedf35e7f5e
-- title:
--   Definitions bundle OAIQ252P002 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1391 declarations of OpenAI's Lean: 756 definitions, 81 inductive types or structures, 50 instances and 504 theorems. The definitions and types are `OAI.PerfectCompleteness.BucketDescriptorLaw.reorder`, `OAI.PerfectCompleteness.ExactTargetOdometer.fillCoordinates`, `OAI.PerfectCompleteness.ExactTargetOdometer.setCoordinate`, `OAI.PerfectCompleteness.ExactTargetOdometer.visits`, `OAI.PerfectCompleteness.ExtraCutCall.middleSwap`, `OAI.PerfectCompleteness.ExtraCutCall.splitLast`, `OAI.PerfectCompleteness.FactoredFunctions.factoringSpace`, `OAI.PerfectCompleteness.FiniteProduct.factor`, `OAI.PerfectCompleteness.FixedBranching.cleanRate`, `OAI.PerfectCompleteness.FixedBranching.extend`, `OAI.PerfectCompleteness.FixedCallBudget.budget`, `OAI.PerfectCompleteness.FixedCallBudget.pairCount`, `OAI.PerfectCompleteness.FixedDecoderCleanRate.F2`, `OAI.PerfectCompleteness.FixedDecoderPairRate.F2`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.Alphabet`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.LocalLabel`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.Mode`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.State`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.Tape`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.localMain`, `OAI.PerfectCompleteness.FixedUnaryRepresentationMachine.localTape`, `OAI.PerfectCompleteness.FixedUnaryRepresentationPlacement.Alphabet`, `OAI.PerfectCompleteness.FixedUnaryRepresentationPlacement.Mode`, `OAI.PerfectCompleteness.FixedUnaryRepresentationPlacement.State`, `OAI.PerfectCompleteness.FixedUnaryRepresentationPlacement.Tape`, `OAI.PerfectCompleteness.FunctionSpaceLowerRank.transportForm`, `OAI.PerfectCompleteness.HiddenChildMixture.averageDensity`, `OAI.PerfectCompleteness.HierarchicalUsefulFamily.Sample`, `OAI.PerfectCompleteness.LevelPairCounting.winCount`, `OAI.PerfectCompleteness.LowerCrossRank.crossLinear`, `OAI.PerfectCompleteness.LowerCutAssembled.F2`, `OAI.PerfectCompleteness.LowerCutBucketLocality.F2`, `OAI.PerfectCompleteness.LowerCutPair.F2`, `OAI.PerfectCompleteness.MatrixErasure.erase`, `OAI.PerfectCompleteness.MatrixErasure.uniformMass`, `OAI.PerfectCompleteness.NormalizationEmitMachine.Alphabet`, `OAI.PerfectCompleteness.NormalizationEmitMachine.LocalLabel`, `OAI.PerfectCompleteness.NormalizationEmitMachine.LocalLabel.enumList`, `OAI.PerfectCompleteness.NormalizationEmitMachine.State`, `OAI.PerfectCompleteness.NormalizationEmitMachine.clean` and 797 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_FunctionSpaceLowerRank`, `PerfectCompleteness_Algebra_LowerCrossRank`, `PerfectCompleteness_Algebra_MatrixErasure`, `PerfectCompleteness_Algebra_RightDecoderAffineSuccess`, `PerfectCompleteness_Construction_FactoredFunctionsLemmas`, `PerfectCompleteness_Construction_HiddenChildMixture`, `PerfectCompleteness_Construction_OriginalChildBlockProducts`, `PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas`, `PerfectCompleteness_Construction_OriginalOwnBucketSplit`, `PerfectCompleteness_Decoding_CollisionAveragingLemmas`, `PerfectCompleteness_Decoding_CutGroupedProjectionLemmas`, `PerfectCompleteness_Decoding_FixedDecoderCleanRateLemmas`, `PerfectCompleteness_Decoding_LowerCutBucketLocality`, `PerfectCompleteness_Decoding_LowerCutPairLemmas`, `PerfectCompleteness_Decoding_LowerCutRowsLemmas`, `PerfectCompleteness_Decoding_RightDecoderWitness`, `PerfectCompleteness_Decoding_TwoResponseCollisionLemmas`, `PerfectCompleteness_Decoding_UpperScalarCutCalls`, `PerfectCompleteness_Decoding_UpperScalarFreshProjectionLemmas`, `PerfectCompleteness_Decoding_WholeCutGroupedProjection`, `PerfectCompleteness_Foundations_DualQuotientRowsLemmas`, `PerfectCompleteness_Foundations_ExtraCutCall`, `PerfectCompleteness_Foundations_FiniteProduct`, `PerfectCompleteness_Foundations_GlobalityLemmas`, `PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas`, `PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas`, `PerfectCompleteness_Foundations_NormalizationLemmas`, `PerfectCompleteness_Foundations_OddLists`, `PerfectCompleteness_Foundations_PartialTableInverse`, `PerfectCompleteness_Foundations_ProjectedCutChoices`, `PerfectCompleteness_Foundations_SignedCostEnvelope`, `PerfectCompleteness_Foundations_SignedTupleLayout`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Foundations_SourceTuplePlacement`, `PerfectCompleteness_Foundations_SourceTupleResetPlacementLemmas`, `PerfectCompleteness_Foundations_StoppedProjectedUsefulEvent`, `PerfectCompleteness_Foundations_TriangularFolding`, `PerfectCompleteness_Foundations_TupleIndexEmitterLemmas`, `PerfectCompleteness_Foundations_WholeCutCallsLemmas`, `PerfectCompleteness_Foundations_WholeCutExteriorTransportLemmas`, `PerfectCompleteness_Foundations_WholeCutReplayGroupingTransport`, `PerfectCompleteness_Machines_ExactTargetOdometer`, `PerfectCompleteness_Machines_FixedUnaryRepresentationMachine`, `PerfectCompleteness_Machines_NormalizationEmitMachine`, `PerfectCompleteness_Machines_NormalizationLoopMachine`, `PerfectCompleteness_Machines_NormalizationMachine`, `PerfectCompleteness_Machines_NormalizationReadMachine`, `PerfectCompleteness_Machines_OwnInputHeavyBounds`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Machines_SignedDescriptorStageMachine`, `PerfectCompleteness_Machines_SignedTupleBodyMachine`, `PerfectCompleteness_Machines_SignedTupleCleanupMachineLemmas`, `PerfectCompleteness_Machines_SourceClauseCountMachine`, `PerfectCompleteness_Machines_SourceClauseLookupMachine`, `PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas`, `PerfectCompleteness_Machines_SourceClauseSelectMachine`, `PerfectCompleteness_Machines_SourceCoordinateMachine`, `PerfectCompleteness_Machines_SourceOccurrenceIndexMachine`, `PerfectCompleteness_Machines_SourceOccurrenceLoopMachine`, `PerfectCompleteness_Machines_SourceOccurrenceMachine`, `PerfectCompleteness_Machines_SourceTupleMachine`, `PerfectCompleteness_Machines_StoppedCleanOwnInputGeometry`, `PerfectCompleteness_Machines_TargetFinalizeMachine`, `PerfectCompleteness_Machines_TargetHeaderMachine`, `PerfectCompleteness_Machines_TargetTapeEnvelope`, `PerfectCompleteness_Machines_TupleInitializationMachine`, `PerfectCompleteness_Machines_UnaryBlockCopyMachine`, `PerfectCompleteness_Machines_UnaryBlockSkipMachine`, `PerfectCompleteness_Machines_UnaryRepresentationMachine`, `PerfectCompleteness_Reduction_CompletionLemmas`, `PerfectCompleteness_Reduction_FixedCallBudgetLemmas`, `PerfectCompleteness_Reduction_NormalizedTargetInitialization`, `PerfectCompleteness_Repetition_RepetitionRateLemmas`, `PerfectCompleteness_Sampling_BucketDescriptorLaw`, `PerfectCompleteness_Sampling_OriginalCutBucketLaw`, `PerfectCompleteness_Sampling_RationalFiniteLawLemmas`, `PerfectCompleteness_Sampling_UniformDifference`, `PerfectCompleteness_Sampling_UniformLatentSupportLemmas`, `PerfectCompleteness_Sampling_WholeArrayBucketsLaw`, `PerfectCompleteness_Sampling_WholeArrayInteriorHiddenLaw`, `UniqueGames_Analysis_A13IndexLemmas`, `UniqueGames_Analysis_BadConvolution`, `UniqueGames_Analysis_CompressionCountLemmas`, `UniqueGames_Analysis_DegreeCover`, `UniqueGames_Analysis_DyadicError`, `UniqueGames_Analysis_FiberEnergyLemmas`, `UniqueGames_Analysis_Identities`, `UniqueGames_Analysis_MatrixCharactersLemmas`, `UniqueGames_Analysis_RestrictionTransport`, `UniqueGames_Analysis_SubspaceCountingLemmas`, `UniqueGames_Foundations_Basic`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_KernelSampling`, `UniqueGames_Foundations_LabelBound`, `UniqueGames_Foundations_PinskerLemmas`, `UniqueGames_Foundations_Rectangle`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Foundations_SharedProfiles`, `UniqueGames_Gadgets_QuotientLemmas`, `UniqueGames_Games_CompletedSamplingLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Games_FinishBoundsLemmas`, `UniqueGames_Games_MaskedVariation`, `UniqueGames_Games_Overlap`, `UniqueGames_Games_PartialRevealLemmas`, `UniqueGames_Games_SelectedCommonMarginalLemmas`, `UniqueGames_Games_SelectedInformationLemmas`, `UniqueGames_Games_SelectionSequence`, `UniqueGames_Games_Variation`, `UniqueGames_Machines_FinalCNFMachineLemmas`, `UniqueGames_Machines_FinalCNFOutputLemmas`, `UniqueGames_Machines_FinalCNFRowPlanLemmas`, `UniqueGames_Machines_FinalCNFTemplate`, `UniqueGames_Machines_GraphCounterFinish`, `UniqueGames_Machines_GraphCounterModel`, `UniqueGames_Machines_GraphCounterStartLemmas`, `UniqueGames_Machines_MachineAppendAt`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineCloudRankLemmas`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineExpanderFamily`, `UniqueGames_Machines_MachineExpanderFamilyLoop`, `UniqueGames_Machines_MachineExpanderRow`, `UniqueGames_Machines_MachineExpanderRowCleanup`, `UniqueGames_Machines_MachineExpanderRowEmitLemmas`, `UniqueGames_Machines_MachineExpanderTableLoop`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineExpanderTableRows`, `UniqueGames_Machines_MachineFiniteAlphabet`, `UniqueGames_Machines_MachineInitialHeaders`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLazyTable`, `UniqueGames_Machines_MachineLazyTableRuntime`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineLogCounter`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachineOverlayRows`, `UniqueGames_Machines_MachineOverlayTable`, `UniqueGames_Machines_MachinePaddingRowsLemmas`, `UniqueGames_Machines_MachinePortReindex`, `UniqueGames_Machines_MachineRegularDummyRow`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOriginalClean`, `UniqueGames_Machines_MachineRegularOriginalRow`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularTableTrace`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineRepeat`, `UniqueGames_Machines_MachineTableSplit`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUnaryAffineAt`, `UniqueGames_Machines_MachineUnaryEqualityBit`, `UniqueGames_Machines_MachineUnaryLessAtLemmas`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_Machines_PoweringGlobalEnumerationLemmas`, `UniqueGames_Machines_PoweringMachineEqualityField`, `UniqueGames_Machines_PoweringMachineFinish`, `UniqueGames_Machines_PoweringMachineInitialize`, `UniqueGames_Machines_PoweringMachineLoop`, `UniqueGames_Machines_PoweringMachineRelationLemmas`, `UniqueGames_Machines_PoweringMachineRow`, `UniqueGames_Machines_PoweringMachineRowBody`, `UniqueGames_Machines_PoweringPlanBudget`, `UniqueGames_PCP_Addresses`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetRetractionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AmplificationIteration`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_CloudRoundingLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_CompareLoop`, `UniqueGames_PCP_EmitRows`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_ExpanderTableEnumeration`, `UniqueGames_PCP_ExpandersLemmas`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_FinalTableFormula`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_Initialization`, `UniqueGames_PCP_InputLemmas`, `UniqueGames_PCP_MachineRawInitialTable`, `UniqueGames_PCP_PortTableLookup`, `UniqueGames_PCP_PoweringLabelsLemmas`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableLayout`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PoweringTablesLemmas`, `UniqueGames_PCP_PreprocessingLazyWords`, `UniqueGames_PCP_PreprocessingOverlayWords`, `UniqueGames_PCP_PreprocessingPaddingOffsets`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialMachineBody`, `UniqueGames_PCP_RawInitialMachineCleanup`, `UniqueGames_PCP_RawInitialMachineFinish`, `UniqueGames_PCP_RawInitialMachineLoop`, `UniqueGames_PCP_RawInitialMachineReadClause`, `UniqueGames_PCP_RawInitialMachineRows`, `UniqueGames_PCP_RawInitialMachineStart`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_RuntimeModel`, `UniqueGames_PCP_Setup`, `UniqueGames_PCP_ZigzagGraphsLemmas`, `UniqueGames_Reduction_FinalParametersLemmas`, `UniqueGames_Reduction_MachineTransducer`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P004`, `OAIQ252P005` and `OAIQ252P006`; the statement `OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision_eq`.
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

section
-- module Solutions.OAIQ252_PC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

/-- Restriction in the domain and quotient in the codomain, as actual
linear maps. This is the Fourier-frequency map of an affine restriction. -/
def compress (A : Submodule K V) (B : Submodule K W) (Y : W →ₗ[K] V) :
    B →ₗ[K] V ⧸ A := A.mkQ.comp (Y.comp B.subtype)

end UniqueGamesTheorem.Appendix.Level.LinearRank

end

section

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace UniqueGamesTheorem.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- Disjoint images prevent cancellation between the two map values. -/
theorem ker_add_of_disjoint (f g : W →ₗ[K] V)
    (h : Disjoint (LinearMap.range f) (LinearMap.range g)) :
    LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext w
  constructor
  · intro hw
    have hsum : f w + g w = 0 := hw
    have hf : f w = 0 := by
      apply Submodule.disjoint_def.mp h (f w)
      · exact ⟨w, rfl⟩
      · exact ⟨-w, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hsum).symm⟩
    have hg : g w = 0 := by simpa only [hf, zero_add] using hsum
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    change f w + g w = 0
    change f w = 0 at hf
    change g w = 0 at hg
    rw [hf, hg, add_zero]

variable [FiniteDimensional K W]

/-- The exact rank-additivity criterion used to define `X ⪯ Y` in Appendix A.1. -/
theorem finrank_add_eq_iff (f g : W →ₗ[K] V) :
    finrank K (LinearMap.range (f + g)) =
        finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ↔
      Disjoint (LinearMap.range f) (LinearMap.range g) ∧
        LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hfg := (f + g).finrank_range_add_finrank_ker
  have hker := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker g)
  constructor
  · intro hrank
    have hle := Submodule.finrank_mono (LinearMap.range_add_le f g)
    have himage := (LinearMap.range f).finrank_sup_add_finrank_inf_eq (LinearMap.range g)
    have hinf : finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K V) = 0 := by
      omega
    have hd : Disjoint (LinearMap.range f) (LinearMap.range g) := by
      exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)
    refine ⟨hd, ?_⟩
    have heq := ker_add_of_disjoint f g hd
    rw [heq] at hfg
    apply Submodule.eq_top_of_finrank_eq
    omega
  · rintro ⟨hd, htop⟩
    rw [ker_add_of_disjoint f g hd] at hfg
    rw [htop, finrank_top] at hker
    omega

/-- The left image is contained in the total image for a rank-additive pair. -/
theorem range_left_le_range_add (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.range f ≤ LinearMap.range (f + g) := by
  have hk := ((finrank_add_eq_iff f g).mp h).2
  intro v hv
  have hp : (v, (0 : V)) ∈ (LinearMap.range f).prod (LinearMap.range g) :=
    ⟨hv, Submodule.zero_mem _⟩
  rw [← LinearMap.range_prod_eq hk] at hp
  rcases hp with ⟨w, hw⟩
  have hwf : f w = v := congrArg Prod.fst hw
  have hwg : g w = 0 := congrArg Prod.snd hw
  refine ⟨w, ?_⟩
  change f w + g w = v
  rw [hwf, hwg, add_zero]

/-- The total kernel is contained in the left kernel for a rank-additive pair. -/
theorem ker_add_le_ker_left (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.ker (f + g) ≤ LinearMap.ker f := by
  rw [ker_add_of_disjoint f g ((finrank_add_eq_iff f g).mp h).1]
  exact inf_le_left

def RankBelow (X Y : W →ₗ[K] V) : Prop :=
  finrank K (LinearMap.range Y) =
    finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X))

omit [FiniteDimensional K W] in
theorem add_remainder (X Y : W →ₗ[K] V) : X + (Y - X) = Y := by
  rw [add_comm X, sub_add_cancel]

theorem range_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range X ≤ LinearMap.range Y := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using range_left_le_range_add X (Y - X) h'

theorem ker_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.ker Y ≤ LinearMap.ker X := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using ker_add_le_ker_left X (Y - X) h'

end UniqueGamesTheorem.Appendix.RankAdditivity

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_SubspaceCountingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace UniqueGamesTheorem.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

noncomputable def generators (S : Submodule K V) (k : ℕ)
    (h : finrank K S = k) : Fin k → V :=
  fun i => (Module.finBasisOfFinrankEq K S h i : V)

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

/-- Factor a map whose kernel contains `ker Y` and whose image lies in `range Y`
through the effective domain and codomain. -/
def quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y :=
  let f := (LinearMap.ker Y).liftQ X hker
  f.codRestrict (LinearMap.range Y) (fun q => himage (by
    rw [← Submodule.range_liftQ (LinearMap.ker Y) X hker]
    exact LinearMap.mem_range_self f q))

omit [Module.Finite K V] [Module.Finite K U] in
@[simp] theorem quotientImageMap_mk (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) (u : U) :
    (quotientImageMap Y X hker himage ((LinearMap.ker Y).mkQ u) : V) = X u := rfl

end UniqueGamesTheorem.Appendix.SubspaceCounting

end

section

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace UniqueGamesTheorem.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def horizontal (B : Submodule K V) : Submodule K (V × K) := B.prod ⊥
def hKernel (S : Submodule K (V × K)) : Submodule K V := S.comap (LinearMap.inl K V K)

def scalarMap {Q : Type*} [AddCommGroup Q] [Module K Q] (q : Q) : K →ₗ[K] Q where
  toFun t := t • q
  map_add' a b := add_smul a b q
  map_smul' a b := by change (a*b) • q = a • (b • q); exact mul_smul a b q

def extension (B : Submodule K V) (q : V ⧸ B) : Submodule K (V × K) :=
  LinearMap.ker (B.mkQ.comp (LinearMap.fst K V K) -
    (scalarMap q).comp (LinearMap.snd K V K))

theorem extension_mem (B : Submodule K V) (q : V ⧸ B) (x : V) (t : K) :
    (x,t) ∈ extension B q ↔ B.mkQ x = t • q := by
  change B.mkQ x - t • q = 0 ↔ _
  exact sub_eq_zero

theorem mkQ_eq_smul_iff (B : Submodule K V) (x v : V) (t : K) :
    B.mkQ x = t • B.mkQ v ↔ x - t • v ∈ B := by
  have he : B.mkQ (x-t•v) = B.mkQ x - t•B.mkQ v := by simp only [map_sub, map_smul]
  rw [← sub_eq_zero, ← he]
  change (x-t•v ∈ LinearMap.ker B.mkQ) ↔ _
  rw [Submodule.ker_mkQ]

@[simp] theorem hKernel_horizontal (B : Submodule K V) : hKernel (horizontal B) = B := by
  ext x
  change (x ∈ B ∧ (0:K) = 0) ↔ x ∈ B
  simp

@[simp] theorem hKernel_extension (B : Submodule K V) (q : V ⧸ B) : hKernel (extension B q) = B := by
  ext x
  change (x,0) ∈ extension B q ↔ x ∈ B
  rw [extension_mem, zero_smul]
  change (x ∈ LinearMap.ker B.mkQ) ↔ x ∈ B
  rw [Submodule.ker_mkQ]

theorem exists_one_extension (B : Submodule K V) (q : V ⧸ B) : ∃ v, (v,1) ∈ extension B q := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  exact ⟨v, (extension_mem B q v 1).mpr (by simpa only [one_smul] using hv)⟩

theorem eq_extension_of_one_mem (S : Submodule K (V × K)) (v : V)
    (hv : (v,1) ∈ S) : S = extension (hKernel S) ((hKernel S).mkQ v) := by
  ext p
  rcases p with ⟨x,t⟩
  rw [extension_mem, mkQ_eq_smul_iff]
  change (x,t) ∈ S ↔ (x-t•v,0) ∈ S
  have hz : (x-t•v,0) = (x,t)-t•(v,1) := by ext <;> simp
  rw [hz]
  constructor
  · intro hx; exact S.sub_mem hx (S.smul_mem t hv)
  · intro hx
    have h := S.add_mem hx (S.smul_mem t hv)
    simpa only [sub_add_cancel] using h

theorem eq_horizontal_of_no_one (S : Submodule K (V × K))
    (hn : ¬ ∃ v, (v,1) ∈ S) : S = horizontal (hKernel S) := by
  have last_zero : ∀ x t, (x,t) ∈ S → t = 0 := by
    intro x t hxt
    by_contra ht
    have h := S.smul_mem t⁻¹ hxt
    have h' : (t⁻¹ • x,1) ∈ S := by simpa [smul_eq_mul, ht] using h
    exact hn ⟨_,h'⟩
  ext p
  rcases p with ⟨x,t⟩
  change (x,t) ∈ S ↔ (x ∈ hKernel S ∧ t = 0)
  constructor
  · intro hp
    have ht := last_zero x t hp
    subst t
    exact ⟨hp,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact hx

theorem horizontal_ne_extension (A B : Submodule K V) (q : V ⧸ B) : horizontal A ≠ extension B q := by
  intro h
  obtain ⟨v,hv⟩ := exists_one_extension B q
  have hv' : (v,1) ∈ horizontal A := h.symm ▸ hv
  change v ∈ A ∧ (1:K) = 0 at hv'
  exact one_ne_zero hv'.2

theorem extension_injective (B : Submodule K V) : Function.Injective (extension B) := by
  intro q r h
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have hp : (v,1) ∈ extension B q := (extension_mem B q v 1).mpr (by simpa using hv)
  have hp' : (v,1) ∈ extension B r := h ▸ hp
  have hr := (extension_mem B r v 1).mp hp'
  simpa only [one_smul, hv] using hr

def encode : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) → Submodule K (V × K)
  | .inl B => horizontal B
  | .inr ⟨B,q⟩ => extension B q

theorem encode_injective : Function.Injective (encode (K:=K) (V:=V)) := by
  intro a b h
  cases a with
  | inl A =>
    cases b with
    | inl B =>
      have hAB : A = B := by simpa only [encode,hKernel_horizontal] using congrArg hKernel h
      subst B
      rfl
    | inr b =>
      rcases b with ⟨B,q⟩
      exact False.elim (horizontal_ne_extension A B q h)
  | inr a =>
    rcases a with ⟨A,q⟩
    cases b with
    | inl B => exact False.elim (horizontal_ne_extension B A q h.symm)
    | inr b =>
      rcases b with ⟨B,r⟩
      have hAB : A = B := by simpa only [encode,hKernel_extension] using congrArg hKernel h
      cases hAB
      have hqr : q = r := extension_injective A h
      cases hqr
      rfl

theorem encode_surjective : Function.Surjective (encode (K:=K) (V:=V)) := by
  intro S
  by_cases h : ∃ v, (v,1) ∈ S
  · obtain ⟨v,hv⟩ := h
    exact ⟨.inr ⟨hKernel S,(hKernel S).mkQ v⟩, (eq_extension_of_one_mem S v hv).symm⟩
  · exact ⟨.inl (hKernel S), (eq_horizontal_of_no_one S h).symm⟩

def splitEquiv : Submodule K (V × K) ≃ (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) :=
  (Equiv.ofBijective encode ⟨encode_injective,encode_surjective⟩).symm

def horizontalEquiv (B : Submodule K V) : B ≃ₗ[K] horizontal B where
  toFun b := ⟨((b:V),0),⟨b.property,rfl⟩⟩
  invFun p := ⟨p.val.1,p.property.1⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hp : p.val.2 = 0 := p.property.2
      exact hp.symm
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def extensionEquiv (B : Submodule K V) (q : V ⧸ B) (v : V) (hv : B.mkQ v = q) :
    (B × K) ≃ₗ[K] extension B q where
  toFun p := ⟨((p.1:V)+p.2•v,p.2), by
    apply (extension_mem B q _ _).mpr
    have hb : B.mkQ (p.1:V) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact p.1.property
    simp only [map_add,map_smul,hb,hv,zero_add]⟩
  invFun p := (⟨p.val.1-p.val.2•v, by
    apply (mkQ_eq_smul_iff B _ v _).mp
    rw [hv]
    exact (extension_mem B q _ _).mp p.property⟩,p.val.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((p.1:V)+p.2•v)-p.2•v = (p.1:V)
      exact add_sub_cancel_right _ _
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (p.val.1-p.val.2•v)+p.val.2•v = p.val.1
      exact sub_add_cancel _ _
    · rfl
  map_add' p r := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.1:V)+(r.1:V))+(p.2+r.2)•v =
        ((p.1:V)+p.2•v)+((r.1:V)+r.2•v)
      rw [add_smul]
      abel
    · rfl
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · change c•(p.1:V)+(c*p.2)•v = c•((p.1:V)+p.2•v)
      rw [smul_add,mul_smul]
    · rfl

local instance quotientFintype [Finite V] (B : Submodule K V) : Fintype (V ⧸ B) := by
  letI : Finite (V ⧸ B) := Finite.of_surjective B.mkQ B.mkQ_surjective
  exact Fintype.ofFinite _

def mobiusWeight (q : Nat) : Nat → ℤ
  | 0 => 1
  | n+1 => -(q:ℤ)^n * mobiusWeight q n

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem map_inverse (e : V ≃ₗ[K] W) (B : Submodule K V) :
    (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
  have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [← Submodule.map_comp,hc,Submodule.map_id]

def subspaceEquiv (e : V ≃ₗ[K] W) : Submodule K V ≃ Submodule K W where
  toFun B := B.map e.toLinearMap
  invFun C := C.map e.symm.toLinearMap
  left_inv := map_inverse e
  right_inv := map_inverse e.symm

def subspaceMapEquiv (e : V ≃ₗ[K] W) (B : Submodule K V) : B ≃ₗ[K] B.map e.toLinearMap where
  toFun b := ⟨e b,Submodule.mem_map.mpr ⟨b,b.property,rfl⟩⟩
  invFun c := ⟨e.symm c,by
    rcases Submodule.mem_map.mp c.property with ⟨b,hb,hbc⟩
    rw [← hbc]
    simpa using hb⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def coordinateSplit (n : Nat) :
    (Fin (n+1) → K) ≃ₗ[K] ((Fin n → K) × K) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp
  map_add' f g := rfl
  map_smul' c f := rfl

end
end UniqueGamesTheorem.Appendix.SubspaceExtensions

end

section

namespace UniqueGamesTheorem.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def lowerIntervalEquiv (I : Submodule 𝕜 V) :
    {A : Submodule 𝕜 V // A ≤ I} ≃ Submodule 𝕜 I where
  toFun A := A.val.comap I.subtype
  invFun B := ⟨B.map I.subtype, by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
    exact b.property⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val.comap I.subtype).map I.subtype = A.val
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      exact Submodule.mem_map.mpr ⟨⟨x, A.property hx⟩, hx, rfl⟩
  right_inv B := by
    change (B.map I.subtype).comap I.subtype = B
    ext b
    constructor
    · intro hb
      change (b : V) ∈ B.map I.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨c, hc, hcb⟩
      have h : c = b := Subtype.ext hcb
      simpa only [h] using hc
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩

open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance submoduleFinite [Finite V] : Finite (Submodule 𝕜 V) :=
  Finite.of_injective (fun S : Submodule 𝕜 V => (S : Set V)) SetLike.coe_injective

noncomputable def lowerWeightedTotal [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) : ℤ := by
  classical
  letI := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  exact ∑ A : {A : Submodule 𝕜 V // A ≤ I}, w (finrank 𝕜 A.val)

end UniqueGamesTheorem.Appendix.SubmoduleInterval

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_DegreeCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace UniqueGamesTheorem.Appendix.DegreeCover

abbrev F2 := ZMod 2
variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

@[simp] theorem binary_add_self (v : V) : v + v = 0 := by
  have h : (1 + 1 : F2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : F2 => c • v) h

@[simp] theorem binary_neg (v : V) : -v = v := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact binary_add_self v

end UniqueGamesTheorem.Appendix.DegreeCover

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_Identities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- The actual hybrid selector from Appendix A.1, for genuine linear maps. -/
def Hybrid (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) : Prop :=
  A ≤ LinearMap.range Y ∧ A.comap Y ≤ B

/-- The compressed dual frequency `Q_A Y|_B`. -/
def compress (Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    B →ₗ[K] (V ⧸ A) := A.mkQ.comp (Y.domRestrict B)

@[simp] theorem compress_apply (Y : W →ₗ[K] V) (A : Submodule K V)
    (B : Submodule K W) (b : B) : compress Y A B b = A.mkQ (Y b) := rfl

variable [FiniteDimensional K W]

/-- The precise right-hand pair selector of (A.5). -/
def A5PairSurvives (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W)
    (p : Submodule K V × Submodule K W) : Prop :=
  Hybrid Y p.1 p.2 ∧ Disjoint p.1 (LinearMap.range X) ∧
  p.1 ⊔ LinearMap.range X = A ∧ p.2 ⊔ LinearMap.ker X = ⊤ ∧
  p.2 ⊓ LinearMap.ker X = B ∧
  RankAdditivity.RankBelow (compress X p.1 p.2) (compress Y p.1 p.2)

/-! ## The unique selector in (A.4) -/

end UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.BinaryA4

open LinearIdentities

abbrev F2 := DegreeCover.F2

end UniqueGamesTheorem.Appendix.BinaryA4

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_CompressionCountLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

def factorViaRange {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    X.range →ₗ[K] T :=
  (X.ker.liftQ P hker).comp X.quotKerEquivRange.symm.toLinearMap

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def aToRange (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) : A →ₗ[K] X.range :=
  (A0.mkQ.comp A.subtype).codRestrict X.range (by
    intro a
    rw [hR]
    exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩)

end Generic

end UniqueGamesTheorem.Appendix.A4IndexCount

end

end

section

namespace UniqueGamesTheorem.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- A complement to the kernel maps isomorphically onto the range. -/
def complementRangeEquiv (X : E →ₗ[𝕜] F) (P : Submodule 𝕜 E)
    (hP : IsCompl X.ker P) : P ≃ₗ[𝕜] X.range :=
  (X.ker.quotientEquivOfIsCompl P hP).symm.trans X.quotKerEquivRange

/-- Codomain coordinates split the range off from a chosen complement. -/
def codomainEquiv (X : E →ₗ[𝕜] F) (C : Submodule 𝕜 F)
    (hC : IsCompl X.range C) : (X.range × C) ≃ₗ[𝕜] F :=
  X.range.prodEquivOfIsCompl C hC

end

end UniqueGamesTheorem.Appendix.CoordinateTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Uniformly normalized complex Fourier coefficient. -/
def fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  𝔼 x, f x * star (ψ x)

end FiniteGroup

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsBoolean (f : α → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

end UniqueGamesTheorem.Appendix.LevelInequality

end

section

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5Scalar

def positiveSum (q : ℝ) (n m k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    if 1 ≤ i + j + k then q ^ (i + j + k) else 0

end UniqueGamesTheorem.Appendix.A5Scalar

end

end

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

def fiber (result : α → β) (i j : α → ℕ) (b : β) (r s : ℕ) : Finset α :=
  Finset.univ.filter (fun a => result a = b ∧ i a = r ∧ j a = s)

end UniqueGamesTheorem.Appendix.A5WeightedReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_DyadicError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.DyadicError

def quarterSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1/4 : ℝ)^i

def quarterError (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if i=0 ∧ j=0 then 0 else (1/4 : ℝ)^(i+j)

def dyadicError (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
    if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))

end UniqueGamesTheorem.Appendix.DyadicError

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_BadConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The signed bad-convolution term of Appendix A.1.  The selector here is
the weak image/kernel selector, prior to its separate A.4 decomposition. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.BadConvolution
open scoped BigOperators
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*}
  [AddCommGroup W]
  [AddCommGroup V]

def mobius (i : ℕ) : ℝ := (-1:ℝ)^i * 2^(i.choose 2)

end UniqueGamesTheorem.Appendix.BadConvolution

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace Appendix.RestrictionTransport

open scoped BigOperators

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem exists_range_preimage (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (h : f.range ≤ g.range) (x : P) : ∃ y : Q, g y = f x := h ⟨x, rfl⟩

/-- The actual linear change of parameters between two injective presentations. -/
def sameRangeEquiv (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : P ≃ₗ[K] Q := by
  let fw (x : P) := Classical.choose (exists_range_preimage f g (le_of_eq h) x)
  let bw (y : Q) := Classical.choose (exists_range_preimage g f (le_of_eq h.symm) y)
  have hfw (x : P) : g (fw x) = f x :=
    Classical.choose_spec (exists_range_preimage f g (le_of_eq h) x)
  have hbw (y : Q) : f (bw y) = g y :=
    Classical.choose_spec (exists_range_preimage g f (le_of_eq h.symm) y)
  exact
    { toFun := fw
      invFun := bw
      left_inv := by
        intro x
        apply hf
        rw [hbw, hfw]
      right_inv := by
        intro y
        apply hg
        rw [hfw, hbw]
      map_add' := by
        intro x y
        apply hg
        simp only [map_add, hfw]
      map_smul' := by
        intro c x
        change fw (c • x) = c • fw x
        apply hg
        simp only [map_smul, hfw] }

end SameRange

end Appendix.RestrictionTransport

end

end UniqueGamesTheorem

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.Globality

noncomputable def energy {N : Type*} [Fintype N] (f : N → ℝ) : ℝ :=
  𝔼 n, f n ^ 2

noncomputable def restrictionEnergy {M N : Type*} [AddCommGroup M] [Fintype N]
    (f : M → ℝ) (ι : N → M) (T : M) : ℝ :=
  energy (fun n => f (T + ι n))

end UniqueGamesTheorem.Appendix.Globality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite prerequisites for Holenstein's consistent sampling argument (Lemma 5.2).

`firstAccepted` is an actual bounded rejection sampler on a shared finite list
of proposals. `first_union_common` proves its synchronization property.
The remaining theorems establish the exact overlap/union mass formulas and the
agreement lower bound used to analyze a first accepted shared proposal.

No infinite random process or locally computable embedding is asserted here.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

/-- Return the first proposal accepted by the given test, or report exhaustion. -/
def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

/-- Total variation for real-valued finite mass functions. Distribution
normalization is supplied explicitly in theorems that need it. -/
def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def unionMass (p q : α → ℝ) : ℝ := ∑ a, max (p a) (q a)

end FiniteWeights

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_FiniteTrialsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite probability mass of a bounded rejection process.

Each trial independently draws from a finite mass function `w`. Its first
accepted proposal is represented by `some proposal`; exhaustion is `none`.
The recursive definition exposes the one-step probability transition. We prove
normalization, nonnegativity, the exact survival probability, and an exact
agreement-event formula with the finite-truncation error.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

/-- Probability transition for a finite first-acceptance process. A successful
first trial contributes its own mass; a rejected first trial continues with
one fewer trial. -/
def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

/-- Probability that the first accepted proposal satisfies an additional test.
For two threshold samplers, take `accept = left || right` and `good = left && right`.
`first_union_common` gives deterministic agreement on this event. -/
def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-! A finite exact replacement for uniform real thresholds. A list of real
thresholds subdivides [0,1]. Each resulting interval is an atom with weight its
length. Every inserted threshold has exactly its stated acceptance mass. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

structure ThresholdInterval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

def splitPoint (I : ThresholdInterval) (t : ℝ) : ℝ := max I.lo (min t I.hi)

def splitLeft (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨I.lo, splitPoint I t, le_max_left _ _⟩

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def unitThresholdInterval : ThresholdInterval := ⟨0, 1, by norm_num⟩

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight] <;> ring) thresholds
  simpa [unitThresholdInterval] using h

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-!
Connect the rejection sampler's executable list recursion to exact finite
probabilities. `traceAverage` is a finite nested sum over independent proposals;
it introduces no assumed probability law. The main theorem computes the actual
mass of each output of `firstAccepted` under those nested sums.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

/-- Expectation over a length-n list of independent proposals with mass `w`.
This is defined directly as a finite nested weighted sum. -/
def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

variable [DecidableEq σ]

/-- Indicator of the first accepted proposal passing a second test. -/
def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Coordinate reindexing for actual finite distributions and repeated games.
The joint questions are iid across coordinates; coordinate-success events
need not be independent. Strategies permute each player's local questions
and answers, so the resulting strategies remain local.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

def reindexEquiv {ι κ Ω : Type*} (e : κ ≃ ι) : (ι → Ω) ≃ (κ → Ω) where
  toFun f := f ∘ e
  invFun g := g ∘ e.symm
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp

end FiniteDistribution

end UniqueGamesTheorem.Foundations.Games

end

end

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite product-reference entropy decomposition, including zero-probability fibers. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

end UniqueGamesTheorem.Foundations.Information

end

section

/-!
Conditional laws on finite spaces, with a normalized default on null rows.
The default remains a probability law when a new input law charges a row
that had zero probability in the original joint distribution.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_PinskerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A finite Pinsker inequality with a nonoptimal constant, sufficient for the
information bound used by Holenstein: TV(p,q)^2 ≤ D_nat(p || q).
The proof factors the L1 distance through square roots and uses log t ≤ t-1.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def hellingerSquared (p q : α → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Tensorization and conditioning for finite independent coordinates. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def coordinateMarginal (p : (ι → α) → ℝ) (i : ι) (a : α) : ℝ := by
  classical
  exact ∑ x, if x i = a then p x else 0

noncomputable def independentProduct (q : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, q i (x i)

theorem independentProduct_isProbability (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) :
    IsProbability (independentProduct q) := by
  classical
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ => (hq i).1 (x i))
  · simp only [independentProduct, ← Fintype.prod_sum, (hq _).2, Finset.prod_const_one]

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite side-information conditioning bound from tensorization and log-sum.
All zero likelihood rows have an explicit normalized fallback. -/
namespace UniqueGamesTheorem.Foundations.Information
open scoped BigOperators

noncomputable def posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ) (z : ℝ) : A → ℝ := by
  classical
  exact if 0 < z then posterior p e z else p

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FactorizationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite product algebra of dependency breaking.

Revealing one endpoint of each independently sampled question pair turns the
remaining question weight into a product of two separate functions, one for
each player. Further separate restrictions on the players' answers preserve
this product. The final theorem normalizes the displayed weights, rather than
assuming conditional independence as an abstract hypothesis.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

variable {X Y : Type*} [Fintype X] [Fintype Y]

def normalizedWeight (weight : X → ℝ) : X → ℝ :=
  fun x => weight x / ∑ x', weight x'

theorem normalizedWeight_isProbability (weight : X → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hmass : 0 < ∑ x, weight x) :
    (∀ x, 0 ≤ normalizedWeight weight x) ∧ (∑ x, normalizedWeight weight x) = 1 := by
  constructor
  · intro x
    exact div_nonneg (hweight x) hmass.le
  · simp only [normalizedWeight, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hmass.ne']

end

end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Replacing the input marginal of an actual conditional profile. -/
namespace UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open UniqueGamesTheorem.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def seedQuestionMarginal (p : X × (S × Y) → ℝ) : X × S → ℝ :=
  firstMarginal (fun z : (X × S) × Y => p (z.1.1, (z.1.2, z.2)))

theorem seedQuestionMarginal_isProbability (p : X × (S × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (seedQuestionMarginal p) := by
  apply firstMarginal_isProbability
  constructor
  · intro z
    exact hp.1 _
  · have h := hp.2
    simp only [Fintype.sum_prod_type] at h ⊢
    exact h

end
end UniqueGamesTheorem.Foundations.Repetition.ProfileCorrection

end

section

namespace UniqueGamesTheorem.Foundations.Repetition

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace KernelSampling

/-- A single seed supplies a full local table to each side. -/
abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

section Completion

variable {I A B S : Type*} [DecidableEq I]

/-- Restore the designated coordinate on every left table read. -/
def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

/-- Restore the designated coordinate on every right table read. -/
def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

end Completion

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite occurrence presentations used by the rounding/subdivision construction.
An occurrence has its own identifier: its endpoints need not be distinct and
different occurrences may have the same endpoints. The bipartite target records
injectivity of the pair of endpoints, which is precisely the required simplicity.
No hardness or analytic premise enters these structures.
-/

namespace UniqueGamesTheorem.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

end UniqueGamesTheorem.Explicit

end

section

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace UniqueGamesTheorem.Explicit

open scoped BigOperators

namespace Subdivision

variable {V E A : Type*}

/-- Original vertices and the middle vertices `q_e`. -/
abbrev Left (V E : Type*) := V ⊕ E

/-- Restrict any output labeling to the original vertices. -/
def restrict (a : Left V E → A) : V → A := fun v => a (Sum.inl v)

def extendLeft (g : OccurrenceGame V E A) (a : V → A) : Left V E → A :=
  Sum.elim a (fun e => a (g.source e))

@[simp] theorem restrict_extendLeft (g : OccurrenceGame V E A) (a : V → A) :
    restrict (extendLeft g a) = a := rfl

variable [DecidableEq A]

variable [Fintype E]

@[simp] theorem left_count [Fintype V] :
    Fintype.card (Left V E) = Fintype.card V + Fintype.card E := by
  simp [Left]

end Subdivision

end UniqueGamesTheorem.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_Variation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite total-variation operations used by the dependency-breaking argument.
All statements concern the displayed real weight functions. In particular,
conditioning rescales actual restricted weights, and kernels act by finite sums.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Applying a finite stochastic kernel, forgetting its input. -/
noncomputable def kernelPushforward (p : α → ℝ) (kernel : α → β → ℝ) : β → ℝ :=
  fun b => ∑ a, p a * kernel a b

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_MaskedVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact variation decomposition for the two choices of revealed endpoint.
The support of the actual reveal profiles makes both branch identities valid,
including zero-probability revealed endpoints. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedJoint (p : S × (X × Y) → ℝ) : (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  (if z.1.2 = Sum.inl z.2.1 then p (z.1.1, z.2) / 2 else 0) +
  (if z.1.2 = Sum.inr z.2.2 then p (z.1.1, z.2) / 2 else 0)

theorem sum_maskedJoint (p : S × (X × Y) → ℝ) :
    (∑ z, maskedJoint p z) = ∑ z, p z := by
  classical
  have hrow (s : S) (q : X × Y) :
      (∑ r : X ⊕ Y, maskedJoint p ((s,r),q)) = p (s,q) := by
    simp [maskedJoint]
  calc
    _ = ∑ s : S, ∑ r : X ⊕ Y, ∑ q : X × Y, maskedJoint p ((s,r),q) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ s : S, ∑ q : X × Y, p (s,q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp_rw [hrow]
    _ = _ := (Fintype.sum_prod_type _).symm

theorem maskedJoint_isProbability_iff (p : S × (X × Y) → ℝ) :
    Information.IsProbability (maskedJoint p) ↔ Information.IsProbability p := by
  classical
  constructor
  · intro h
    constructor
    · intro z
      have hp := h.1 ((z.1,Sum.inl z.2.1),z.2)
      simp [maskedJoint] at hp
      linarith
    · rw [← sum_maskedJoint]
      exact h.2
  · intro h
    constructor
    · intro z
      have hp : 0 ≤ p (z.1.1,z.2) / 2 := div_nonneg (h.1 _) (by norm_num)
      dsimp [maskedJoint]
      split_ifs <;> linarith
    · rw [sum_maskedJoint]
      exact h.2

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedInformationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Concrete selected-coordinate questions and answer labels for the
side-information inequality. The event is the actual repeated game's selected
success event. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

def mergeCoordinates {Ω : Type*} {n : Nat} (selected : Finset (Fin n))
    (fixed : selected → Ω) (remaining : {i : Fin n // i ∉ selected} → Ω) : Fin n → Ω :=
  fun i => if h : i ∈ selected then fixed ⟨i,h⟩ else remaining ⟨i,h⟩

def coordinateSplitEquiv {Ω : Type*} {n : Nat} (selected : Finset (Fin n)) :
    (Fin n → Ω) ≃ ((selected → Ω) × ({i : Fin n // i ∉ selected} → Ω)) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun x := mergeCoordinates selected x.1 x.2
  left_inv x := by funext i; simp [mergeCoordinates]
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

abbrev SelectedLabels (selected : Finset (Fin n)) :=
  (selected → A₁) × (selected → A₂)

def selectedQuestionTuple (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (Fin n → Q₁) × (Fin n → Q₂) :=
  (fun i => (mergeCoordinates selected fixed remaining i).1,
   fun i => (mergeCoordinates selected fixed remaining i).2)

abbrev SelectedInput (Q₁ Q₂ : Type*) {n : Nat} (selected : Finset (Fin n)) :=
  (selected → Q₁ × Q₂) × ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The selected-success likelihood factors into a fixed verifier check and
two separate tests on the local deterministic answers. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLocalAnswers {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q)
    (remaining : {i : Fin n // i ∉ selected} → Q) : selected → A :=
  fun i => strategy (mergeCoordinates selected fixed remaining) i.1

def selectedLocalTest {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) : ℝ := by
  classical
  exact if selectedLocalAnswers strategy selected fixed remaining = label then 1 else 0

theorem selectedLocalTest_nonnegative {Q A : Type*} (strategy : (Fin n → Q) → (Fin n → A))
    (selected : Finset (Fin n)) (fixed : selected → Q) (label : selected → A)
    (remaining : {i : Fin n // i ∉ selected} → Q) :
    0 ≤ selectedLocalTest strategy selected fixed label remaining := by
  classical
  unfold selectedLocalTest
  split <;> norm_num

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_PartialRevealLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Removing one independent reveal from the explicit product law. The
likelihood can be any function of the questions and outside data. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def mergeAt {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) : I → R :=
  fun i => if h : i = j then a else rest ⟨i,h⟩

omit [Fintype I] in
@[simp] theorem mergeAt_self {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) :
    mergeAt j a rest j = a := by simp [mergeAt]

omit [Fintype I] in
@[simp] theorem mergeAt_other {R : Type*} (j : I) (a : R)
    (rest : {i : I // i ≠ j} → R) (i : {i : I // i ≠ j}) :
    mergeAt j a rest i.1 = rest i := by simp [mergeAt, i.property]

def revealSplitEquiv (j : I) :
    ((T × (I → X ⊕ Y)) × (X × Y)) ≃
      (((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) × (X × Y)) where
  toFun z := (((z.1.1, fun i => z.1.2 i.1), z.1.2 j), z.2)
  invFun z := ((z.1.1.1, mergeAt j z.1.2 z.1.1.2), z.2)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        by_cases h : i = j <;> simp [mergeAt, h]
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          exact mergeAt_other j z.1.2 z.1.1.2 i
      · exact mergeAt_self j z.1.2 z.1.1.2
    · rfl

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The side-information estimate for the explicit coordinate marginals of
the selected-answer/reveal law, followed by removal of one reveal variable. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationEquiv (selected : Finset (Fin n)) :
    ((SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂)) ≃
    ((((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) × (Q₁ × Q₂)) where
  toFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  invFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The common data used by the two local simulators is the actual
selected-answer law with only the embedded coordinate's reveal removed. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem isProbability_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (hp : IsProbability p) :
    IsProbability (fun a => p (e a)) := by
  constructor
  · intro a
    exact hp.1 _
  · rw [e.sum_comp]
    exact hp.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

abbrev SelectedCommonData (selected : Finset (Fin n))
    (j : {i : Fin n // i ∉ selected}) :=
  ((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
    ({i : {i : Fin n // i ∉ selected} // i ≠ j} → Q₁ ⊕ Q₂)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Conditional common-data profiles, with their error measured against the
actual endpoint-reveal reference and the actual question marginal. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def leftCommonMarginal (p : S × (X × Y) → ℝ) : X × S → ℝ :=
  fun z => ∑ y, p (z.2,(z.1,y))

def leftCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : X → S → ℝ :=
  conditionalKernel (leftCommonMarginal p) fallback

def swapSeedLeft : (X × (S × Y)) ≃ (S × (X × Y)) where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! An actual finite probability rectangle implementing all thresholds from a
fixed finite list. The seed distribution is shared; each local acceptance test
depends only on its own density. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

theorem sum_div_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i) / c = ∑ i, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_LabelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

def goodLabel (left right : σ → Bool) (decode : σ → α) (a : α) (s : σ) : Bool :=
  (left s && right s) && decide (decode s = a)

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SharedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A single finite rectangle proposal law for two finite families of distributions.
The subdivision includes every density appearing in either family.  Consequently
the local samplers share a seed space independently of their particular inputs.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

open scoped BigOperators

noncomputable section

def profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) : List ℝ := by
  classical
  exact (Finset.univ.toList : List (κ × S)).map (fun ks => P ks.1 ks.2)

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def uniformRejectionRate (S : Type*) [Fintype S] : ℝ :=
  1 - 1 / (Fintype.card S : ℝ)

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Direct diagonal-overlap comparison for the finite correlated sampler.
All quantities are finite weight arrays; no reference sampler or embedding
claim is assumed. The final theorem consumes the per-label lower bound that
is proved for the actual finite threshold sampler in CorrelatedSampling.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Information

noncomputable def discountedCommonMass {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (t : X → ℝ) : ℝ :=
  ∑ z, min (p z) (min (a z) (b z)) / (1 + t z.1)

noncomputable def diagonalWeights {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) : X × S × S → ℝ := by
  classical
  exact fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0

theorem diagonalWeights_isProbability {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (hp : IsProbability p) : IsProbability (diagonalWeights p) := by
  classical
  constructor
  · intro z
    dsimp [diagonalWeights]
    split
    · exact hp.1 _
    · exact le_rfl
  · simpa [diagonalWeights, Fintype.sum_prod_type] using hp.2

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedCommonMarginalLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The common-data law has exactly the actual selected-event question marginal.
Removing the fair endpoint reveal and regrouping the outside data preserve
the embedded question pair. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealDataSplitEquiv (j : I) :
    (T × (I → X ⊕ Y)) ≃ ((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) where
  toFun z := ((z.1, fun i => z.2 i.1), z.2 j)
  invFun z := (z.1.1, mergeAt j z.2 z.1.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = j <;> simp [mergeAt, h]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact mergeAt_other j z.2 z.1.2 i
    · exact mergeAt_self j z.2 z.1.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationDataEquiv (selected : Finset (Fin n)) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ≃
      (((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
        ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-!
Actual local completions of the unused questions, conditioned on common data
and the player's own embedded question. The raw row factors are explicit
finite weights. Their normalization reconstructs the actual selected common
law, including zero rows. The fallback independently samples base marginal
questions and then inserts the local input at the embedded coordinate.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def completionTupleEquiv : (I → X × Y) ≃ ((I → X) × (I → Y)) where
  toFun u := (fun i => (u i).1, fun i => (u i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv u := by funext i; rfl
  right_inv z := by cases z; rfl

end LocalNormalization

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectionSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

/-- Insert a chosen unused coordinate while there are coordinates remaining. -/
noncomputable def nextSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if hs : S.card < n then insert (Classical.choose (witness S hs)) S else S

/-- A total sequence, constant after all `n` coordinates have been selected. -/
noncomputable def selectedSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) : Nat → Finset (Fin n)
  | 0 => ∅
  | m + 1 => nextSet Step witness (selectedSet Step witness m)

open UniqueGamesTheorem.Foundations.Games

end UniqueGamesTheorem.Foundations.Repetition.SelectionSequence

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_CompletedSamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite local completion after correlated sampling

One independent seed contains the original shared seed and two full response
tables. Its local reads give exactly the mixture of the requested completion
kernels. Applying those kernels contracts total variation. On a diagonal
target the same construction uses one common selected label.
-/

namespace UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- The independent original seed and two full local completion tables. -/
abbrev Seed (Γ X Y S U V : Type*) :=
  Γ × KernelSampling.Seed (X × S) (Y × S) U V

def left (sL : Γ → X → S) (seed : Seed Γ X Y S U V) (x : X) : U :=
  KernelSampling.readLeft seed.2 (x, sL seed.1 x)

def right (sR : Γ → Y → S) (seed : Seed Γ X Y S U V) (y : Y) : V :=
  KernelSampling.readRight seed.2 (y, sR seed.1 y)

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- Restore the left input coordinate even on completion tables of weight zero. -/
def coordinateLeft (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) : I → X :=
  KernelSampling.completedLeft j seed.2 (x, sL seed.1 x)

/-- Restore the right input coordinate even on completion tables of weight zero. -/
def coordinateRight (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) : I → Y :=
  KernelSampling.completedRight j seed.2 (y, sR seed.1 y)

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateLeft_preserves (j : I) (sL : Γ → X → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (x : X) :
    coordinateLeft j sL seed x j = x := by
  simp [coordinateLeft]

omit [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
@[simp] theorem coordinateRight_preserves (j : I) (sR : Γ → Y → S)
    (seed : Seed Γ X Y S (I → X) (I → Y)) (y : Y) :
    coordinateRight j sR seed y j = y := by
  simp [coordinateRight]

end CoordinateCompletion

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Gadgets_QuotientLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional uniformity by translation averaging

For uniform finite input, an equivariant output is uniform even conditional on
any shift-invariant observable.  The observable need not have a finite range.
The proof averages translations directly and therefore never divides by a
conditioning probability.  In particular it applies to the output difference
at a fixed perturbation, and to an independent finite noise choice.
-/

namespace UniqueGamesTheorem.Gadget

section

universe u v

/-- An equivariant finite stage, including its concrete finite noise sampler. -/
structure Stage (k : Type u) (B : Type v) [CommRing k]
    [AddCommGroup B] [Module k B] where
  Input : Type v
  Shift : Type v
  Noise : Type v
  [inputAdd : AddCommGroup Input]
  [inputModule : Module k Input]
  [shiftAdd : AddCommGroup Shift]
  [shiftModule : Module k Shift]
  [inputFinite : Finite Input]
  [shiftFinite : Finite Shift]
  [noiseFinite : Finite Noise]
  [noiseNonempty : Nonempty Noise]
  embed : Shift →ₗ[k] Input
  embed_injective : Function.Injective embed
  logical : Shift →ₗ[k] B
  logical_surjective : Function.Surjective logical
  output : Input → B
  equivariant : ∀ u h, output (u + embed h) = output u + logical h
  noise : Noise → Input

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end

/-!
# Actual lifts and their descendant restrictions

Every descendant lift is constructed by a linear section of the child image.
Its detection on the child noise implies detection by the parent family on
the actual embedded noise. The common parent family is chosen before the
child index; only the image section is chosen after that index is known.
-/

universe u v

end UniqueGamesTheorem.Gadget

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCompositionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

open Turing

section Block

variable {K Λ σ : Type} {N M : Nat}

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end Block

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

end UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

end

section

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

/-- Exactly `n` supplied body blocks and `n + 1` concrete guard transitions. -/
def totalSteps (cost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, cost r) + n + 1

@[simp] theorem totalSteps_zero (cost : Nat → Nat) : totalSteps cost 0 = 1 := by
  simp [totalSteps]

theorem totalSteps_succ (cost : Nat → Nat) (n : Nat) :
    totalSteps cost (n + 1) = (totalSteps cost n + cost n) + 1 := by
  simp only [totalSteps, Finset.sum_range_succ]
  omega

theorem totalSteps_le (cost : Nat → Nat) (n B : Nat)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    totalSteps cost n ≤ n * (B + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
    calc
      (∑ r ∈ Finset.range n, cost r) ≤ ∑ _r ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
      _ = n * B := by simp
  simpa only [totalSteps, Nat.mul_add, Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1

end UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_FinalParametersLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

theorem rate_bounds {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    0 < rate gap ∧ rate gap < 1 := by
  have hcube : gap ^ 3 ≤ 1 := pow_le_one₀ hgap.le hgap1
  have hcubePos : 0 < gap ^ 3 := pow_pos hgap _
  constructor <;> unfold rate <;> linarith

end UniqueGamesTheorem.Integration.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartialTableInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PartialTableInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Appendix.LevelInequality

variable {Ω Y : Type*} [Fintype Y]

def definedEquality (f : Ω → Option Y) (X X' : Ω) : ℝ :=
  if ∃ y, f X = some y ∧ f X' = some y then 1 else 0

end
end PerfectCompleteness.PartialTableInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def factor (i : I) (f : Ω i → ℝ) (j : I) (a : Ω j) : ℝ :=
  if h : j = i then f (h ▸ a) else 1

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_self (i : I) (f : Ω i → ℝ) (a : Ω i) :
    factor i f i a = f a := by simp [factor]

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_other (i j : I) (h : j ≠ i) (f : Ω i → ℝ) (a : Ω j) :
    factor i f j a = 1 := by simp [factor, h]

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_function_self (i : I) (f : Ω i → ℝ) :
    factor i f i = f := by funext a; exact factor_self i f a

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_function_other (i j : I) (h : j ≠ i) (f : Ω i → ℝ) :
    factor i f j = fun _ => 1 := by funext a; exact factor_other i j h f a

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_FactoredFunctionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FactoredFunctions

variable {𝕜 Ω Z I J : Type*} [Field 𝕜]

def factoringSpace (other : Ω → Z) : Submodule 𝕜 (Ω → 𝕜) where
  carrier := {f | ∀ x y, other x = other y → f x = f y}
  zero_mem' := by intro x y _; rfl
  add_mem' := by
    intro f g hf hg x y h
    change f x + g x = f y + g y
    rw [hf x y h, hg x y h]
  smul_mem' := by
    intro c f hf x y h
    change c • f x = c • f y
    rw [hf x y h]

@[simp] theorem mem_factoringSpace (other : Ω → Z) (f : Ω → 𝕜) :
    f ∈ factoringSpace other ↔ ∀ x y, other x = other y → f x = f y := Iff.rfl

end PerfectCompleteness.FactoredFunctions



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_TwoResponseCollisionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TwoResponseCollision

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def responds (f : Ω → Option Y) (good : Ω → Bool) (y : Y) (x : Ω) : Bool :=
  good x && decide (f x = some y)

def goodDefined (f : Ω → Option Y) (good : Ω → Bool) (x : Ω) : Bool :=
  good x && (f x).isSome

def GoodResponse (f : Ω → Option Y) (good : Ω → Bool) (y : Y) : Prop :=
  ∃ x, good x = true ∧ f x = some y

end
end PerfectCompleteness.TwoResponseCollision



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem replicate_append_cons (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineInitialHeaders

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_UnaryRepresentationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UnaryRepresentationMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

inductive RawLabel
  | scan | restore
  deriving DecidableEq

protected abbrev RawLabel.enumList : List RawLabel := [.scan, .restore]

protected theorem RawLabel.enumList_nodup : RawLabel.enumList.Nodup := by decide

instance instFintypeRawLabel : Fintype RawLabel where
  elems := ⟨RawLabel.enumList, RawLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive EncodedLabel
  | seed | copy | restore
  deriving DecidableEq

protected abbrev EncodedLabel.enumList : List EncodedLabel := [.seed, .copy, .restore]

protected theorem EncodedLabel.enumList_nodup : EncodedLabel.enumList.Nodup := by decide

instance instFintypeEncodedLabel : Fintype EncodedLabel where
  elems := ⟨EncodedLabel.enumList, EncodedLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def encodedToRawMain : RawLabel := .scan
def rawToEncodedMain : EncodedLabel := .seed

variable {K Λ A : Type} [DecidableEq K]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.UnaryRepresentationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineDrainManyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Tapes (K : Type) := K → List Bool
abbrev Data (K : Type) := Tapes K × Option Bool

def result (source : K) (data : Data K) : Data K :=
  (Function.update data.1 source [], none)

def cost (source : K) (data : Data K) : Nat := (data.1 source).length + 1

def finalTapes : List K → Tapes K → Tapes K
  | [], base => base
  | source :: chosen, base => finalTapes chosen (Function.update base source [])

def finalRegister : List K → Option Bool → Option Bool
  | [], register => register
  | _ :: _, _ => none

omit [DecidableEq K] in
@[simp] theorem finalRegister_none (chosen : List K) : finalRegister chosen none = none := by
  cases chosen <;> rfl

def steps : List K → Tapes K → Nat
  | [], _ => 0
  | source :: chosen, base => (base source).length + 1 +
      steps chosen (Function.update base source [])

/-- An executable complete cleanup list from an explicit finite enumeration. -/
def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FixedUnaryRepresentationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedUnaryRepresentationMachine


open Turing UniqueGamesTheorem.Foundations.Complexity

inductive Mode
  | encodedToRaw | rawToEncoded
  deriving DecidableEq

inductive Tape (width : Nat)
  | source (position : Fin width)
  | destination (position : Fin width)
  | scratch
  deriving DecidableEq, Fintype

abbrev Alphabet {width : Nat} (_ : Tape width) := Bool
abbrev State (A : Type) := A × Option Bool

def LocalLabel : Mode → Type
  | .encodedToRaw => UnaryRepresentationMachine.RawLabel
  | .rawToEncoded => UnaryRepresentationMachine.EncodedLabel

instance instFintypeLocalLabel (mode : Mode) : Fintype (LocalLabel mode) := by
  cases mode with
  | encodedToRaw => exact inferInstanceAs (Fintype UnaryRepresentationMachine.RawLabel)
  | rawToEncoded => exact inferInstanceAs (Fintype UnaryRepresentationMachine.EncodedLabel)

instance instDecidableEqLocalLabel (mode : Mode) : DecidableEq (LocalLabel mode) := by
  cases mode with
  | encodedToRaw => exact inferInstanceAs (DecidableEq UnaryRepresentationMachine.RawLabel)
  | rawToEncoded => exact inferInstanceAs (DecidableEq UnaryRepresentationMachine.EncodedLabel)

def localMain : (mode : Mode) → LocalLabel mode
  | .encodedToRaw => UnaryRepresentationMachine.encodedToRawMain
  | .rawToEncoded => UnaryRepresentationMachine.rawToEncodedMain

variable {width : Nat} {Λ A : Type}

def localTape (position : Fin width) : Fin 3 → Tape width
  | 0 => .source position
  | 1 => .scratch
  | 2 => .destination position

theorem localTape_injective (position : Fin width) :
    Function.Injective (localTape position) := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [localTape]

end PerfectCompleteness.FixedUnaryRepresentationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AssignmentTester
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AssignmentTester

open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

theorem truth_nonneg (b : Bool) : 0 ≤ truth b := by cases b <;> norm_num [truth]

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_xor_le (a b c d : Bool) :
    disagree (a ^^ b) (c ^^ d) ≤ disagree a c + disagree b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [disagree]

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

theorem four_truth_lower (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

theorem disagree_triangle (a b c : Bool) :
    disagree a c ≤ disagree a b + disagree b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

variable {K : Type*} [Fintype K] [Nonempty K]

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

end UniqueGamesTheorem.Foundations.PCP.AssignmentTester

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CodeComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CodeComposition

open scoped BigOperators

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_nonnegative (a b : Bool) : 0 ≤ disagreement a b := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_comm (a b : Bool) : disagreement a b = disagreement b a := by
  simp [disagreement, eq_comm]

theorem disagreement_triangle (a b c : Bool) :
    disagreement a c ≤ disagreement a b + disagreement b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagreement]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_nonnegative {X : Type*} [Fintype X] (f g : X → Bool) :
    0 ≤ relativeDistance f g :=
  Finset.expect_nonneg (fun _ _ => disagreement_nonnegative _ _)

theorem relativeDistance_comm {X : Type*} [Fintype X] (f g : X → Bool) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, disagreement_comm]

theorem relativeDistance_triangle {X : Type*} [Fintype X] (f g h : X → Bool) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  rw [relativeDistance, relativeDistance, relativeDistance,
    ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect (fun _ _ => disagreement_triangle _ _ _)

end UniqueGamesTheorem.Foundations.PCP.CodeComposition

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetReductionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Reindex

variable {W D B : Type*}

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

end Reindex

end UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_InitialGraphLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual indicator counting and the second-moment rejection estimate.
The hypotheses describe event inclusion and moment bounds, while the
Cauchy--Schwarz conclusion and all positivity properties are proved here. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_sq (p : Prop) : bit p ^ 2 = bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_mul (p q : Prop) : bit p * bit q = bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, hpq hp]
  · have hz : bit p = 0 := by simp [bit, hp]
    rw [hz]
    exact bit_nonneg q

theorem hits_nonneg {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ hits E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := Finset.expect_nonneg (fun ω _ => hf ω)

theorem mean_hits {I Ω : Type*} [Fintype I] [Fintype Ω] (E : I → Ω → Prop) :
    mean (hits E) = ∑ i, mean (fun ω => bit (E i ω)) := by
  exact Finset.expect_sum_comm _ _ _

theorem second_moment_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E : I → Ω → Prop) :
    mean (fun ω => hits E ω ^ 2) =
      ∑ i, ∑ j, mean (fun ω => bit (E i ω ∧ E j ω)) := by
  simp only [hits, pow_two, Finset.sum_mul, Finset.mul_sum, bit_mul,
    mean, Finset.expect_sum_comm]
  exact Finset.sum_comm

theorem mean_witness_sq_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω) :
    mean (hits W) ^ 2 ≤
      mean (fun ω => bit (reject ω)) * mean (fun ω => hits E ω ^ 2) := by
  classical
  have hNH (ω : Ω) : hits W ω ≤ hits E ω :=
    Finset.sum_le_sum (fun i _ => bit_mono (hWE i ω))
  have hzero (ω : Ω) (hr : ¬ reject ω) : hits W ω = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : ¬ W i ω := fun h => hr (hWR i ω h)
    simp [bit, hw]
  have hsupport (ω : Ω) : bit (reject ω) * hits W ω = hits W ω := by
    by_cases hr : reject ω
    · simp [bit, hr]
    · rw [hzero ω hr]
      simp
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => bit (reject ω)) (hits W)
  have hsquares : mean (fun ω => hits W ω ^ 2) ≤ mean (fun ω => hits E ω ^ 2) := by
    apply Finset.expect_le_expect
    intro ω _
    simpa only [pow_two] using
      (mul_le_mul (hNH ω) (hNH ω) (hits_nonneg W ω) (hits_nonneg E ω))
  calc
    _ ≤ mean (fun ω => bit (reject ω)) * mean (fun ω => hits W ω ^ 2) := by
      simpa only [mean, hsupport, bit_sq] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares
      (mean_nonneg _ (fun ω => bit_nonneg (reject ω)))

theorem rejection_lower_bound {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a ≤ mean (hits W))
    (hsecond : mean (fun ω => hits E ω ^ 2) ≤ b) :
    a ^ 2 / b ≤ mean (fun ω => bit (reject ω)) := by
  have hN : 0 ≤ mean (hits W) := mean_nonneg _ (hits_nonneg W)
  have hρ : 0 ≤ mean (fun ω => bit (reject ω)) :=
    mean_nonneg _ (fun ω => bit_nonneg (reject ω))
  have haSq : a ^ 2 ≤ mean (hits W) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfirst hfirst ha.le hN
  have hCS := mean_witness_sq_le E W reject hWE hWR
  apply (div_le_iff₀ hb).2
  exact haSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsecond hρ))

end UniqueGamesTheorem.Foundations.PCP.PoweringMoment

end

end

section

/-!
# The scalar bound for all positive error densities

The first lemma bounds a ratio using only a nonnegative coefficient bounded
by a positive cutoff. The second applies it to a positive natural count and
the first- and second-moment expressions in the powering argument.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringNumeric

/-- A bounded nonnegative coefficient gives the required ratio bound both
below and above the cutoff `1/t`. -/
theorem min_density_ratio (ε C k t : ℝ)
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 ≤ k)
    (ht : 0 < t) (hkt : k ≤ t) :
    min ε (1 / t) / (C + 1) ≤ ε / (C + k * ε) := by
  have hx : 0 ≤ min ε (1 / t) :=
    le_min hε.le (one_div_nonneg.mpr ht.le)
  have hxt : min ε (1 / t) * t ≤ 1 :=
    (le_div_iff₀ ht).mp (min_le_right ε (1 / t))
  have hkx : k * min ε (1 / t) ≤ 1 := by
    calc
      k * min ε (1 / t) ≤ t * min ε (1 / t) :=
        mul_le_mul_of_nonneg_right hkt hx
      _ ≤ 1 := by simpa only [mul_comm] using hxt
  have hC1 : 0 < C + 1 := by positivity
  have hden : 0 < C + k * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  apply (div_le_div_iff₀ hC1 hden).2
  calc
    min ε (1 / t) * (C + k * ε) =
        C * min ε (1 / t) + ε * (k * min ε (1 / t)) := by ring
    _ ≤ C * ε + ε * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left ε (1 / t)) hC.le)
        (mul_le_mul_of_nonneg_left hkx hε.le)
    _ = ε * (C + 1) := by ring

/-- A positive natural count supplies `0 ≤ m - 1`. After cancelling the
positive mass `m*ε`, the ratio of moments dominates a constant times
`min ε (1/t)`. No sign condition on `α` is needed for its fourth power. -/
theorem count_moment_ratio_lower (α ε C t : ℝ) (m : ℕ)
    (hm : 0 < m) (hε : 0 < ε) (hC : 0 < C) (ht : 0 < t)
    (hmt : (m : ℝ) - 1 ≤ t) :
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) ≤
      (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have hk : 0 ≤ (m : ℝ) - 1 := sub_nonneg.mpr hm1
  have hden : 0 < C + ((m : ℝ) - 1) * ε :=
    add_pos_of_pos_of_nonneg hC (mul_nonneg hk hε.le)
  have hαm : 0 ≤ α ^ 4 * (m : ℝ) := by positivity
  have hratio := min_density_ratio ε C ((m : ℝ) - 1) t hε hC hk ht hmt
  calc
    (α ^ 4 * (m : ℝ) / (C + 1)) * min ε (1 / t) =
        (α ^ 4 * (m : ℝ)) * (min ε (1 / t) / (C + 1)) := by ring
    _ ≤ (α ^ 4 * (m : ℝ)) * (ε / (C + ((m : ℝ) - 1) * ε)) :=
      mul_le_mul_of_nonneg_left hratio hαm
    _ = (α ^ 2 * (m : ℝ) * ε) ^ 2 /
        ((m : ℝ) * ε * (C + ((m : ℝ) - 1) * ε)) := by
      field_simp [ne_of_gt hm0, ne_of_gt hε, ne_of_gt hden]

end UniqueGamesTheorem.Foundations.PCP.PoweringNumeric

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringLabelsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Modal decoding is an actual maximum of finite empirical letter masses.
Its reciprocal-alphabet lower bound is derived from their total mass one. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty A] in
theorem mass_sum (opinion : Ω → A) : (∑ a, mass opinion a) = 1 := by
  classical
  calc
    (∑ a, mass opinion a) =
        (Finset.univ : Finset Ω).expect
          (fun ω => ∑ a : A, if opinion ω = a then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm (Finset.univ : Finset Ω) (Finset.univ : Finset A)
        (fun ω a => if opinion ω = a then (1 : ℝ) else 0)).symm
    _ = (Finset.univ : Finset Ω).expect (fun _ => (1 : ℝ)) := by
      apply Finset.expect_congr rfl
      intro ω _
      simp
    _ = 1 := Finset.expect_const Finset.univ_nonempty 1

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

omit [Nonempty Ω] in
theorem mode_max (opinion : Ω → A) (b : A) :
    mass opinion b ≤ mass opinion (mode opinion) :=
  Classical.choose_spec (exists_mode opinion) b

theorem mode_mass_lower (opinion : Ω → A) :
    1 / (Fintype.card A : ℝ) ≤ mass opinion (mode opinion) := by
  have hk : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (1 : ℝ) ≤ mass opinion (mode opinion) * (Fintype.card A : ℝ) := by
    calc
      (1 : ℝ) = ∑ a : A, mass opinion a := (mass_sum opinion).symm
      _ ≤ ∑ _a : A, mass opinion (mode opinion) :=
        Finset.sum_le_sum (fun a _ => mode_max opinion a)
      _ = mass opinion (mode opinion) * (Fintype.card A : ℝ) := by simp [mul_comm]
  exact (div_le_iff₀ hk).2 hsum

end UniqueGamesTheorem.Foundations.PCP.PoweringDecoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetRetractionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.SpectralReturn

open scoped BigOperators

noncomputable section

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

end

end UniqueGamesTheorem.Foundations.PCP.SpectralReturn

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_InputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

abbrev Alphabet (_ : K) := Bool

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

end

section

/-!
Concrete bridges between graph cardinality and the length of the validated
unary table encoding. These bounds supply the input-length and intermediate
encoding estimates used by actual machine trace composition; they are not
themselves a machine execution certificate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTableComplexity

open UniqueGamesTheorem.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

end UniqueGamesTheorem.Foundations.PCP.GraphTableComplexity

end

section

/-! Additive smoothing of the actual fair Boolean-tape length law.  This is
the finite-probability input to the lazy-walk amplification argument. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

theorem bitCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    bitCount x = (if x 0 then 1 else 0) + bitCount (fun i => x i.succ) := by
  exact Fin.sum_univ_succ _

theorem mean_congr {n : ℕ} {f g : ℕ → ℝ} (h : ∀ k, f k = g k) :
    binomialMean n f = binomialMean n g := by
  unfold binomialMean
  exact Finset.expect_congr rfl (fun x _ => h (bitCount x))

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

theorem mean_add (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k + g k) = binomialMean n f + binomialMean n g :=
  Finset.expect_add_distrib _ _ _

theorem mean_sub (n : ℕ) (f g : ℕ → ℝ) :
    binomialMean n (fun k => f k - g k) = binomialMean n f - binomialMean n g :=
  Finset.expect_sub_distrib _ _ _

theorem mean_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    binomialMean n (fun k => c * f k) = c * binomialMean n f := by
  exact (Finset.mul_expect Finset.univ (fun x : Fin n → Bool => f (bitCount x)) c).symm

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

theorem expect_bool (f : Bool → ℝ) : Finset.univ.expect f = (f false + f true) / 2 := by
  rw [Finset.expect_eq_sum_div_card]
  simp [Fintype.univ_bool, add_comm]

theorem mean_succ (n : ℕ) (g : ℕ → ℝ) :
    binomialMean (n + 1) g =
      (binomialMean n g + binomialMean n (fun k => g (k + 1))) / 2 := by
  unfold binomialMean
  rw [Fintype.expect_equiv (splitTape n)
    (fun x => g (bitCount x))
    (fun x => g ((if x.1 then 1 else 0) + bitCount x.2))
    (fun x => congrArg g (bitCount_succ x))]
  rw [← Finset.univ_product_univ, Finset.expect_product, expect_bool]
  simp [Nat.add_comm]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

theorem scoreMean_succ (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g =
      ((scoreMean n g + binomialMean n g) +
       (scoreMean n (fun k => g (k + 1)) -
        binomialMean n (fun k => g (k + 1)))) / 2 := by
  unfold scoreMean
  rw [mean_succ]
  have h₁ : (fun k => score (n + 1) k * g k) =
      (fun k => score n k * g k + g k) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (fun k => score (n + 1) (k + 1) * g (k + 1)) =
      (fun k => score n k * g (k + 1) - g (k + 1)) := by
    funext k
    simp only [score, Nat.cast_add, Nat.cast_one]
    ring
  rw [h₁, h₂, mean_add, mean_sub]

/-- Exact finite integration by parts for the fair Boolean-tape law. -/
theorem score_identity (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) / 2 *
      (binomialMean n g - binomialMean n (fun k => g (k + 1))) := by
  induction n generalizing g with
  | zero => simp [scoreMean_succ] <;> ring
  | succ n ih =>
    rw [scoreMean_succ, ih g, ih (fun k => g (k + 1))]
    simp only [mean_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem score_mean_zero (n : ℕ) : binomialMean n (score n) = 0 := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (fun _ => 1)
    simpa [scoreMean] using h

/-- The score variance is proved from the actual tape distribution. -/
theorem score_second_moment (n : ℕ) :
    binomialMean n (fun k => score n k ^ 2) = (n : ℝ) := by
  cases n with
  | zero => simp [score]
  | succ n =>
    have h := score_identity n (score (n + 1))
    have hd : binomialMean n (score (n + 1)) -
        binomialMean n (fun k => score (n + 1) (k + 1)) = 2 := by
      rw [← mean_sub]
      calc
        _ = binomialMean n (fun _ => 2) := by
          apply mean_congr
          intro k
          simp only [score, Nat.cast_add, Nat.cast_one]
          ring
        _ = 2 := mean_const _ _
    rw [hd] at h
    simpa [scoreMean, pow_two] using h

theorem score_difference (n : ℕ) (g : ℕ → ℝ) :
    scoreMean (n + 1) g = ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) := by
  rw [score_identity, mean_succ]
  ring

/-- Cauchy--Schwarz yields an adjacent-length bound without any support or
small-parameter caveat.  The square form avoids introducing square roots. -/
theorem adjacent_difference_sq (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    4 * ((n : ℝ) + 1) *
      (binomialMean n g - binomialMean (n + 1) g) ^ 2 ≤ 1 := by
  have hc : binomialMean (n + 1)
      (fun k => score (n + 1) k * (g k - 1 / 2)) = scoreMean (n + 1) g := by
    calc
      _ = binomialMean (n + 1) (fun k =>
          score (n + 1) k * g k - (1 / 2) * score (n + 1) k) := by
        apply mean_congr
        intro k
        ring
      _ = scoreMean (n + 1) g := by
        rw [mean_sub, mean_mul, score_mean_zero]
        simp [scoreMean]
  have hv : binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) ≤ 1 / 4 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro tape _
    have h₀ := (hg (bitCount tape)).1
    have h₁ := (hg (bitCount tape)).2
    have hp := mul_nonneg h₀ (sub_nonneg.mpr h₁)
    nlinarith
  have hcs : (binomialMean (n + 1)
        (fun k => score (n + 1) k * (g k - 1 / 2))) ^ 2 ≤
      binomialMean (n + 1) (fun k => score (n + 1) k ^ 2) *
        binomialMean (n + 1) (fun k => (g k - 1 / 2) ^ 2) :=
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [hc, score_difference, score_second_moment] at hcs
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hv (le_of_lt hn)
  simp only [Nat.cast_add, Nat.cast_one] at hcs
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem adjacent_difference_le (n : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean n g - binomialMean (n + 1) g| ≤ 1 / r := by
  have hs := adjacent_difference_sq n g hg
  have hd := sq_nonneg (binomialMean n g - binomialMean (n + 1) g)
  have hh := mul_le_mul_of_nonneg_right hrn hd
  rw [le_div_iff₀ hr]
  have ha := sq_abs (binomialMean n g - binomialMean (n + 1) g)
  have hp : 0 ≤ |binomialMean n g - binomialMean (n + 1) g| * r :=
    mul_nonneg (abs_nonneg _) (le_of_lt hr)
  nlinarith [sq_nonneg (|binomialMean n g - binomialMean (n + 1) g| * r - 1)]

theorem mean_shift_le (n d : ℕ) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrn : r ^ 2 ≤ 4 * ((n : ℝ) + 1)) :
    |binomialMean (n + d) g - binomialMean n g| ≤ (d : ℝ) / r := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hrnd : r ^ 2 ≤ 4 * ((n + d : ℕ) + 1 : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith
    have ha := adjacent_difference_le (n + d) g hg r hr hrnd
    rw [abs_sub_comm] at ha
    calc
      _ ≤ |binomialMean (n + d + 1) g - binomialMean (n + d) g| +
          |binomialMean (n + d) g - binomialMean n g| := abs_sub_le _ _ _
      _ ≤ 1 / r + (d : ℝ) / r := add_le_add ha ih
      _ = ((d + 1 : ℕ) : ℝ) / r := by push_cast <;> ring

theorem mean_ordered_difference_le (m n : ℕ) (hmn : m ≤ n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (r : ℝ) (hr : 0 < r)
    (hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1)) :
    |binomialMean n g - binomialMean m g| ≤ ((n - m : ℕ) : ℝ) / r := by
  simpa [Nat.add_sub_of_le hmn] using mean_shift_le m (n - m) g hg r hr hrm

theorem mean_window_le (N M m : ℕ) (hlo : N - M ≤ m) (hhi : m ≤ N + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (r : ℝ) (hr : 0 < r) (hbase : r ^ 2 ≤ 4 * (((N - M : ℕ) : ℝ) + 1)) :
    |binomialMean m g - binomialMean N g| ≤ (M : ℝ) / r := by
  by_cases hmN : m ≤ N
  · have hrm : r ^ 2 ≤ 4 * ((m : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
      linarith
    have h := mean_ordered_difference_le m N hmN g hg r hr hrm
    rw [abs_sub_comm] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : N - m ≤ M := by omega
    exact_mod_cast this
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmN)
    have hrN : r ^ 2 ≤ 4 * ((N : ℝ) + 1) := by
      have : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
      linarith
    have h := mean_ordered_difference_le N m hNm g hg r hr hrN
    refine h.trans (div_le_div_of_nonneg_right ?_ (le_of_lt hr))
    have : m - N ≤ M := by omega
    exact_mod_cast this

/-- A convenient square center for a fixed alphabet. -/
theorem square_window_le (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |binomialMean m g - binomialMean ((4 * q * M) ^ 2) g| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hR : (4 : ℝ) * M ≤ ((4 * q * M : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hRM : (M : ℝ) ≤ (((4 * q * M : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hMN : M ≤ (4 * q * M) ^ 2 := by exact_mod_cast hRM
  have hr : (0 : ℝ) < ((4 * q * M : ℕ) : ℝ) := by linarith
  have hb : (((4 * q * M : ℕ) : ℝ)) ^ 2 ≤
      4 * (((((4 * q * M) ^ 2 - M : ℕ)) : ℝ) + 1) := by
    rw [Nat.cast_sub hMN, Nat.cast_pow]
    nlinarith
  have h := mean_window_le ((4 * q * M) ^ 2) M m hlo hhi g hg
    ((4 * q * M : ℕ) : ℝ) hr hb
  have he : (M : ℝ) / ((4 * q * M : ℕ) : ℝ) = 1 / (4 * (q : ℝ)) := by
    push_cast
    have hq0 : (q : ℝ) ≠ 0 := by linarith
    have hM0 : (M : ℝ) ≠ 0 := by linarith
    field_simp
  rw [he] at h
  exact h

/-- A modal event of probability at least `1/q` retains probability `1/(2q)`
throughout the middle window used in lazy-walk powering. -/
theorem modal_transfer (q M m : ℕ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hlo : (4 * q * M) ^ 2 - M ≤ m) (hhi : m ≤ (4 * q * M) ^ 2 + M)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hmodal : 1 / (q : ℝ) ≤ binomialMean ((4 * q * M) ^ 2) g) :
    1 / (2 * (q : ℝ)) ≤ binomialMean m g := by
  have h := square_window_le q M m hq hM hlo hhi g hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hrec : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqR
  have he₁ : 1 / (4 * (q : ℝ)) = (1 / (q : ℝ)) / 4 := by ring
  have he₂ : 1 / (2 * (q : ℝ)) = (1 / (q : ℝ)) / 2 := by ring
  rw [he₁] at h
  rw [he₂]
  have hl := (abs_le.mp h).1
  linarith

end UniqueGamesTheorem.Foundations.PCP.LazySmoothing

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpandersLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Finite existence of the Cayley expander base

The sample space is the actual finite type of indexed Boolean-cube generators.
For each nonzero character, the checked sign sampling equivalence supplies its
uniform word law. A finite union bound then selects a generator family whose
nonconstant character biases are small. There is no random-graph hypothesis.

The fixed numbers below are manipulated symbolically; no enumeration of the
generator sample space is executed. The subsequent square-and-zigzag family
is a separate construction.
-/

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

namespace UniqueGamesTheorem.Foundations.PCP.LazySpectral

open SpectralReturn

variable {V D : Type*}

theorem half_sum_sq_le (a b : ℝ) : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (a - b)]

end UniqueGamesTheorem.Foundations.PCP.LazySpectral

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringReturn

open SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

def portConsEquiv (D : Type*) (n : Nat) :
    (D × (Fin n → D)) ≃ (Fin (n + 1) → D) where
  toFun z := Fin.cases z.1 z.2
  invFun r := (r 0, fun j => r j.succ)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      rfl
  right_inv r := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

end UniqueGamesTheorem.Foundations.PCP.PoweringReturn

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

end UniqueGamesTheorem.Foundations.PCP.PoweringMomentBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ZigzagGraphsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Energy contraction for the actual zigzag graph

The proof splits a function into its cloud average and its cloud-centered
part. All operators are the actual graph averages from `ZigzagGraphs`.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

open SpectralReturn

noncomputable section

variable {V D E : Type*}

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

end

end UniqueGamesTheorem.Foundations.PCP.ZigzagSpectral

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCeilingPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

open Turing
open UniqueGamesTheorem.Foundations.PCP

inductive Label
  | init | fuelFirst | fuelSecond | guard | copyFirst | copySecond
  | compare | restore | decide | scale | transfer | cleanup
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.init, .fuelFirst, .fuelSecond, .guard,
  .copyFirst, .copySecond, .compare, .restore, .decide, .scale, .transfer, .cleanup]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

def overflow (flag : Bool) (x p : Nat) : Bool := flag || decide (p < x)

theorem appendTrace {α : Type*} (f : α → α) {a b c : α} {s t : Nat}
    (hs : f^[s] a = b) (ht : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

def prefixTime (k p : Nat) : Nat := (1 + 2 * (k + 2)) + (k + min k p + 2) + 1

def coreTime (g k : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | f + 1, p => prefixTime k p +
      if k ≤ p then f + 2 else (p + g * p + 2) + coreTime g k f (p * g)

def roundBudget (g k : Nat) : Nat := (g + 8) * (k + 1) + 16

theorem prefixTime_le (k p : Nat) : prefixTime k p ≤ 4 * k + 8 := by
  have h := Nat.min_le_left k p
  unfold prefixTime
  omega

theorem prefixTime_le_roundBudget (g k p : Nat) : prefixTime k p ≤ roundBudget g k := by
  have h := prefixTime_le k p
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem continuingTime_le (g k p : Nat) (h : p < k) :
    prefixTime k p + (p + g * p + 2) ≤ roundBudget g k := by
  have hprefix := prefixTime_le k p
  have hmul := Nat.mul_le_mul_left g h.le
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

def totalTime (g k : Nat) : Nat := 1 + 2 * (k + 2) + coreTime g k k 1

def timeBound (g k : Nat) : Nat := (g + 8) * (k + 1) ^ 2 + 18 * (k + 1) + 3

/-- The bound is one fixed quadratic polynomial in the actual unary input
length. Its coefficient may depend on the fixed growth factor. -/
noncomputable def timePolynomial (g : Nat) : Polynomial Nat :=
  Polynomial.C (g + 8) * Polynomial.X ^ 2 + 18 * Polynomial.X + 3

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

open Turing
abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {Λ σ : Type}

/-- Specification only: equality of the original natural values, unless an
earlier step has already detected overflow. -/
def hit (flag : Bool) (x v : Nat) : Nat := if flag = false ∧ x = v then 1 else 0

inductive Label
  | copyFirst | copySecond | headerFirst | headerSecond | row | field | restore
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : Label :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

abbrev Row := Nat × List Nat

def rowWords (r : Row) : List Nat := r.1 :: r.2

def rowsHits (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => (if r.1 = v then 1 else 0) + rowsHits v rs

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

open Turing
open UniqueGamesTheorem.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/

inductive Label
  | init | countCode (l : MachineCloudCount.Label)
  | branch | powerCode (l : MachineCeilingPower.Label)
  | subtract | restore
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.FixedUnaryRepresentationPlacement


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineCloudPadding

abbrev Mode := FixedUnaryRepresentationMachine.Mode
abbrev Tape (width : Nat) := FixedUnaryRepresentationMachine.Tape width
abbrev State (A : Type) := A × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

end PerfectCompleteness.FixedUnaryRepresentationPlacement



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_LowerCrossRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LowerCrossRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section Evaluation

variable {K I N : Type*} [Field K] [Fintype I]
  [AddCommGroup N] [Module K N]

variable {J : Type*} [Fintype J]

def crossLinear (forms : I → Module.Dual K N) :
    (J → N) →ₗ[K] Matrix I J K where
  toFun y i j := forms i (y j)
  map_add' y z := by ext i j; exact map_add (forms i) (y j) (z j)
  map_smul' a y := by ext i j; exact map_smul (forms i) a (y j)

end Evaluation

end
end PerfectCompleteness.LowerCrossRank

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixErasure

noncomputable section

open scoped BigOperators Classical
open PerfectCompleteness.PartialTableInverse

variable {Ω Y : Type*}

def erase (f : Ω → Option Y) (T : Ω → Prop) (X : Ω) : Option Y :=
  if T X then none else f X

def uniformMass [Fintype Ω] (T : Ω → Prop) : ℝ :=
  𝔼 X, if T X then (1 : ℝ) else 0

@[simp] theorem erase_eq_none_of (f : Ω → Option Y) (T : Ω → Prop)
    {X : Ω} (hX : T X) : erase f T X = none := by
  simp [erase, hX]

end
end PerfectCompleteness.MatrixErasure

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DualQuotientRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.LevelPairCounting

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω : Type*} [Fintype Ω] {d : Nat}

def winCount (win : Fin d → Ω → Bool) (ω : Ω) : ℝ :=
  ∑ i, if win i ω then (1 : ℝ) else 0

end
end PerfectCompleteness.LevelPairCounting



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RationalFiniteLawLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSamplerBiasProducts

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

def pairTapeEquiv (R : Nat) (V : Type*) :
    ((Fin R × Bool) → V) ≃ (Fin R → V × V) where
  toFun x h := (x (h, false), x (h, true))
  invFun y hb := if hb.2 then (y hb.1).2 else (y hb.1).1
  left_inv x := by
    funext hb
    rcases hb with ⟨h, b⟩
    cases b <;> rfl
  right_inv y := by
    funext h
    rfl

end PerfectCompleteness.RecursiveSamplerBiasProducts



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddLists

open scoped BigOperators

variable {A B : Type*} {s : Nat}

section Supports

variable [Fintype A]

theorem binary_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact h x

end Supports

end PerfectCompleteness.OddLists

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_FunctionSpaceLowerRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FunctionSpaceLowerRank

noncomputable section

open scoped BigOperators Classical

section Transport

variable {K H V : Type*} [Field K]
  [AddCommGroup H] [Module K H] [AddCommGroup V] [Module K V]

def transportForm (e : H ≃ₗ[K] V) (F : H →ₗ[K] Module.Dual K H) :
    V →ₗ[K] Module.Dual K V :=
  e.symm.toLinearMap.dualMap.comp (F.comp e.symm.toLinearMap)

@[simp] theorem transportForm_apply (e : H ≃ₗ[K] V)
    (F : H →ₗ[K] Module.Dual K H) (u v : V) :
    transportForm e F u v = F (e.symm u) (e.symm v) := rfl

end Transport

end
end PerfectCompleteness.FunctionSpaceLowerRank

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HiddenChildMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HiddenChildMixture

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def averageDensity (q : (i : I) → Ω i → ℝ) (x : (i : I) → Ω i) : ℝ :=
  (∑ i, q i (x i)) / Fintype.card I

end
end PerfectCompleteness.HiddenChildMixture

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_RepetitionRateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RepetitionRate

open scoped BigOperators
open UniqueGamesTheorem.Foundations Games

def halfRate (L : Nat) : ℚ := 1 - 1 / (48000 * (L : ℚ))

end PerfectCompleteness.RepetitionRate



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

def tolerance (s : Nat) : ℚ := 1 / (2 * (s : ℚ) ^ 2)

theorem tolerance_positive (s : Nat) [NeZero s] : 0 < tolerance s := by
  have hs : (0 : ℚ) < s := Nat.cast_pos.mpr (Nat.pos_of_neZero s)
  unfold tolerance
  positivity

end
end PerfectCompleteness.SourceOddLists



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutCallsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OriginalCutCalls

open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

def count (rows repeats : Nat → Nat) (root cutoff : Nat) : Nat :=
  (2 ^ rows cutoff - 1) +
    ∑ h ∈ Finset.Ioc cutoff root, (2 ^ rows h - 1) *
      ∏ k ∈ Finset.Ioc cutoff h, 2 * repeats k

end
end PerfectCompleteness.OriginalCutCalls

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatentSupportLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSamplerBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open RecursiveSamplerBiasProducts

noncomputable section

universe u

variable {branch : Nat → Nat} {n m : Nat}

def RepetitionsBalanced (repeats : Nat → Nat) : Prop :=
  ∀ k : Nat, (7 / 8 : ℝ) ^ repeats (k + 1) ≤ 1 / 2

end
end PerfectCompleteness.RecursiveSamplerBias

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputHeavyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OwnInputHeavyBounds

open scoped TensorProduct Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.OwnInputHeavyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RightDecoderWitness

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end PerfectCompleteness.RightDecoderWitness

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_RightDecoderAffineSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RightDecoderAffineSuccess

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end PerfectCompleteness.RightDecoderAffineSuccess

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildBlockProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlockProducts

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

universe uC uI uΩ uΓ uΔ

def pairEquiv {I : Type uI} (Ω : I → Type uΩ) (Γ : I → Type uΓ) :
    ((i : I) → Ω i) × ((i : I) → Γ i) ≃ ((i : I) → Ω i × Γ i) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.OriginalChildBlockProducts

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TupleIndexEmitterLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TupleIndexEmitter

open Turing UniqueGamesTheorem.Foundations.Complexity

variable {width : Nat} {Extra σ : Type}

def prefixWords (d : Fin width → Nat) (r : Nat) (hr : r ≤ width) : List Nat :=
  List.ofFn (fun i : Fin r => d ⟨i.val, Nat.lt_of_lt_of_le i.isLt hr⟩)

@[simp] theorem prefixWords_zero (d : Fin width → Nat) :
    prefixWords d 0 (Nat.zero_le _) = [] := rfl

@[simp] theorem prefixWords_all (d : Fin width → Nat) :
    prefixWords d width (Nat.le_refl _) = List.ofFn d := by
  rfl

def prefixBudget (d : Fin width → Nat) (r : Nat) (hr : r ≤ width) : Nat :=
  ((prefixWords d r hr).map (fun n => 2 * (n + 2))).sum

@[simp] theorem prefixBudget_zero (d : Fin width → Nat) :
    prefixBudget d 0 (Nat.zero_le _) = 0 := rfl

@[simp] theorem prefixBudget_all (d : Fin width → Nat) :
    prefixBudget d width (Nat.le_refl _) = ∑ j, 2 * (d j + 2) := by
  simp only [prefixBudget, prefixWords_all, List.map_ofFn, Function.comp_def,
    List.sum_ofFn]

end PerfectCompleteness.TupleIndexEmitter



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def increment (current remaining : K) (doneLabel resetLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek remaining (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop remaining (fun state _ => (state.1, none))
        (.push current (fun _ => true) (.goto fun _ => doneLabel)))
      (.load (fun state => (state.1, none)) (.goto fun _ => resetLabel)))

section AscendingCycle

open scoped BigOperators

def cycleSteps (cost : ℕ → ℕ) (maximum count : ℕ) : ℕ :=
  (∑ r ∈ Finset.range (count + 1), cost r) + count + maximum + 2

theorem cycleSteps_zero (cost : ℕ → ℕ) (maximum : ℕ) :
    cycleSteps cost maximum 0 = (maximum + 2) + cost 0 := by
  simp [cycleSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem cycleSteps_succ (cost : ℕ → ℕ) (maximum count : ℕ) :
    cycleSteps cost maximum (count + 1) =
      (cycleSteps cost maximum count + 1) + cost (count + 1) := by
  simp only [cycleSteps, Finset.sum_range_succ]
  omega

end AscendingCycle

section Order

omit [DecidableEq K]

open scoped BigOperators

theorem tupleRank_snoc {n q : ℕ} (tail : Fin q → Fin n) (d : Fin n) :
    (finFunctionFinEquiv (Fin.snoc tail d)).val =
      (finFunctionFinEquiv tail).val + d.val * n ^ q := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

end Order

section Nested

open scoped BigOperators

/-- Explicit caller state and tape endpoints for one level of the nested
loop. Compatibility with its child schedules is checked by their types. -/
structure CycleSchedule (K σ : Type) where
  currentSuffix : List Bool
  remainingSuffix : List Bool
  ambient : ℕ → σ
  register : ℕ → Option Bool
  base : ℕ → K → List Bool

abbrev Configuration (K Λ σ : Type) :=
  TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool)

omit [DecidableEq K] in
/-- Exact concrete-counter overhead for a complete positive-radix nesting. -/
def counterOverhead (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => n * (counterOverhead n q + 2)

omit [DecidableEq K] in
theorem counterOverhead_le (n q : ℕ) (hn : 0 < n) :
    counterOverhead n q ≤ 2 * q * n ^ q := by
  induction q with
  | zero => simp [counterOverhead]
  | succ q ih =>
    have hp : 1 ≤ n ^ q := by apply Nat.one_le_pow; exact hn
    have h := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 2)
    have htwo : 2 ≤ 2 * n ^ q := Nat.mul_le_mul_left 2 hp
    have hinner : 2 * q * n ^ q + 2 ≤ 2 * (q + 1) * n ^ q := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    exact h.trans (by
      simpa only [counterOverhead, pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using Nat.mul_le_mul_left n hinner)

end Nested

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TupleInitializationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TupleInitializationMachine


open Turing UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def clean (ambient : σ) : State σ := (ambient, none)

inductive Label
  | seed
  | scan
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def prefixOn (destinations : List K) (addedBits : List Bool) (base : K → List Bool) :
    K → List Bool :=
  fun k => if k ∈ destinations then addedBits ++ base k else base k

@[simp] theorem prefixOn_nil (destinations : List K) (base : K → List Bool) :
    prefixOn destinations [] base = base := by
  funext k
  simp [prefixOn]

theorem prefixOn_comp (destinations : List K) (first second : List Bool)
    (base : K → List Bool) :
    prefixOn destinations first (prefixOn destinations second base) =
      prefixOn destinations (first ++ second) base := by
  funext k
  by_cases hk : k ∈ destinations <;> simp [prefixOn, hk, List.append_assoc]

theorem prefixOn_update (destinations : List K) (src : K)
    (hsrc : src ∉ destinations) (addedBits rest : List Bool) (base : K → List Bool) :
    prefixOn destinations addedBits (Function.update base src rest) =
      Function.update (prefixOn destinations addedBits base) src rest := by
  funext k
  by_cases hk : k = src
  · subst k
    simp [prefixOn, hsrc]
  · simp [prefixOn, hk]

def pushEach (destinations : List K) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  match destinations with
  | [] => next
  | dst :: rest => .push dst (fun _ => bit) (pushEach rest bit next)

theorem stepAux_pushEach (destinations : List K) (hn : destinations.Nodup) (bit : Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (state : State σ) (tapes : K → List Bool) :
    TM2.stepAux (pushEach destinations bit next) state tapes =
      TM2.stepAux next state (prefixOn destinations [bit] tapes) := by
  induction destinations generalizing tapes with
  | nil =>
    have emptyDest : prefixOn [] [bit] tapes = tapes := by
      funext k
      simp [prefixOn]
    simp only [pushEach, emptyDest]
  | cons dst rest ih =>
    obtain ⟨hdst, hrest⟩ := List.nodup_cons.mp hn
    simp only [pushEach, TM2.stepAux]
    rw [ih hrest]
    apply congrArg (TM2.stepAux next state)
    funext k
    by_cases hk : k = dst
    · subst k
      simp [prefixOn, hdst]
    · simp [prefixOn, hk]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun state => clean state.1)
    (match exit with | none => .halt | some label => .goto (fun _ => label))

theorem stepAux_finish (exit : Option Λ) (ambient : σ) (register : Option Bool)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) (ambient, register) tapes = ⟨exit, clean ambient, tapes⟩ := by
  cases exit <;> rfl

def initializedTapes (src : K) (currents remaining : List K) (base : K → List Bool)
    (last : Nat) (suffix : List Bool) : K → List Bool :=
  Function.update
    (prefixOn remaining (List.replicate last true)
      (prefixOn (currents ++ remaining) [false] base)) src suffix

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

@[simp] theorem initializedTapes_source (src : K) (currents remaining : List K)
    (base : K → List Bool) (last : Nat) (suffix : List Bool) :
    initializedTapes src currents remaining base last suffix src = suffix := by
  simp [initializedTapes]

end PerfectCompleteness.TupleInitializationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TriangularFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TriangularFolding

variable {A B X : Type*} [AddCommGroup A]

def translate (q : B → A) : A × B ≃ A × B where
  toFun y := (y.1 + q y.2, y.2)
  invFun y := (y.1 - q y.2, y.2)
  left_inv y := by ext <;> simp
  right_inv y := by ext <;> simp

@[simp] theorem translate_first (q : B → A) (y : A × B) :
    (translate q y).1 = y.1 + q y.2 := rfl

@[simp] theorem translate_second (q : B → A) (y : A × B) :
    (translate q y).2 = y.2 := rfl

end PerfectCompleteness.TriangularFolding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open UniqueGamesTheorem.Foundations.PCP

def encodeBit (b : Bool) : List Bool := if b then [true, false] else [false]

def encodeBits : List Bool → List Bool
  | [] => []
  | b :: bits => encodeBit b ++ encodeBits bits

@[simp] theorem encodeBits_append (xs ys : List Bool) :
    encodeBits (xs ++ ys) = encodeBits xs ++ encodeBits ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [encodeBits, ih, List.append_assoc]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CloudRoundingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudRounding

open scoped BigOperators

theorem dart_rejection_count_le
    {E V A : Type*} [Fintype E] [DecidableEq A]
    (tail : E → V) (reverse : E ≃ E) (accepts : E → A → A → Bool)
    (ell : E → A) (rounded : V → A) :
    (Finset.univ.filter (fun e =>
      accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)).card ≤
    (Finset.univ.filter (fun e => accepts e (ell e) (ell (reverse e)) = false)).card +
      2 * (Finset.univ.filter (fun e => ell e ≠ rounded (tail e))).card := by
  classical
  let R : Finset E := Finset.univ.filter (fun e =>
    accepts e (rounded (tail e)) (rounded (tail (reverse e))) = false)
  let B : Finset E := Finset.univ.filter (fun e =>
    accepts e (ell e) (ell (reverse e)) = false)
  let M : Finset E := Finset.univ.filter (fun e => ell e ≠ rounded (tail e))
  let MR : Finset E := Finset.univ.filter (fun e =>
    ell (reverse e) ≠ rounded (tail (reverse e)))
  have hrev : MR.card = M.card := by
    have hsets : MR = M.map reverse.symm.toEmbedding := by
      ext e
      constructor
      · intro he
        apply Finset.mem_map.mpr
        refine ⟨reverse e, ?_, reverse.symm_apply_apply e⟩
        simpa [MR, M] using he
      · intro he
        obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp he
        simpa [MR, M] using hd
    rw [hsets, Finset.card_map]
  have hsub : R ⊆ (B ∪ M) ∪ MR := by
    intro e he
    by_cases hl : ell e = rounded (tail e)
    · by_cases hr : ell (reverse e) = rounded (tail (reverse e))
      · have hb : e ∈ B := by simpa [B, R, hl, hr] using he
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
      · exact Finset.mem_union_right _ (by simp [MR, hr])
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [M, hl]))
  change R.card ≤ B.card + 2 * M.card
  calc
    R.card ≤ ((B ∪ M) ∪ MR).card := Finset.card_le_card hsub
    _ ≤ (B ∪ M).card + MR.card := Finset.card_union_le _ _
    _ ≤ (B.card + M.card) + MR.card :=
      Nat.add_le_add_right (Finset.card_union_le B M) _
    _ = B.card + 2 * M.card := by rw [hrev]; omega

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

omit [DecidableEq X] in
theorem majority_maximal (ell : X → A) [Nonempty A] (a : A) :
    (colorSet ell a).card ≤ (colorSet ell (majority ell)).card :=
  Classical.choose_spec (exists_max_color ell) a

omit [Fintype A] in
/-- Every nonchosen color occupies at most half the cloud. -/
theorem nonchosen_color_twice_le (ell : X → A) (m : A)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (a : A) (ha : a ≠ m) :
    2 * (colorSet ell a).card ≤ Fintype.card X := by
  have hd : Disjoint (colorSet ell a) (colorSet ell m) := by
    apply Finset.disjoint_left.mpr
    intro x hx hm
    have hxa : ell x = a := by simpa [colorSet] using hx
    have hxm : ell x = m := by simpa [colorSet] using hm
    exact ha (hxa.symm.trans hxm)
  have hu : (colorSet ell a).card + (colorSet ell m).card ≤ Fintype.card X := by
    calc
      _ = (colorSet ell a ∪ colorSet ell m).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  have hm := maximal a
  omega

def minorityEquiv (ell : X → A) (m : A) :
    (Σ a : Nonmajor m, ↥(colorSet ell a.val)) ≃ ↥(minoritySet ell m) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val = t.1.val := (Finset.mem_filter.mp t.2.property).2
    have hn : ell t.2.val ≠ m := fun h => t.1.property (hc.symm.trans h)
    simpa [minoritySet] using hn⟩
  invFun x :=
    ⟨⟨ell x.val, by simpa [minoritySet] using x.property⟩,
      ⟨x.val, by simp [colorSet]⟩⟩
  left_inv t := by
    rcases t with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    have hxa : ell x = a := by simpa [colorSet] using hx
    cases hxa
    rfl
  right_inv x := by apply Subtype.ext; rfl

omit [DecidableEq X] in
theorem minority_card_eq_sum (ell : X → A) (m : A) :
    (minoritySet ell m).card = ∑ a : Nonmajor m, (colorSet ell a.val).card := by
  have h := Fintype.card_congr (minorityEquiv ell m)
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h.symm

/-- The tail label determines the forgotten minority color. -/
def minorityCutEmbedding (ell : X → A) (next : X × D → X) (m : A) :
    (Σ a : Nonmajor m, ↥(directedCut next (colorSet ell a.val))) ↪
      ↥(disagreementSet ell next) where
  toFun t := ⟨t.2.val, by
    have hc : ell t.2.val.1 = t.1.val ∧ ell (next t.2.val) ≠ t.1.val := by
      simpa [directedCut, colorSet] using t.2.property
    have hn : ell t.2.val.1 ≠ ell (next t.2.val) :=
      fun h => hc.2 (h.symm.trans hc.1)
    simpa [disagreementSet] using hn⟩
  inj' p q h := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    rcases q with ⟨⟨b, hb⟩, ⟨y, hy⟩⟩
    have hxy : x = y := congrArg Subtype.val h
    cases hxy
    have hxa : ell x.1 = a := by
      have hc : ell x.1 = a ∧ ell (next x) ≠ a := by
        simpa [directedCut, colorSet] using hx
      exact hc.1
    have hxb : ell x.1 = b := by
      have hc : ell x.1 = b ∧ ell (next x) ≠ b := by
        simpa [directedCut, colorSet] using hy
      exact hc.1
    have hab : a = b := hxa.symm.trans hxb
    cases hab
    rfl

theorem minority_cut_sum_le (ell : X → A) (next : X × D → X) (m : A) :
    (∑ a : Nonmajor m, (directedCut next (colorSet ell a.val)).card) ≤
      (disagreementSet ell next).card := by
  have h := Fintype.card_le_of_injective
    (minorityCutEmbedding ell next m) (minorityCutEmbedding ell next m).injective
  simpa only [Fintype.card_sigma, Fintype.card_coe] using h

/-- Sum genuine directed-cut expansion over the nonchosen color classes. -/
theorem minority_expansion_bound (ell : X → A) (next : X × D → X) (m : A)
    (h : ℚ)
    (maximal : ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card)
    (expansion : ∀ S : Finset X, S.card ≤ Fintype.card X / 2 →
      h * (S.card : ℚ) ≤ ((directedCut next S).card : ℚ)) :
    h * ((minoritySet ell m).card : ℚ) ≤ ((disagreementSet ell next).card : ℚ) := by
  have each (a : Nonmajor m) :
      h * ((colorSet ell a.val).card : ℚ) ≤
        ((directedCut next (colorSet ell a.val)).card : ℚ) := by
    apply expansion
    have ha := nonchosen_color_twice_le ell m maximal a.val a.property
    omega
  calc
    h * ((minoritySet ell m).card : ℚ) =
        ∑ a : Nonmajor m, h * ((colorSet ell a.val).card : ℚ) := by
      rw [minority_card_eq_sum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ a : Nonmajor m, ((directedCut next (colorSet ell a.val)).card : ℚ) :=
      Finset.sum_le_sum (fun a _ => each a)
    _ ≤ ((disagreementSet ell next).card : ℚ) := by
      exact_mod_cast minority_cut_sum_le ell next m

end CloudCounts

end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

/-!
# Actual graph data consumed by the powered-row machine

The data fields are computed from the stored rotor and base relations. The
endpoint masks compare actual bounded word endpoints, in `allAddresses` order.
Their first true positions equal the already checked canonical address indices.

Reversing a row swaps the two masks and transposes each base predicate. Thus
one fixed row machine handles both directions. Its label lookup depends only
on the fixed degree and radius. The final identities describe the exact unary
input fields and the exact serialized relation emitted for a stored output row.

These are semantic producer-to-emitter identities. A machine implementation
that computes the input data from the serialized rotor is a separate frontend.
-/

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

open UniqueGamesTheorem.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

/-- The actual ports before a selected time, with no vertex-dependent choice. -/
def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

/-- Static commands; all changing vertex identifiers remain inputs to evaluation. -/
inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

/-- The number of shared trajectory tapes needed by a single instruction. -/
def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

end UniqueGamesTheorem.Foundations.PCP.PoweringFieldPlan

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

open UniqueGamesTheorem.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

end UniqueGamesTheorem.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringTableSemanticsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open SpectralReturn PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

theorem le_center (q M : Nat) (hq : 1 ≤ q) (hM : 1 ≤ M) : M ≤ center q M := by
  have hfour : 1 ≤ 4 * q := by omega
  have hx : M ≤ 4 * q * M := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right M hfour
  have hone : 1 ≤ 4 * q * M := hM.trans hx
  have hsquare : 4 * q * M ≤ (4 * q * M) * (4 * q * M) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * q * M) hone
  exact hx.trans (by simpa only [center, pow_two] using hsquare)

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

end UniqueGamesTheorem.Foundations.PCP.PoweringSoundness

namespace UniqueGamesTheorem.Foundations.PCP.PoweringGap

open SpectralReturn PoweringSoundness

variable {V D A : Type*}

theorem gain_nonneg (q M : Nat) (lambda : ℝ) (hlambda : lambda < 1) :
    0 ≤ gain q M lambda := by
  have hden : 0 < 1 - lambda := sub_pos.mpr hlambda
  unfold gain
  positivity

end UniqueGamesTheorem.Foundations.PCP.PoweringGap

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/
namespace UniqueGamesTheorem.Foundations.PCP.SpectralCut

open scoped BigOperators
open SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

omit [Fintype V] in
theorem indicator_nonnegative (S : Finset V) (v : V) : 0 ≤ indicator S v := by
  unfold indicator
  split_ifs <;> norm_num
end Indicators

end UniqueGamesTheorem.Foundations.PCP.SpectralCut

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetGraphLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem expect_prod {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 z : I × J, f z) = 𝔼 i : I, 𝔼 j : J, f (i, j) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset I) (Finset.univ : Finset J) f

theorem expect_rejection_eq_count {I : Type*} [Fintype I] (b : I → Bool) :
    (𝔼 i : I, AssignmentTester.truth (!(b i))) =
      ((Finset.univ.filter (fun i => b i = false)).card : ℝ) / Fintype.card I := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  calc
    (∑ i : I, AssignmentTester.truth (!(b i))) = ∑ i : I, if b i = false then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> norm_num [AssignmentTester.truth]
    _ = _ := Finset.sum_boole _ _

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

end

/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetTableBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.NormalizationWords


open UniqueGamesTheorem.Foundations
open Complexity

abbrev Signs := Fin 3 → Bool
abbrev Names := Fin 3 → Nat

inductive NameRef
  | old (slot : Fin 3)
  | fresh (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive SignRef
  | source (slot : Fin 3)
  | constant (sign : Bool)
  deriving DecidableEq, Fintype

structure LiteralRecipe where
  name : NameRef
  sign : SignRef
  deriving DecidableEq, Fintype

def sourceValue (names : Names) (freshBase : Nat) : NameRef → Nat
  | .old i => names i
  | .fresh _ => freshBase

def offset : NameRef → Nat
  | .old _ => 0
  | .fresh i => i.val

def nameValue (names : Names) (freshBase : Nat) (name : NameRef) : Nat :=
  sourceValue names freshBase name + offset name

def signValue (signs : Signs) : SignRef → Bool
  | .source i => signs i
  | .constant sign => sign

def literalWords (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) : List Nat :=
  [nameValue names freshBase literal.name, if signValue signs literal.sign then 1 else 0]

def mainRecipe : List LiteralRecipe :=
  [⟨.fresh 0, .source 0⟩, ⟨.fresh 1, .source 1⟩, ⟨.fresh 2, .source 2⟩]

def equalityRecipe (i : Fin 3) : List LiteralRecipe :=
  [⟨.fresh i.castSucc, .constant false⟩, ⟨.old i, .constant true⟩, ⟨.fresh 3, .constant true⟩,
   ⟨.fresh i.castSucc, .constant false⟩, ⟨.old i, .constant true⟩, ⟨.fresh 3, .constant false⟩,
   ⟨.fresh i.castSucc, .constant true⟩, ⟨.old i, .constant false⟩, ⟨.fresh 3, .constant true⟩,
   ⟨.fresh i.castSucc, .constant true⟩, ⟨.old i, .constant false⟩, ⟨.fresh 3, .constant false⟩]

def recipe : List LiteralRecipe :=
  mainRecipe ++ equalityRecipe 0 ++ equalityRecipe 1 ++ equalityRecipe 2

end PerfectCompleteness.NormalizationWords



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryAffineAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

inductive Label
  | seed | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan, .restore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLookupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CleanupLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

/-- Actual tape family after the selected stacks have been drained in order. -/
def clearTapes : {n : Nat} → (Fin n → K) → (K → List Bool) → K → List Bool
  | 0, _, base => base
  | n + 1, selected, base =>
      clearTapes (fun i : Fin n => selected i.succ) (Function.update base (selected 0) [])

/-- Exact number of transitions, including the final state-reset transition. -/
def actualCost : {n : Nat} → (Fin n → K) → (K → List Bool) → Nat
  | 0, _, _ => 1
  | n + 1, selected, base =>
      actualCost (fun i : Fin n => selected i.succ) (Function.update base (selected 0) []) +
        ((base (selected 0)).length + 1)

theorem clearTapes_apply {n : Nat} (selected : Fin n → K) (base : K → List Bool) (k : K) :
    clearTapes selected base k = if ∃ i, selected i = k then [] else base k := by
  induction n generalizing base with
  | zero => simp [clearTapes]
  | succ n ih =>
      rw [clearTapes, ih]
      by_cases first : selected 0 = k
      · subst k
        simp [Function.update]
      · have notFirst : k ≠ selected 0 := Ne.symm first
        by_cases later : ∃ i : Fin n, selected i.succ = k <;>
          simp [Fin.exists_fin_succ, first, later, Function.update, notFirst]

theorem actualCost_le {n : Nat} (selected : Fin n → K) (base : K → List Bool) :
    actualCost selected base ≤ (∑ i, (base (selected i)).length) + n + 1 := by
  induction n generalizing base with
  | zero => simp [actualCost]
  | succ n ih =>
      have tailBound := ih (fun i : Fin n => selected i.succ)
        (Function.update base (selected 0) [])
      have sumBound :
          (∑ i : Fin n, ((Function.update base (selected 0) []) (selected i.succ)).length) ≤
            ∑ i : Fin n, (base (selected i.succ)).length := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : selected i.succ = selected 0 <;> simp [h]
      rw [actualCost, Fin.sum_univ_succ]
      omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLogCounter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLogCounter

open Turing

def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[simp] theorem bitLength_zero : bitLength 0 = 0 := rfl

theorem bitLength_positive {n : Nat} (h : n ≠ 0) : bitLength n = n.log2 + 1 := by
  simp [bitLength, h]

def increments (n : Nat) (started : Bool) : Nat :=
  if n = 0 then (if started then 0 else 1) else bitLength n

@[simp] theorem increments_true (n : Nat) : increments n true = bitLength n := by
  by_cases hn : n = 0 <;> simp [increments, hn]

theorem increments_false (n : Nat) : increments n false = n.log2 + 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · simp [increments, bitLength, hn]

def coreTime (n : Nat) : Nat :=
  if h : n = 0 then 1 else n + n / 2 + 3 + coreTime (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem coreTime_zero : coreTime 0 = 1 := by rw [coreTime]; rfl

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := (Bool × Bool) × Option Bool

def initialState : State := ((false, false), none)

def rawTapes (input scratch output : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => scratch
  | 2 => output

theorem update_input (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

theorem update_scratch (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 2 replacement = rawTapes input scratch replacement := by
  funext k
  fin_cases k <;> rfl

def stripLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => (1 : Fin 5)))
      (.load (fun _ => initialState) (.goto fun _ => 4)))

def guardLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .peek 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 2 (fun _ => true)
        (.load (fun _ => ((false, true), none)) (.goto fun _ => 3)))
      (.branch (fun state => state.1.2)
        (.load (fun _ => initialState) .halt)
        (.push 2 (fun _ => true) (.load (fun _ => initialState) .halt))))

def halfLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.1.1)
        (.push 1 (fun _ => true)
          (.load (fun state => ((false, state.1.2), state.2)) (.goto fun _ => 3)))
        (.load (fun state => ((true, state.1.2), state.2)) (.goto fun _ => 3)))
      (.load (fun state => ((false, state.1.2), none)) (.goto fun _ => 4)))

def totalTime (n : Nat) : Nat := 2 * n + 3 + coreTime n

end UniqueGamesTheorem.Foundations.Complexity.MachineLogCounter

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance instFintypeExtraLabel : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

/-- Homogeneous Boolean embedding of the fixed logarithm program. -/
def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterFinish

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterStartLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Reduction.MachineTransducer

open Turing
open UniqueGamesTheorem.Foundations.Complexity

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

theorem update_input (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

variable {Q : Type} [Fintype Q]

/-- The semantic output, with the control state updated after each input bit. -/
def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

def loop (initial : Q) :
    TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool) :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun state => some (state.1, state.2.getD false))
      (.load (fun _ => (initial, none)) .halt))

end UniqueGamesTheorem.Reduction.MachineTransducer

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Emitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

def resultTapes (output : K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem resultTapes_output (output : K) (base : K → List Bool) (bits : List Bool) :
    resultTapes output base bits output = bits.reverse ++ base output := by
  simp [resultTapes]

def affineValue (terms : List (Fin h × Nat)) (values : Fin h → Nat) (offset : Nat) : Nat :=
  (terms.map (fun term => term.2 * values term.1)).sum + offset

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

variable {V E : Type*} {n m : Nat}

theorem count_false_map_filter {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.filter (fun x => decide (f x = false))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem count_false_finRange (f : Fin m → Bool) :
    ((List.finRange m).map f).count false =
      (Finset.univ.filter (fun e : Fin m => f e = false)).card := by
  classical
  calc
    _ = ((List.finRange m).filter (fun e => decide (f e = false))).length :=
      count_false_map_filter _ _
    _ = (((List.finRange m).filter (fun e => decide (f e = false))).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)).symm
    _ = _ := by
      congr 1
      ext e
      simp

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

/-- A fixed polynomial in the complete encoded input length. -/
noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFTemplate

open PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

/-- The same prefix-chain clauses used by `splitLong`, in their output order. -/
def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

/-- Fixed clause/slot indexing for the machine's finite emission plan. -/
def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFTemplate

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFRowPlanLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

section Templates

open FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

end Templates

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

open Turing

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AmplificationIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

theorem min_double_min (u cap : ℝ) (hc : 0 ≤ cap) :
    min (2 * min u cap) cap = min (2 * u) cap := by
  by_cases hu : u ≤ cap
  · rw [min_eq_left hu]
  · have hcu : cap ≤ u := le_of_not_ge hu
    rw [min_eq_right hcu, min_eq_right (by linarith : cap ≤ 2 * cap),
      min_eq_right (by linarith : cap ≤ 2 * u)]

end UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringPortReindexLemmas
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
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

end UniqueGamesTheorem.Foundations.PCP.PoweringPortReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalConstantsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

/-- The spectral denominator is exactly 66 at the fixed return parameter. -/
theorem spectral_denominator_eq :
    (1 + 2 / (1 - (31 / 32 : ℝ))) + 1 = 66 := by
  norm_num

end UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The executable dummy numbering is the sum of earlier cloud sizes plus
the local dummy index. This connects the actual list search in vertexOrder
with unary prefix-sum routines, without changing the chosen enumeration. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

open scoped BigOperators

theorem idxOf_map_injective {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

theorem sigma_length {A : Type*} (sizes : A → Nat) (xs : List A) :
    (xs.sigma (fun x => List.finRange (sizes x))).length = (xs.map sizes).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sigma_cons, ih]

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingOffsets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

/-- A two-parameter bound for the complete unary graph codec. -/
noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalTableFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Complexity

/-- A fixed quadratic in the full serialized input length. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFOutputLemmas
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

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRepeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape
  | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase
  | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

/-- Running time after the parser: actual body budgets, two transfers per
body result, one guard per iteration, and the final transfer and empty guard. -/
def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

end UniqueGamesTheorem.Foundations.Complexity.MachineRepeat

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-! Every physical tape has a finite alphabet. Together with `M.kFin`, this
also makes the disjoint union of all physical tape alphabets finite. -/

theorem of_homogeneous (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k = α) : FiniteAlphabet M := by
  intro k
  rw [alphabet k]
  infer_instance

/-- All concrete Boolean-stack machines satisfy the stronger alphabet condition. -/
theorem of_bool (M : FinTM2) (alphabet : ∀ k, M.Γ k = Bool) : FiniteAlphabet M :=
  of_homogeneous M alphabet

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryLessAtLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- Slots 0 and 1 are the operands; slots 2 and 3 are their saved prefixes. -/
def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PCPIterationMachine

open Turing
open MachineCountedLoop

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

/-- The exponent is a fixed growth constant, independent of the input. -/
theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

/-- This recurrence concerns semantic cardinality, not unary encoding length. -/
theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

end UniqueGamesTheorem.Foundations.Complexity.PCPIterationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineAppendAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

end UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

end

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

open Turing

/-- The homogeneous parts of a finite machine, without dependent alphabet casts. -/
structure Program (K Λ σ : Type) where
  input : K
  output : K
  main : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

section Structural

variable {K Λ Λ' σ : Type} [DecidableEq K]

def extendedLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def extendedCfg (labels : Λ → Λ') (haltTarget : Option Λ') (register : Option Bool)
    (cfg : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ' (σ × Option Bool) :=
  ⟨extendedLabel labels haltTarget cfg.l, (cfg.var, register), cfg.stk⟩

/-- Add one finite scratch register while preserving each raw transition. -/
def extendedStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ →
      TM2.Stmt (fun _ : K => Bool) Λ' (σ × Option Bool)
  | .push k f next => .push k (fun state => f state.1)
      (extendedStmt labels haltTarget next)
  | .peek k f next => .peek k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .pop k f next => .pop k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .load f next => .load (fun state => (f state.1, state.2))
      (extendedStmt labels haltTarget next)
  | .branch test yes no => .branch (fun state => test state.1)
      (extendedStmt labels haltTarget yes) (extendedStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_extended (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ)
    (register : Option Bool) (tapes : K → List Bool) :
    TM2.stepAux (extendedStmt labels haltTarget stmt) (state, register) tapes =
      extendedCfg labels haltTarget register (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Structural

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def sourceMachine (P : Program K Λ σ) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Λ
  main := P.main
  σ := σ
  initialState := P.initial
  m := P.code

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.relationRead, .relationRestore, .reverseRead,
  .reverseRestore, .tailRead, .tailRestore, .appendOld, .appendRow, .appendBack]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Exact row field concatenation at the level of stored bits. -/
def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

end UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

open Turing

/-- One initialization label and ten labels per fixed port. -/
abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

/-- The only data-changing index operation is a tape push, below. This
function chooses a finite continuation among the fixed port-control labels. -/
def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddingRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

open Turing

inductive Control
  | initialize_ | guard | bump
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .guard, .bump]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 6 ⊕ Unit
abbrev Label (d : Nat) := MachineDummyRows.Label d ⊕ Control
abbrev State := (Unit × Option Bool) × Unit

def bodyEntry (d : Nat) (hd : 0 < d) : Label d :=
  .inl (MachineDummyRows.rowLabel ⟨0, hd⟩ .relationRead)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingRows

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-- A common row-size bound for all remaining vertices and ports. -/
def rowBound (d v e count : Nat) : Nat := v + count + e + (count + 1) * d + 8194

/-- This bound is invariant when one vertex and its `d` reverse indices
have been consumed from the remaining outer-loop count. -/
theorem rowBound_next (d v e count : Nat) :
    rowBound d (v + 1) (e + d) count = rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

theorem blockRow_le_rowBound (d v e count : Nat) :
    v + e + d + 8194 ≤ rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

def rowCap (d size : Nat) : Nat := size + (size + 1) * d + 8194

noncomputable def rowPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + 1) * Polynomial.C d + Polynomial.C 8194

/-- A cubic polynomial for fixed degree, including the final zero-fuel
guard. The one-time relation initializer can be accounted for separately. -/
noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C d *
    (Polynomial.C 4 * rowPolynomial d +
      Polynomial.C 2 * (Polynomial.X + Polynomial.X * Polynomial.C d * rowPolynomial d) +
      Polynomial.C 10) + Polynomial.C 2) + 1

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingBounds

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddingCertificate

open MachinePaddingRows

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachinePaddingBounds.timePolynomial d + 1

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddingCertificate

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialTablesLemmas
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

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBudget

open Complexity

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBudget

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialRows

def dummyWords (n m : Nat) : List Nat :=
  [n + m, 6 * m] ++ List.replicate 4096 1

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

/-- The list induced by an explicit numbering, in increasing numeric order. -/
def orderedList {α : Type*} {n : Nat} (e : α ≃ Fin n) : List α :=
  List.ofFn e.symm

theorem orderedList_cast {α : Type*} {m n : Nat} (e : α ≃ Fin m) (h : m = n) :
    orderedList (e.trans (finCongr h)) = orderedList e := by
  subst n
  rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialRows

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Prefix and suffix invariants for regular-table row loops

These finite block identities apply to original-vertex blocks, to dummy blocks
within an owner, and to whole owner blocks. They expose exactly the next emitted
block while preserving the codec's established order.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularLoopWords

/-- Bits emitted by the first `k` blocks. -/
def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

/-- Bits remaining after the first `k` blocks. -/
def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksPrefix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f 0 = [] := by
  simp only [blocksPrefix, List.take_zero, List.flatten_nil]

@[simp] theorem blocksPrefix_all {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f n = (List.ofFn f).flatten := by
  have h : (List.ofFn f).take n = List.ofFn f := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksPrefix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksPrefix f (k + 1) = blocksPrefix f k ++ f ⟨k, h⟩ := by
  unfold blocksPrefix
  rw [List.take_succ_eq_append_getElem
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.getElem_ofFn]

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

/-- The completed and remaining portions partition the original bitstream. -/
theorem blocksPrefix_append_suffix {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    blocksPrefix f k ++ blocksSuffix f k = (List.ofFn f).flatten := by
  unfold blocksPrefix blocksSuffix
  rw [← List.flatten_append, List.take_append_drop]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularLoopWords

end

section

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularLoopWords
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem blocksPrefix_length_le {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    (blocksPrefix f k).length ≤ (List.ofFn f).flatten.length := by
  have h := congrArg List.length (blocksPrefix_append_suffix f k)
  simp only [List.length_append] at h
  omega

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

end

section

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq, Fintype

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineReadClause
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineCleanup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

open Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel


theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! One complete clause iteration of the actual initial graph machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBody

open Turing Complexity RawInitialMachineModel
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineBody

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RawInitialMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact execution of the clause loop, in the original occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

open Turing Complexity RawInitialMachineModel
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_MachineRawInitialTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

namespace UniqueGamesTheorem.Foundations.PCP.MachineRawInitialTable

open Turing Complexity RawInitialMachineModel
open RawInitialMachineBudget RawInitialMachineLoop

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.PCP.MachineRawInitialTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

open UniqueGamesTheorem.Foundations.Complexity

variable {n d : Nat}

/-- The machine's fixed-degree numerical map for an old reverse-row index. -/
def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLazyWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

open Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label (d : Nat)
  | copySeed | copyScan | copyRestore | initialize_ | divide
  | emit (r : Fin d)
  | affineScan | affineRestore | drainQuotient | finish
  deriving DecidableEq, Fintype

def steps (d j : Nat) : Nat := 3 * j + 3 * (j / d) + 11

def value (d c b j : Nat) : Nat := c * (j / d) + (j % d) + b

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem lazy_value (d j : Nat) : value d (2 * d) d j =
    2 * d * (j / d) + d + (j % d) := by
  unfold value
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

open Turing
open PCP

/-! ## The actual stored row and its input word boundaries -/

/-! ## One fixed finite program -/

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool

def lookupTape (i : Fin 5) : Tape := ⟨i.val + 1, by omega⟩

theorem lookupTape_injective : Function.Injective lookupTape := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

theorem source_outside (i : Fin 5) : (0 : Tape) ≠ lookupTape i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

def fields : Fin 3 → Tape := Fin.cases 0 (Fin.cases 6 (fun _ => 7))

@[simp] theorem fields_zero : fields 0 = 0 := rfl
@[simp] theorem fields_one : fields 1 = 6 := rfl
@[simp] theorem fields_two : fields 2 = 7 := rfl

theorem fields_separate (i : Fin 3) : fields i ≠ 8 ∧ fields i ≠ 5 := by
  fin_cases i <;> decide

/-! ## Physical intermediate tape states -/

section Execution

variable {Λ σ : Type}

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Execution

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (4 * q + 17) * inputLength + 2 * outputLength + 4 * q + 32795

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

open Turing
open PCP.PreprocessingLazyWords (reverseMap )

variable {K Λ A : Type} [DecidableEq K]

abbrev Label (d : Nat) := MachinePortReindex.Label d ⊕ MachineTableRows.Label

/-- Tape roles: tail, old reverse, relation, scratch, divided copy,
quotient, new reverse, accumulated output, row buffer. -/
def addressIndex : Fin 5 → Fin 9 := ![1, 3, 4, 5, 6]

theorem addressIndex_injective : Function.Injective addressIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [addressIndex]

def fields (tape : Fin 9 → K) : Fin 3 → K := ![tape 0, tape 6, tape 2]

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

inductive StreamLabel (d : Nat)
  | tailStart | tailRead | reverseStart | reverseRead | copyRelation
  | row (stage : Label d)
  | clearTail | clearOld | clearRelation | clearNew
  deriving DecidableEq, Fintype

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

abbrev VertexLabel (d : Nat) := Fin (d + 1) × Option (StreamLabel d)

def valueBound (c b m : Nat) : Nat := c * m + m + b
def rowSizeBound (c b n m : Nat) : Nat := n + valueBound c b m + 8194
def rowCostBound (c b n m : Nat) : Nat :=
  2 * n + 8 * m + valueBound c b m + 4 * rowSizeBound c b n m + 8224

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTableSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

open Turing

abbrev Tape := Fin 5
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .startVertices,
  .readVertices, .startDarts, .readDarts]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Tape 0 is protected input, 1 is the working row stream, 2 is scratch,
and 3 and 4 hold the extracted vertex and dart counts. -/
def tapes (original work vertices darts : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then original else if k = 1 then work
    else if k = 3 then vertices else if k = 4 then darts else []

def initialTapes (input : List Bool) : Tape → List Bool := tapes input [] [] []

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 6

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 4 * length + 6 := by simp [timePolynomial]

end UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

open Turing PCP

inductive Tape
  | input | output | source | vertices | darts | fuel | vertex | reverse
  | tail | old | relation | scratch | divided | quotient | newReverse | rowBuffer
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .source, .vertices, .darts, .fuel,
  .vertex, .reverse, .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
  .rowBuffer]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def splitRoles : Fin 5 → Tape := ![.input, .source, .scratch, .vertices, .darts]
def splitView : Tape → Option (Fin 5)
  | .input => some 0 | .source => some 1 | .scratch => some 2
  | .vertices => some 3 | .darts => some 4 | _ => none

def dummyRoles : Fin 6 → Tape := ![.tail, .reverse, .relation, .rowBuffer, .output, .scratch]
def dummyView : Tape → Option (Fin 6)
  | .tail => some 0 | .reverse => some 1 | .relation => some 2
  | .rowBuffer => some 3 | .output => some 4 | .scratch => some 5 | _ => none

def oldRoles : Fin 10 → Tape :=
  ![.tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
    .output, .rowBuffer, .source]

theorem splitRoles_left (i : Fin 5) : splitView (splitRoles i) = some i := by
  fin_cases i <;> rfl

theorem dummyRoles_left (i : Fin 6) : dummyView (dummyRoles i) = some i := by
  fin_cases i <;> rfl

theorem dummyRoles_right (t : Tape) (i : Fin 6) (h : dummyView t = some i) : dummyRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [dummyView, dummyRoles]

theorem oldRoles_injective : Function.Injective oldRoles := by decide

inductive Label (d : Nat)
  | split (label : MachineTableSplit.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | fuelFirst | fuelSecond | seedCounters | guard | copyVertexFirst | copyVertexSecond
  | dummy (label : MachineDummyRows.Label d)
  | clearDummyTail | clearDummyRelation
  | oldRows (label : MachineLazyRows.VertexLabel d)
  | nextVertex | clearVertices | clearDarts | clearFuel | clearVertex | clearReverse
  deriving DecidableEq, Fintype

def frame (input source output vertices darts fuel vertex reverse : List Bool) : Tape → List Bool
  | .input => input | .source => source | .output => output
  | .vertices => vertices | .darts => darts | .fuel => fuel
  | .vertex => vertex | .reverse => reverse | _ => []

def initialTapes (input : List Bool) : Tape → List Bool := frame input [] [] [] [] [] [] []

def finalTapes (input output : List Bool) : Tape → List Bool := frame input [] output [] [] [] [] []

theorem joinTrace {X : Type} {f : X → X} {a b c : X} {s t : Nat}
    (first : f^[s] a = b) (second : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem frame_old_empty (input source output vertices darts fuel vertex reverse : List Bool)
    (i : Fin 10) (h7 : i ≠ 7) (h9 : i ≠ 9) :
    frame input source output vertices darts fuel vertex reverse (oldRoles i) = [] := by
  fin_cases i <;> simp_all [frame, oldRoles]

def finishSteps (d n m v : Nat) : Nat := n + m + v + 2 * d * v + 11

def remaining (n r : Nat) : List (Fin n) := (List.finRange n).drop r

@[simp] theorem remaining_zero (n : Nat) : remaining n 0 = List.finRange n := by simp [remaining]
@[simp] theorem remaining_done (n : Nat) : remaining n n = [] := by simp [remaining]

theorem remaining_cons (n r : Nat) (h : r < n) :
    remaining n r = ⟨r, h⟩ :: remaining n (r + 1) := by
  unfold remaining
  rw [List.drop_eq_getElem_cons (l := List.finRange n) (i := r) (by simpa using h)]
  simp

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (1000000 * (d + 1) ^ 3 + 100) * (Polynomial.X + 1) ^ 3

@[simp] theorem timePolynomial_eval (d L : Nat) :
    (timePolynomial d).eval L = (1000000 * (d + 1) ^ 3 + 100) * (L + 1) ^ 3 := by
  simp [timePolynomial]

@[simp] theorem finalTapes_input (input output : List Bool) : finalTapes input output .input = input := rfl
@[simp] theorem finalTapes_output (input output : List Bool) : finalTapes input output .output = output := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyTableRuntime
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
open MachineLazyTable (Tape Label )

/-- A fixed explicit list of every non-output tape, independent of input data. -/
def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableProgramLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing

inductive ExtraTape
  | vertexCount | result
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.vertexCount, .result]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive OuterLabel
  | initialize_ | vertexGuard | prepareRow | afterRow | reverseOutput | done
  deriving DecidableEq

protected abbrev OuterLabel.enumList : List OuterLabel := [.initialize_, .vertexGuard, .prepareRow,
  .afterRow, .reverseOutput, .done]

protected theorem OuterLabel.enumList_nodup : OuterLabel.enumList.Nodup := by decide

instance instFintypeOuterLabel : Fintype OuterLabel where
  elems := ⟨OuterLabel.enumList, OuterLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing

inductive AffinePhase
  | copyCount | multiplySize
  deriving DecidableEq

protected abbrev AffinePhase.enumList : List AffinePhase := [.copyCount, .multiplySize]

protected theorem AffinePhase.enumList_nodup : AffinePhase.enumList.Nodup := by decide

instance instFintypeAffinePhase : Fintype AffinePhase where
  elems := ⟨AffinePhase.enumList, AffinePhase.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive AffineLabel
  | seed | scan | restore
  deriving DecidableEq

protected abbrev AffineLabel.enumList : List AffineLabel := [.seed, .scan, .restore]

protected theorem AffineLabel.enumList_nodup : AffineLabel.enumList.Nodup := by decide

instance instFintypeAffineLabel : Fintype AffineLabel where
  elems := ⟨AffineLabel.enumList, AffineLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive OuterLabel
  | initialize_
  | levelGuard
  | affine (phase : AffinePhase) (label : AffineLabel)
  | clearOldTable | reverseResult | reverseTable | clearCurrentSize
  | drainInputVertex | drainVertexCount | done
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing

variable {K Λ ρ : Type} [DecidableEq K]

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowEmitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.AlphabetTable

/-- One scaled scan/restore, one bounded offset, the delimiter, and final jump. -/
def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

end

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

open Turing

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.AlphabetTable

theorem concatenate {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

open UniqueGamesTheorem.Foundations.Complexity

variable {v d : Nat}

theorem ofFn_cast {α : Type*} {n m : Nat} (h : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTableEnumeration

def singleStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := Nat.le_refl _

def sequence {α : Type*} {step : α → Option α} {a b c : α} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) := by
  simpa only [Nat.add_comm n m] using
    StateTransition.EvalsToInTime.trans step m n a b (some c) first second

def widen {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (bound : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bound

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderTableLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTableEnumeration

def boundarySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamilyLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing

def familySingleStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing

def singleFamilyStep {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingOverlayWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact stored-row and codec expansion of the executable overlay. Within
each vertex block, all original ports precede all expander ports. -/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayWords

open Complexity

variable {n d e : Nat}

def oldReverseMap (d e j : Nat) : Nat := (d + e) * (j / d) + j % d
def expanderReverseMap (d e j : Nat) : Nat := (d + e) * (j / e) + d + j % e

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineOverlayRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

open Turing
open PCP.PreprocessingOverlayWords

variable {K Λ A : Type} [DecidableEq K]

inductive Label (e : Nat)
  | loadStart | loadLoop | seedRelation
  | row (stage : MachineLazyRows.Label e)
  | drainOld | drainNew | drainRelation
  deriving DecidableEq, Fintype

/-- The row body's nine tapes retain their numbering; tape 9 is the stream. -/
def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  exact Fin.castSucc_injective 9 h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

/-! The fixed-degree vertex loop has one finite label block per port, plus
one terminal boundary. The stored row values do not occur in its program. -/

abbrev VertexLabel (e : Nat) := Fin (e + 1) × Option (Label e)

def valueBound (d e B : Nat) : Nat := (d + e) * B + B + d

theorem value_le (d e j B : Nat) (hj : j ≤ B) :
    MachinePortReindex.value e (d + e) d j ≤ valueBound d e B := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hmod := (Nat.mod_le j e).trans hj
  have hmul := Nat.mul_le_mul_left (d + e) hdiv
  unfold MachinePortReindex.value valueBound
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineOverlayTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

variable {AmbientState : Type}

open Turing
open PCP PCP.PreprocessingOverlayWords
open MachineCloudPadding

abbrev Tape := Fin 5 ⊕ Fin 12

def graphArchive : Tape := .inl 0
def graphStream : Tape := .inl 1
def scratch : Tape := .inl 2
def vertexCount : Tape := .inl 3
def dartCount : Tape := .inl 4
def expanderArchive : Tape := .inr 0
def expanderStream : Tape := .inr 1
def fuel : Tape := .inr 2
def vertex : Tape := .inr 3
def tail : Tape := .inr 4
def oldReverse : Tape := .inr 5
def relation : Tape := .inr 6
def dividedCopy : Tape := .inr 7
def quotient : Tape := .inr 8
def newReverse : Tape := .inr 9
def rowBuffer : Tape := .inr 10
def output : Tape := .inr 11

def oldTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, graphStream]

def expanderTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, expanderStream]

theorem expanderTapes_injective : Function.Injective expanderTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [expanderTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, expanderStream]

inductive MainLabel (d e : Nat)
  | copyHFirst | copyHSecond
  | countSeed | countScan | countRestore
  | headerSeed | headerScan | headerRestore
  | fuelSeed | fuelScan | fuelRestore | vertexSeed | guard
  | old (stage : MachineLazyRows.VertexLabel d)
  | tailSeed | tailScan | tailRestore
  | expander (stage : MachineOverlayRows.VertexLabel e)
  | drainTail | increment
  | drainFuel | drainVertex | drainVertexCount | drainDartCount
  deriving DecidableEq, Fintype

abbrev Label (d e : Nat) := MachineTableSplit.Label ⊕ MainLabel d e

def next {oldDegree expanderDegree : Nat} (l : MainLabel oldDegree expanderDegree) :
    Option (Label oldDegree expanderDegree) := some (.inr l)

def extraTapes (rawH : List Bool) : Fin 12 → List Bool :=
  fun i => if i = 0 then rawH else []

def splitView : Tape → Option (Fin 5)
  | .inl i => some i
  | .inr _ => none

def combine (left : Fin 5 → List Bool) (rawH : List Bool) : Tape → List Bool
  | .inl i => left i
  | .inr i => extraTapes rawH i

def initialTapes (graph rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.initialTapes graph) rawH

/-- Every unnamed work tape is empty at these phase boundaries. -/
def memory (g h gs hs n m f v t out : List Bool) : Tape → List Bool
  | .inl i => ![g, gs, [], n, m] i
  | .inr i => ![h, hs, f, v, t, [], [], [], [], [], [], out] i

@[simp] theorem memory_graphArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphArchive = g := rfl
@[simp] theorem memory_graphStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphStream = gs := rfl
@[simp] theorem memory_scratch (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out scratch = [] := rfl
@[simp] theorem memory_vertexCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertexCount = n := rfl
@[simp] theorem memory_dartCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dartCount = m := rfl
@[simp] theorem memory_expanderArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderArchive = h := rfl
@[simp] theorem memory_expanderStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderStream = hs := rfl
@[simp] theorem memory_fuel (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out fuel = f := rfl
@[simp] theorem memory_vertex (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertex = v := rfl
@[simp] theorem memory_tail (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out tail = t := rfl
@[simp] theorem memory_oldReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out oldReverse = [] := rfl
@[simp] theorem memory_relation (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out relation = [] := rfl
@[simp] theorem memory_dividedCopy (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dividedCopy = [] := rfl
@[simp] theorem memory_quotient (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out quotient = [] := rfl
@[simp] theorem memory_newReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out newReverse = [] := rfl
@[simp] theorem memory_rowBuffer (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out rowBuffer = [] := rfl
@[simp] theorem memory_output (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out output = out := rfl

@[simp] theorem update_output (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) output x = memory g h gs hs n m f v t x := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_expanderStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) expanderStream x =
      memory g h gs x n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_graphStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) graphStream x =
      memory g h x hs n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_fuel (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) fuel x = memory g h gs hs n m x v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertex (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertex x = memory g h gs hs n m f x t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_tail (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) tail x = memory g h gs hs n m f v x out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertexCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertexCount x = memory g h gs hs x m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_dartCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) dartCount x = memory g h gs hs n x f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def preparationSteps (n : Nat) (h : List Bool) : Nat := 2 * (h.length + 1) + 6 * (n + 1) + 4

def remaining {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).drop k).flatten
def emittedPrefix {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).take k).flatten

theorem remaining_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    remaining block v.val = block v ++ remaining block (v.val + 1) := by
  have hs := List.getElem_cons_drop (as := List.ofFn block) (i := v.val)
    (by simpa only [List.length_ofFn] using v.isLt)
  unfold remaining
  rw [← hs]
  simp only [List.flatten_cons, List.getElem_ofFn, Fin.eta]

theorem prefix_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    emittedPrefix block (v.val + 1) = emittedPrefix block v.val ++ block v := by
  unfold emittedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using v.isLt)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.getElem_ofFn, Fin.eta]

@[simp] theorem remaining_zero {n : Nat} (block : Fin n → List Bool) :
    remaining block 0 = (List.ofFn block).flatten := by simp [remaining]
@[simp] theorem remaining_end {n : Nat} (block : Fin n → List Bool) :
    remaining block n = [] := by
  unfold remaining
  rw [List.drop_eq_nil_iff.mpr (by simpa only [List.length_ofFn] using (Nat.le_refl n)), List.flatten_nil]
@[simp] theorem prefix_zero {n : Nat} (block : Fin n → List Bool) : emittedPrefix block 0 = [] := by
  simp [emittedPrefix]
@[simp] theorem prefix_end {n : Nat} (block : Fin n → List Bool) :
    emittedPrefix block n = (List.ofFn block).flatten := by
  unfold emittedPrefix
  have ht : (List.ofFn block).take n = List.ofFn block :=
    List.take_of_length_le (by simpa only [List.length_ofFn] using (Nat.le_refl n))
  rw [ht]

def cleanupSteps (n m : Nat) : Nat := 2 * n + m + 8

theorem flatMap_length_le {α : Type*} (items : List α) (f : α → List Bool)
    (B : Nat) (bounded : ∀ x ∈ items, (f x).length ≤ B) :
    (items.flatMap f).length ≤ items.length * B := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      have hx := bounded x (by simp)
      have ht := ih (fun y hy => bounded y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem flatten_length_le (items : List (List Bool)) (B : Nat)
    (bounded : ∀ x ∈ items, x.length ≤ B) : items.flatten.length ≤ items.length * B := by
  simpa only [List.flatMap_id] using flatMap_length_le items id B bounded

def oldSize (d e n : Nat) : Nat := MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineVertexPadding
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

open Turing
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

inductive Tape
  | original | output | vertex | edge | power | level | fuel | relation
  | scratch | work | saved | product | rowWork | rowSpare
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .output, .vertex, .edge, .power, .level,
  .fuel, .relation, .scratch, .work, .saved, .product, .rowWork, .rowSpare]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label (d : Nat)
  | splitCode (l : MachineTableSplit.Label)
  | powerCode (l : MachineCeilingPower.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | copyFirst | copySecond | subtractCode (l : MachineCloudPadding.Label)
  | rowsCode (l : MachinePaddingRows.Label d)
  | cleanVertex | cleanEdge | cleanPower | cleanRelation | cleanFuel
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- All unnamed work stacks are empty at the phase boundaries below. -/
def memory (input output vertex edge power level fuel relation : List Bool) : Tape → List Bool
  | .original => input
  | .output => output
  | .vertex => vertex
  | .edge => edge
  | .power => power
  | .level => level
  | .fuel => fuel
  | .relation => relation
  | _ => []

@[simp] theorem update_output (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .output x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_vertex (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .vertex x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_edge (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .edge x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_relation (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .relation x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

def rowTape : MachinePaddingRows.Tape → Tape
  | .inl k => (![.vertex, .edge, .relation, .rowWork, .output, .rowSpare] : Fin 6 → Tape) k
  | .inr _ => .fuel
def rowView : Tape → Option MachinePaddingRows.Tape
  | .vertex => some (.inl 0)
  | .edge => some (.inl 1)
  | .relation => some (.inl 2)
  | .rowWork => some (.inl 3)
  | .output => some (.inl 4)
  | .rowSpare => some (.inl 5)
  | .fuel => some (.inr ())
  | _ => none

theorem rowView_left (k : MachinePaddingRows.Tape) : rowView (rowTape k) = some k := by
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl
theorem rowView_right (j : Tape) (k : MachinePaddingRows.Tape)
    (h : rowView j = some k) : rowTape k = j := by
  rcases k with k | k
  · cases j <;> fin_cases k <;> simp_all [rowView, rowTape]
  · cases k; cases j <;> simp_all [rowView, rowTape]

def rowStateEquiv (σ : Type) : (MachinePaddingRows.State × (σ × Bool)) ≃ State σ where
  toFun x := (x.2, x.1.1.2)
  invFun x := ((((), x.2), ()), x.1)
  left_inv := by rintro ⟨⟨⟨⟨⟩, r⟩, ⟨⟩⟩, a⟩; rfl
  right_inv := by rintro ⟨a, r⟩; rfl

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

def cleanupTime (d m : Nat) : Nat := 2 * m + m * d + 8201

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudRankLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

open Turing MachineCloudCount

variable {σ : Type}

inductive RankLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | row | field | restore | done
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def rankSkip (i : Nat) : RankLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

/-- In a filtered list, the rank of a retained entry is the number of retained
entries preceding its first original occurrence. This is a specification lemma. -/
theorem idxOf_filter_prefix {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (hp : p a = true) :
    ∀ xs : List α, a ∈ xs →
      (xs.filter p).idxOf a = ((xs.take (xs.idxOf a)).filter p).length := by
  classical
  intro xs
  induction xs with
  | nil => intro ha; simp at ha
  | cons b xs ih =>
      intro ha
      by_cases hba : b = a
      · subst b
        simp [hp]
      · have ha' : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
        cases hb : p b <;>
          simp [hba, hb, ih ha']

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

open Turing
open MachineCloudCount (Row rowWords rowsHits )

abbrev BaseState (σ : Type) := MachineCloudCount.State σ

inductive BaseLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | field | restore | done | clearWork | clearRank
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : BaseLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .done

variable {σ : Type}

inductive Phase
  | checking | advancing | finishing
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.checking, .advancing, .finishing]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Control
  | initialize_ | dispatch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .dispatch]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Label := BaseLabel ⊕ Control
abbrev State (σ : Type) := BaseState σ × Phase

open UniqueGamesTheorem.Foundations.PCP

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularInternalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive FinishLabel
  | seedReturn | copyReturn | restoreReturn | affine | restoreTarget | equality
  | row (stage : MachineTableRows.Label)
  | clearReverse | clearEquality
  deriving DecidableEq, Fintype

/-- Tail, selected global target, returned port, scratch, reverse field,
equality field, row buffer, accumulated output. -/
def finishFields (tape : Fin 8 → K) : Fin 3 → K := fun i =>
  if i = 0 then tape 0 else if i = 1 then tape 4 else tape 5

omit [DecidableEq K] in
@[simp] theorem finishFields_zero (tape : Fin 8 → K) : finishFields tape 0 = tape 0 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_one (tape : Fin 8 → K) : finishFields tape 1 = tape 4 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_two (tape : Fin 8 → K) : finishFields tape 2 = tape 5 := rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def rotorLookupTapes (tape : Fin 8 → K) (j : Fin 5) : K :=
  tape ⟨j.val + 1, by omega⟩

omit [DecidableEq K] in
theorem rotorLookupTapes_injective (tape : Fin 8 → K) (h : Function.Injective tape) :
    Function.Injective (rotorLookupTapes tape) := by
  intro i j hij
  have hv := congrArg Fin.val (h hij)
  apply Fin.ext
  simpa only [Fin.val_mk, Nat.add_left_inj] using hv

omit [DecidableEq K] in
theorem rotorLookupTapes_outside (tape : Fin 8 → K) (h : Function.Injective tape)
    (i : Fin 5) : tape 0 ≠ rotorLookupTapes tape i := by
  intro he
  have hv := congrArg Fin.val (h he)
  change 0 = i.val + 1 at hv
  omega

inductive SelectExtraTape
  | localIndex | owner | cloudSize | prefixOffset | darts
  | savedLeft | savedRight | localWork | sizeWork
  deriving DecidableEq

abbrev SelectState (σ : Type) := MachineUnaryLessAt.State (σ × MachineCloudSelect.Phase)

def selectStateEquiv (σ : Type) : (MachineCloudSelect.State σ × Unit) ≃ SelectState σ where
  toFun s := (((s.1.1.1.1, s.1.2), s.1.1.1.2), s.1.1.2)
  invFun s := ((((s.1.1.1, s.1.2), s.2), s.1.1.2), ())
  left_inv s := by rcases s with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨⟩⟩; rfl
  right_inv s := by rcases s with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

inductive SelectCopy
  | oldLocal | oldOwner | dummyLocal | dummySize | dummyDifference
  deriving DecidableEq

protected abbrev SelectCopy.enumList : List SelectCopy := [.oldLocal, .oldOwner, .dummyLocal,
  .dummySize, .dummyDifference]

protected theorem SelectCopy.enumList_nodup : SelectCopy.enumList.Nodup := by decide

instance instFintypeSelectCopy : Fintype SelectCopy where
  elems := ⟨SelectCopy.enumList, SelectCopy.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAdd
  | prefixOffset | darts
  deriving DecidableEq

protected abbrev SelectAdd.enumList : List SelectAdd := [.prefixOffset, .darts]

protected theorem SelectAdd.enumList_nodup : SelectAdd.enumList.Nodup := by decide

instance instFintypeSelectAdd : Fintype SelectAdd where
  elems := ⟨SelectAdd.enumList, SelectAdd.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAddStage
  | scan | restore
  deriving DecidableEq

protected abbrev SelectAddStage.enumList : List SelectAddStage := [.scan, .restore]

protected theorem SelectAddStage.enumList_nodup : SelectAddStage.enumList.Nodup := by decide

instance instFintypeSelectAddStage : Fintype SelectAddStage where
  elems := ⟨SelectAddStage.enumList, SelectAddStage.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectControl
  | compare (stage : MachineUnaryLessAt.Label)
  | choose
  | copy (kind : SelectCopy) (stage : MachineUnaryAffineAt.Label)
  | subtract
  | add (kind : SelectAdd) (stage : SelectAddStage)
  | cleanup (i : Fin 5)
  deriving DecidableEq, Fintype

abbrev SelectLabel := MachineCloudSelect.Label ⊕ SelectControl

def afterCleanup (i : Fin 5) : Option SelectLabel :=
  if h : i.val + 1 < 5 then some (.inr (.cleanup ⟨i.val + 1, h⟩)) else none

abbrev CoreTape := Fin 27

def dummySelectSteps (j k o m : Nat) : Nat :=
  (2 * (j + 1) + 1) + (2 * (k + 1) + 1) + (k + 1) +
    (2 * (j - k + 1) + 1) + 2 * (o + 1) + 2 * (m + 1) + (j + k + 7)

theorem dummySelectSteps_eq (j k o m : Nat) (h : k ≤ j) :
    dummySelectSteps j k o m = 5 * j + 2 * k + 2 * o + 2 * m + 21 := by
  unfold dummySelectSteps
  omega

/-- The fixed core rotor roles use the agreed reusable 27-tape frame. -/
def coreRotorTapes : Fin 8 → CoreTape := ![3, 7, 10, 11, 12, 9, 13, 14]

/-- Tail, selected destination, return port, scratch and emitted row fields. -/
def coreFinishTapes : Fin 8 → CoreTape := ![1, 15, 14, 9, 24, 25, 26, 8]

def coreCleanupTape : Fin 10 → CoreTape := ![10, 11, 12, 13, 14, 15, 9, 16, 17, 18]

/-- For fixed cloud degree q this is affine in the lengths and unary values
on the actual input tapes. All relation/cleanup constants are included. -/
def coreTimeBound (q graphLength rotorLength x v i k o m outputLength : Nat) : Nat :=
  (5 * q + 32) * rotorLength + 10 * graphLength + 2 * i + 13 * v + 5 * k +
    (5 * q + 10) * (m + o) + 4 * x + 2 * outputLength + 8 * q + 41066

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

open Turing
open UniqueGamesTheorem.Foundations.PCP
open scoped BigOperators

inductive Label
  | init | copyFirst | copySecond | guard | done
  | padding (l : MachineCloudPadding.Label)
  | add | clearCount | clearLevel | increment
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

open Turing
open UniqueGamesTheorem.Foundations.PCP

inductive Extra
  | padding | level
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.padding, .level]

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance instFintypeExtra : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 27 ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- Original table, affine query, copied scan, owner output, and scratch. -/
def ownerTapes : Fin 5 → Tape := ![.inl 0, .inl 9, .inl 10, .inl 2, .inl 11]

variable {σ : Type}

/-- Boundary data is a specification of physical tape contents, never part
of the machine's finite control state. All eighteen core work tapes are empty. -/
structure Data where
  table : List Bool
  globalIndex : List Bool
  owner : List Bool
  localRank : List Bool
  count : List Bool
  offset : List Bool
  darts : List Bool
  rotor : List Bool
  output : List Bool
  padding : List Bool
  level : List Bool

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def querySteps (v x : Nat) : Nat := 2 * (x + 2) + 2 * (v + 2) + 1

def overhead (N x v : Nat) : Nat :=
  (2*x + 5*N + 6) + 2 + (N+1) + 2*(x+2) + 2*(v+2) + 1 +
    (5*N + 3*(v+x+2) + 6) + (v+x+3) + (N+1) + 2 + (v+2) + 2

theorem overhead_le (N x v : Nat) (hx : x ≤ N) (hv : v ≤ N) :
    overhead N x v ≤ 40*(N+1) := by
  unfold overhead
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

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

open Turing
open MachineCloudPadding

abbrev CoreTape := Fin 27

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularDummyRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

open Turing

abbrev Tape := Fin 6
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | affine (stage : MachineUnaryAffineAt.Label)
  | row (stage : MachineDummyRows.Label 1)
  | reverse | relation
  deriving DecidableEq, Fintype

def reverseIndex (q x : Nat) : Nat := (q + 1) * x + q

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

/-- For each fixed degree, the exact cost is linear in index and prior output. -/
def timeBound (q x outputLength : Nat) : Nat :=
  (5 * q + 11) * x + 2 * outputLength + 5 * q + 40986

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularDummyRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

open Turing PCP

abbrev Tape := MachineRegularOriginalRow.Tape
abbrev Alphabet := MachineRegularOriginalRow.Alphabet

def cleanupTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update base 2 []) 3 []) 4 []) 6 []) 7 []

def cleanupSteps (base : Tape → List Bool) : Nat :=
  ((base 2).length + 1) + ((base 3).length + 1) + ((base 4).length + 1) +
    ((base 6).length + 1) + ((base 7).length + 1)

theorem join_trace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (5 * q + 20) * inputLength + 2 * outputLength + 5 * q + 40995

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularVertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

open Turing PCP MachineRegularInternalRow

variable {σ Λ : Type}

/-- A prefix of the emitted rows, defined without any execution hypothesis. -/
def portBits {q : Nat} (bits : Fin q → List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => portBits bits k ++ if h : k < q then bits ⟨k, h⟩ else []

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

/-- Uniform bound on a serialized row in the actual output table. -/
def rowSizeBound (q vertices : Nat) : Nat := vertices + vertices * (q + 1) + 8192

theorem portBits_length_le {q : Nat} (bits : Fin q → List Bool) (bound : Nat)
    (hbits : ∀ p, (bits p).length ≤ bound) (k : Nat) :
    (portBits bits k).length ≤ k * bound := by
  induction k with
  | zero => simp only [portBits, List.length_nil, Nat.zero_mul, le_refl]
  | succ k ih =>
    rw [portBits, List.length_append]
    split_ifs with h
    · have hp := hbits ⟨k, h⟩
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih hp
    · simp only [List.length_nil, Nat.add_zero]
      exact ih.trans (Nat.mul_le_mul_right bound (by omega))

def portTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  q * coreTimeBound q graphLength rotorLength x v i k o m
    (outputLength + q * rowSizeBound q vertices)

def originalTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularOriginalClean.timeBound q graphLength
      (outputLength + q * rowSizeBound q vertices)

def dummyTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularDummyRow.timeBound q x (outputLength + q * rowSizeBound q vertices)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

open Turing PCP
abbrev MetaState := MachineRegularMetadata.State Unit

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBodyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing PCP
open PreprocessingMachineBounds MachineRegularOriginalBody

theorem originalTimeBound_le (q L R x v i k o m O V W R' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ W) (hV : V ≤ W) :
    MachineRegularVertexBlock.originalTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.originalTimeBound q W R' W W W W W W W W := by
  unfold MachineRegularVertexBlock.originalTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularOriginalClean.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

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

open Turing

/-- Constructor-by-constructor equality for a fixed sum of tape alphabets. -/
def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerProgram
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

open Turing PCP
open PreprocessingRegularLoopWords

abbrev MetaState := MachineRegularOriginalBody.MetaState

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing PCP
open PreprocessingRegularLoopWords

theorem joinTrace {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBodyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing PCP
open PreprocessingMachineBounds PreprocessingRegularLoopWords

theorem dummyTimeBound_le (q L R x v i k o m O V W R' O' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ O') (hV : V ≤ W) :
    MachineRegularVertexBlock.dummyTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.dummyTimeBound q W R' W W W W W W O' W := by
  unfold MachineRegularVertexBlock.dummyTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularDummyRow.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

end

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

open Turing
open UniqueGamesTheorem.Foundations.PCP

namespace Header

inductive Extra
  | m | index | work | scratch | vertices | darts | emit | output
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.m, .index, .work, .scratch, .vertices, .darts,
  .emit, .output]

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance instFintypeExtra : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (σ : Type) := MachineCloudPrefix.State σ

inductive Field
  | vertices | darts
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.vertices, .darts]

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance instFintypeField : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive CopyPhase
  | count | rEmit | nEmit
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.count, .rEmit, .nEmit]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {σ : Type}

theorem appendTrace {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end Header

namespace Fuel

variable {K Λ σ : Type} [DecidableEq K]

/-- The outer loop consumes one real unary fuel bit. The zero delimiter is
consumed on exit; its temporary finite register is reset on both branches. -/
def guard (fuel : K) (body : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop fuel (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.getD false)
      (.load (fun s => (s.1, none)) (.goto fun _ => body))
      (.load (fun s => (s.1, none))
        (match exit with | some label => .goto fun _ => label | none => .halt)))

/-- Unary successor needs one physical push and no unbounded register. -/
def increment (counter : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .push counter (fun _ => true) (.goto fun _ => next)

end Fuel

namespace Top

def sumDecidableEq {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

inductive CopyPhase
  | old | owner
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.old, .owner]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

def counterStacks (old owners dummy work : List Bool) : Fin 4 → List Bool :=
  ![old, owners, dummy, work]

theorem joinTrace_p0 {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTableTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing
open UniqueGamesTheorem.Foundations.PCP

theorem joinTrace_p1 {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem normalizeEmptyAppend {A : Type*} (output : List Bool → A)
    (bits : List Bool) : output ([] ++ bits) = output bits :=
  congrArg output (List.nil_append bits)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryEqualityBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

open Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

inductive Label
  | seedLeft | scanLeft | restoreLeft
  | seedRight | scanRight | restoreRight
  | compare | equal | different
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seedLeft, .scanLeft, .restoreLeft, .seedRight,
  .scanRight, .restoreRight, .compare, .equal, .different]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Two fixed exits, each containing only literal push instructions. -/
def emit (destination : K) (bit : Bool) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (if bit then .push destination (fun _ => true) (exitAt exit) else exitAt exit)

def copySteps (n : Nat) : Nat := 2 * (n + 1) + 1
def compareSteps (a b : Nat) : Nat := max (a + 1) (b + 1) + 1
def steps (a b : Nat) : Nat := copySteps a + copySteps b + compareSteps a b + 1

theorem steps_le (a b : Nat) : steps a b ≤ 3 * (a + b) + 9 := by
  unfold steps copySteps compareSteps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryEqualityBit

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PortTableLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact word offsets in executable port tables

These are optional list-lookup equalities for the unary-word stream consumed by
the lookup machine. They expose the stored tail, reverse index, and predicate
bit at their actual positions in the existing graph-table serialization.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PortTableLookup

theorem flatMap_word {α β : Type*} (f : α → List β)
    (width j : Nat) (hj : j < width) :
    ∀ (rows : List α), (∀ a ∈ rows, (f a).length = width) →
      ∀ (i : Nat) (row : α), rows[i]? = some row →
        (rows.flatMap f)[width * i + j]? = (f row)[j]? := by
  intro rows
  induction rows with
  | nil =>
      intro _ i row selected
      simp at selected
  | cons a rows ih =>
      intro hwidth i row selected
      have ha : (f a).length = width := hwidth a (by simp)
      cases i with
      | zero =>
          have heq : a = row := by simpa using selected
          subst row
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          have selected' : rows[i]? = some row := by simpa using selected
          have hskip : (f a).length ≤ width * (i + 1) + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          have hoff : width * (i + 1) + j - (f a).length = width * i + j := by
            rw [ha, Nat.mul_add, Nat.mul_one]
            omega
          rw [List.flatMap_cons, List.getElem?_append_right hskip, hoff]
          exact ih (fun b hb => hwidth b (by simp [hb])) i row selected'

end UniqueGamesTheorem.Foundations.PCP.PortTableLookup

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineRelationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def address (vertex : Fin n) (port : Fin d) (position : Fin 4096) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 4 + position.val)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelation

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def reverseRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 6

def endpointRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5 else 6

theorem reverseRole_injective : Function.Injective reverseRole := by decide
theorem endpointRole_injective : Function.Injective endpointRole := by decide
theorem source_outside_reverse : ∀ i, (1 : Fin 7) ≠ reverseRole i := by decide
theorem reverse_outside_endpoint : ∀ i, (4 : Fin 7) ≠ endpointRole i := by decide

def reverseTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ reverseRole
def endpointTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ endpointRole

def reverseAddress (vertex : Fin n) (port : Fin d) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 3)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape (t : Nat) := Fin 6 ⊕ Fin (t + 1)

def first (t : Nat) : Fin (t + 1) := ⟨0, by omega⟩

def shift (t : Nat) : Tape t → Tape (t + 1) := Sum.map id Fin.succ

theorem shift_injective (t : Nat) : Function.Injective (shift t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [shift]

def rotorRole (t : Nat) (i : Fin 7) : Tape (t + 1) :=
  if i = 0 then .inl 0 else if i = 1 then .inr (first (t + 1)) else
  if i = 2 then .inl 1 else if i = 3 then .inl 2 else
  if i = 4 then .inl 3 else if i = 5 then .inr (first t).succ else .inl 4

theorem rotorRole_injective (t : Nat) : Function.Injective (rotorRole t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rotorRole, first, Fin.ext_iff]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

/-- Table, query, scan, reverse identifier, scratch, selected endpoint. -/
def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

/-- Position zero is the caller's starting vertex; later positions are the
separate physical trajectory tapes. -/
def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

theorem wordSharedRole_injective (target : Bool) : Function.Injective (wordSharedRole target) := by
  cases target <;> decide

theorem wordSharedRole_ne_start (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 1 := by
  cases target <;> decide

theorem trajectoryPlacement_injective {t max : Nat} (ht : t ≤ max) :
    Function.Injective (trajectoryPlacement ht) := by
  intro a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro _
      rfl
    · intro h
      change (Sum.inl (1 : Fin 11) : Tape max) = .inr (Fin.castLE ht j) at h
      cases h
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (1 : Fin 11) at h
      cases h
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inr (Fin.castLE ht j) at h
      have hc : Fin.castLE ht i = Fin.castLE ht j := Sum.inr.inj h
      have hv : i.val = j.val := congrArg (fun x : Fin max => x.val) hc
      have hij : i = j := Fin.ext hv
      exact congrArg Fin.succ hij

theorem wordShared_ne_trajectory {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : Fin 6) :
    ∀ j : Fin (t + 1),
      (Sum.inl (wordSharedRole target i) : Tape max) ≠ trajectoryPlacement ht j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inl (1 : Fin 11) at h
    exact wordSharedRole_ne_start target i (Sum.inl.inj h)
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inr (Fin.castLE ht k) at h
    cases h

/-- Every tape used by a bounded word is placed on its own physical tape. -/
theorem wordPlacement_injective {t max : Nat} (ht : t ≤ max) (target : Bool) :
    Function.Injective (wordPlacement ht target) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact congrArg Sum.inl (wordSharedRole_injective target (Sum.inl.inj h))
      | inr j =>
          exact False.elim (wordShared_ne_trajectory ht target i j h)
  | inr i =>
      cases b with
      | inl j =>
          exact False.elim (wordShared_ne_trajectory ht target j i h.symm)
      | inr j =>
          exact congrArg Sum.inr (trajectoryPlacement_injective ht h)

theorem relationPlacement_injective (max : Nat) : Function.Injective (relationPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [relationPlacement]

theorem equalityPlacement_injective (max : Nat) : Function.Injective (equalityPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPlacement]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineTapes

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineEqualityField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual producer for equality of two bounded walk endpoints

The two port words are fixed finite control. Each executes against the live
rotor table from the same preserved starting vertex. Their endpoint fields
are compared by the physical unary equality primitive. The emitted field is
the Boolean equality of the two actual walk endpoints.

Work tapes may retain arbitrary histories. The table, start, scratch and two
comparison copies satisfy exact frame theorems. There is no execution or
running-time premise in the composite trace theorem.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape := PoweringMachineTapes.Tape
abbrev State := MachineUnaryEqualityBit.State

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {u v : Nat}
    (first : f^[u] a = b) (second : f^[v] b = c) : f^[u + v] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineEqualityField

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-control preparation and enumeration for the powered-table
machine. The degree and radius determine a fixed multiplier `B = 2*d^t`.
Only the input vertex count varies at runtime, and it is stored on unary
tapes. The header machine consumes a cloned first input field, preserving
its unread suffix, and writes the three fields needed by the outer loop.

The row enumeration lemmas specify the canonical suffix invariant used with
`MachineCountedLoop`. They do not stand in for the caller's per-row machine
traces, which must be supplied by the actual walk and relation evaluator. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

protected abbrev HeaderTape.enumList : List HeaderTape := [.source, .counter, .vertices, .darts]

protected theorem HeaderTape.enumList_nodup : HeaderTape.enumList.Nodup := by decide

instance instFintypeHeaderTape : Fintype HeaderTape where
  elems := ⟨HeaderTape.enumList, HeaderTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive HeaderLabel
  | initialize_ | scan
  deriving DecidableEq

protected abbrev HeaderLabel.enumList : List HeaderLabel := [.initialize_, .scan]

protected theorem HeaderLabel.enumList_nodup : HeaderLabel.enumList.Nodup := by decide

instance instFintypeHeaderLabel : Fintype HeaderLabel where
  elems := ⟨HeaderLabel.enumList, HeaderLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

/-- A syntactic chain of a fixed number of true-bit pushes. -/
def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

theorem stepAux_pushTrue {K Λ σ : Type} [DecidableEq K]
    (destination : K) (count : Nat) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (pushTrue destination count next) state tapes =
      TM2.stepAux next state
        (Function.update tapes destination (List.replicate count true ++ tapes destination)) := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih =>
    rw [pushTrue, ih]
    simp [TM2.stepAux, List.replicate_succ, Function.update_idem]

/-- Each true bit from the first input field contributes one counter bit,
one vertex-header bit, and `B` dart-header bits. No numeric register is used. -/
def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize_ =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineLoop

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual powering initialization on the common finite tape set. The first
unary input field is copied by the affine machine and consumed by the checked
header program. The original input and every unrelated tape are preserved.
No runtime graph or vertex count is captured by the finite program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max
abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

/-- The unary start vertex and outer counter occupy the same physical tape. -/
def commonPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.start max then .inl .counter else .inr (.inl tape)

theorem commonPlacement_injective (max : Nat) : Function.Injective (commonPlacement max) := by
  intro a b h
  by_cases ha : a = PoweringMachineTapes.start max <;>
    by_cases hb : b = PoweringMachineTapes.start max <;>
      simp_all [commonPlacement]

@[simp] theorem commonPlacement_start (max : Nat) :
    commonPlacement max (PoweringMachineTapes.start max) = .inl .counter := by
  simp [commonPlacement]

@[simp] theorem commonPlacement_table (max : Nat) :
    commonPlacement max (PoweringMachineTapes.table max) =
      .inr (.inl (PoweringMachineTapes.table max)) := by
  simp [commonPlacement, PoweringMachineTapes.table, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_scratch (max : Nat) :
    commonPlacement max (PoweringMachineTapes.scratch max) =
      .inr (.inl (PoweringMachineTapes.scratch max)) := by
  simp [commonPlacement, PoweringMachineTapes.scratch, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_rowOutput (max : Nat) :
    commonPlacement max (PoweringMachineTapes.rowOutput max) =
      .inr (.inl (PoweringMachineTapes.rowOutput max)) := by
  simp [commonPlacement, PoweringMachineTapes.rowOutput, PoweringMachineTapes.start]

theorem commonPlacement_ne_finalOutput (max : Nat) (tape : PoweringMachineTapes.Tape max) :
    commonPlacement max tape ≠ finalOutput max := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, finalOutput, h]

theorem commonPlacement_ne_header (max : Nat) (tape : PoweringMachineTapes.Tape max)
    (field : HeaderTape) (hne : field ≠ .counter) :
    commonPlacement max tape ≠ .inl field := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, h, Ne.symm hne]

def castTapes {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ tapes

def castStatement {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Δ Λ σ := h ▸ q

def castConfiguration {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Δ Λ σ := h ▸ c

theorem castTapes_apply {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) (k : K) :
    castTapes h tapes k = cast (congrArg (fun alphabet => List (alphabet k)) h) (tapes k) := by
  cases h
  rfl

theorem castConfiguration_mk {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (label : Option Λ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    castConfiguration h ⟨label, state, tapes⟩ = ⟨label, state, castTapes h tapes⟩ := by
  cases h
  rfl

theorem stepAux_cast {K Λ σ : Type} [DecidableEq K]
    {Γ Δ : K → Type} (h : Γ = Δ) (q : TM2.Stmt Γ Λ σ)
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (castStatement h q) state (castTapes h tapes) =
      castConfiguration h (TM2.stepAux q state tapes) := by
  cases h
  rfl

def mergeTapes {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) : GlobalTape max → List Bool
  | .inl k => header k
  | .inr e => extra e

def initialGlobalTapes {max : Nat} (extra : ExtraTape max → List Bool) :
    GlobalTape max → List Bool := mergeTapes (fun _ => []) extra

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringGlobalEnumerationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit executable enumeration of the global powering tapes

The four header tapes come first, followed by the eleven shared roles, the
bounded trajectory tapes, and the final output tape. Both directions use
constructor cases and arithmetic sum encodings. No enumeration is selected
from a cardinality theorem.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

/-- The single extra output tape occupies its unique local index. -/
def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

end UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

open Turing
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Alphabet (_ : K) := Bool

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

omit [DecidableEq K] in
theorem lookupTapes_injective (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) : Function.Injective (lookupTapes placement) := by
  intro i j h
  exact (Fin.succ_injective _) ((PoweringMachineTapes.relationPlacement_injective max) (distinct h))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

open Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

open Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev Command (d max : Nat) := {op : Instruction d // op.radius ≤ max}

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

open Turing
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

/-- The existing word placement, with its result directed to row-output 10. -/
def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

theorem headerPlacement_injective {t max : Nat} (h : t ≤ max) :
    Function.Injective (headerPlacement h) :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)).injective.comp (wordPlacement_injective h false)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

open Turing

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

def copySteps (n m : Nat) : Nat := (2 * (m + 1) + 1) + (2 * (n + 1) + 1)

theorem copySteps_eq (n m : Nat) : copySteps n m = 2 * (n + m) + 6 := by
  unfold copySteps
  omega

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringPlanBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Execution budget of the concrete powered-row field plan

The cost is the sum of the actual relation and endpoint-comparison transition
counts. Each fixed command scans only the serialized input graph. The execution
certificates below instantiate the concrete plan trace; no execution witness or
running-time bound is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringPlanBudget

open Turing PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

/-- A common bound for either concrete field operation of radius at most `max`. -/
def fieldBudget (max inputLength : Nat) : Nat :=
  (28 * max + 10) * inputLength + 24 * max + 15

end UniqueGamesTheorem.Foundations.Complexity.PoweringPlanBudget

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_PoweringMachineRowBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

open Turing PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev capacity (n : Nat) := 2 * (n + 1)

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringTableLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex-major serialization of the actual powering table

Each vertex contributes a fixed number of consecutive stored dart rows. The
identities below group the actual vector, including every predicate entry, and
then apply the shared word codec. They do not assume an output layout or assert
a machine running time. Unary bit lengths can vary with the stored indices.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

open UniqueGamesTheorem.Foundations.Complexity

/-- One adjacent orientation pair for each recorded port word. -/
def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

theorem vector_toList_ofFn {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

/-- Regroup a stored vector without changing, omitting, or permuting a row. -/
theorem vector_blocks {α : Type*} {m vertices width : Nat}
    (sameCount : m = vertices * width) (rows : Vector α m) :
    rows.toList = (List.finRange vertices).flatMap (fun v =>
      List.ofFn (fun j : Fin width =>
        rows[Fin.cast sameCount.symm (finProdFinEquiv (v, j))])) := by
  have atIndex (v : Fin vertices) (j : Fin width)
      (h : v.val * width + j.val < vertices * width) :
      (⟨v.val * width + j.val, h⟩ : Fin (vertices * width)) =
        finProdFinEquiv (v, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [vector_toList_ofFn rows,
    List.ofFn_congr sameCount (fun i : Fin m => rows[i]), List.ofFn_mul]
  simp only [atIndex, List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open UniqueGamesTheorem.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .cursor, .scan, .vertices, .darts,
  .counter, .edge, .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight,
  .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool

/-- Self-loop flag, comparison mismatch flag, and second head register. -/
abbrev Flags := Bool × Bool × Option Bool

def setupPorts : Fin 7 → Tape :=
  ![.original, .cursor, .vertices, .darts, .counter, .scratch, .edge]

def headPorts : Fin 6 → Tape :=
  ![.original, .reverseIndex, .scan, .indexScan, .head, .scratch]

def rowSources : Fin 5 → Tape := ![.vertices, .darts, .edge, .tail, .head]
def headerSources : Fin 2 → Tape := ![.vertices, .darts]
def fieldPorts : Fin 3 → Tape := ![.tail, .reverseIndex, .head]

def cleanupPorts : Fin 15 → Tape :=
  ![.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight, .reversed]

theorem cleanupPorts_cover (tape : Tape) (h : tape ≠ .output) :
    ∃ i, cleanupPorts i = tape := by
  cases tape
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact (h rfl).elim

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

inductive Label
  | leftFirst | leftSecond | rightFirst | rightSecond | compare
  | equalStore | differentStore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftFirst, .leftSecond, .rightFirst,
  .rightSecond, .compare, .equalStore, .differentStore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {q : Nat} {Λ : Type}

def comparisonTime (tailName headName : Nat) : Nat :=
  2 * (tailName + 2) + 2 * (headName + 2) + max (tailName + 1) (headName + 1) + 2

theorem comparisonTime_le_of_lt (tailName headName N : Nat)
    (hTail : tailName < N) (hHead : headName < N) :
    comparisonTime tailName headName ≤ 5 * N + 6 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Addresses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Addresses

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_EmitRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual alphabet-reduction row template. The old predicate and the loop flag
are finite registers. All unbounded quantities reside in five preserved unary
tapes. The fixed event/slot/orientation order is retained without deduplication.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open Emitter

abbrev Context (q : Nat) := Vector Bool (q * q) × Bool

theorem vector_list_ofFn {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

theorem flatMap_length_le {α β : Type} (items : List α) (f : α → List β)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    have hh := bounded item (by simp)
    have ht := ih (fun x hx => bounded x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Setup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev Ports (K : Type) := Fin 7 → K

inductive Label
  | copyFirst | copySecond | verticesStart | verticesLoop
  | dartsStart | dartsLoop | counterFirst | counterSecond | initialize_
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .verticesStart,
  .verticesLoop, .dartsStart, .dartsLoop, .counterFirst, .counterSecond, .initialize_]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Setup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Initialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual setup-to-guard execution of the alphabet-table driver. The preserved
input is parsed by Setup; the finite header template runs through an explicit
state equivalence. The resulting loop invariant is a complete tape equation.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Initialization

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationEmitMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationEmitMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open NormalizationWords

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Signs) × Option Bool

def clean (ambient : A) (signs : Signs) : State A := ((ambient, signs), none)

def sourceIndex : NameRef → Fin 6
  | .old i => ⟨i.val + 1, by have := i.isLt; omega⟩
  | .fresh _ => 0

theorem sourceIndex_ne_scratch (name : NameRef) : sourceIndex name ≠ 4 := by
  cases name with
  | old i =>
      intro h
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp only [sourceIndex] at hv
      omega
  | fresh i => simp [sourceIndex]

theorem sourceIndex_ne_output (name : NameRef) : sourceIndex name ≠ 5 := by
  cases name with
  | old i =>
      intro h
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp only [sourceIndex] at hv
      omega
  | fresh i => simp [sourceIndex]

inductive LocalLabel
  | copyOut
  | copyBack
  | emit
  deriving DecidableEq

protected abbrev LocalLabel.enumList : List LocalLabel := [.copyOut, .copyBack, .emit]

protected theorem LocalLabel.enumList_nodup : LocalLabel.enumList.Nodup := by decide

instance instFintypeLocalLabel : Fintype LocalLabel where
  elems := ⟨LocalLabel.enumList, LocalLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem sourceValue_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (name : NameRef) : sourceValue names freshBase name ≤ maximum := by
  cases name with
  | old i => exact nameBounds i
  | fresh i => exact freshBound

end PerfectCompleteness.NormalizationEmitMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationReadMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationReadMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity
abbrev Alphabet {K : Type} (_ : K) := Bool

inductive Label where
  | field (slot : Fin 3)
  | sign (slot : Fin 3)
  deriving DecidableEq, Fintype

section Placement

variable {K Λ A : Type} [DecidableEq K]

def afterSign (labels : Label → Λ) (exit : Option Λ) (slot : Fin 3) : Option Λ :=
  if slot = 0 then some (labels (.field 1))
  else if slot = 1 then some (labels (.field 2)) else exit

@[simp] theorem afterSign_zero (labels : Label → Λ) (exit : Option Λ) :
    afterSign labels exit 0 = some (labels (.field 1)) := rfl

@[simp] theorem afterSign_one (labels : Label → Λ) (exit : Option Λ) :
    afterSign labels exit 1 = some (labels (.field 2)) := rfl

@[simp] theorem afterSign_two (labels : Label → Λ) (exit : Option Λ) :
    afterSign labels exit 2 = exit := rfl

variable (tape : Fin 4 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (exit rejected : Option Λ)
variable (base : K → List Bool) (ambient : A)

include distinct

omit [DecidableEq K] distinct in
theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Placement

end PerfectCompleteness.NormalizationReadMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationLoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationLoopMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity
open NormalizationWords

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Signs) × Option Bool
abbrev clean (ambient : A) (signs : Signs) : State A := NormalizationEmitMachine.clean ambient signs
def reset (ambient : A) : State A := clean ambient (fun _ => false)

def readerIndex : Fin 4 → Fin 9
  | 0 => 0
  | 1 => 4
  | 2 => 5
  | 3 => 6

def emitterIndex : Fin 6 → Fin 9
  | 0 => 1
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 8

def oldIndex (slot : Fin 3) : Fin 9 := ⟨slot.val + 4, by have := slot.isLt; omega⟩

def readerTapes (tape : Fin 9 → K) : Fin 4 → K := fun i => tape (readerIndex i)
def emitterTapes (tape : Fin 9 → K) : Fin 6 → K := fun i => tape (emitterIndex i)

omit [DecidableEq K] in
theorem readerTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (readerTapes tape) :=
  distinct.comp (by decide : Function.Injective readerIndex)

omit [DecidableEq K] in
theorem emitterTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (emitterTapes tape) :=
  distinct.comp (by decide : Function.Injective emitterIndex)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => reset state.1.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def loopTapes (tape : Fin 9 → K) (base : K → List Bool) (input : List Bool)
    (freshBase remaining : Nat) (clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    (tape 0) input) (tape 1) (List.replicate freshBase true))
    (tape 2) (List.replicate remaining true)) (tape 3) clauseCounter) (tape 8) output

theorem loopTapes_fresh (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 1) =
      List.replicate freshBase true := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_remaining (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 2) =
      List.replicate remaining true := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_count (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 3) =
      clauseCounter := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem update_remaining (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining replacement : Nat)
    (clauseCounter output : List Bool) :
    Function.update (loopTapes tape base input freshBase remaining clauseCounter output)
        (tape 2) (List.replicate replacement true) =
      loopTapes tape base input freshBase replacement clauseCounter output := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 2
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_fresh (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining replacement : Nat)
    (clauseCounter output : List Bool) :
    Function.update (loopTapes tape base input freshBase remaining clauseCounter output)
        (tape 1) (List.replicate replacement true) =
      loopTapes tape base input replacement remaining clauseCounter output := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_count (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output replacement : List Bool) :
    Function.update (loopTapes tape base input freshBase remaining clauseCounter output)
        (tape 3) replacement =
      loopTapes tape base input freshBase remaining replacement output := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 3
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, reset state.1.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end PerfectCompleteness.NormalizationLoopMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationMachine


open Turing UniqueGamesTheorem.Foundations Complexity
abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool
abbrev State := NormalizationLoopMachine.State Unit

def loopTapes : Fin 9 → Tape := Fin.castSucc

theorem loopTapes_injective : Function.Injective loopTapes := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Tape => k.val) h

def tapes (input fresh remaining clauseCounter reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then fresh else if k = 2 then remaining
    else if k = 3 then clauseCounter else if k = 8 then reversed else if k = 9 then output else []

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1) ^ 2

end PerfectCompleteness.NormalizationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TreeShapeBounds

open scoped BigOperators

def leafCount (branch : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => branch n * leafCount branch n

def domainCountBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  (7 ^ t) ^ leafCount branch n

def functionCountBound (branch : Nat → Nat) (n t : Nat) : Nat :=
  2 ^ domainCountBound branch n t

def arrayCountBound (branch : Nat → Nat) : (n t : Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 1
  | n + 1, t, rows =>
      functionCountBound branch (n + 1) t ^ rows (n + 1) *
        arrayCountBound branch n t rows ^ branch n

end PerfectCompleteness.TreeShapeBounds


namespace PerfectCompleteness.FixedBranching

noncomputable section

def extend {n : Nat} (prior : Fin n → Nat) : Nat → Nat :=
  fun k => if h : k < n then prior ⟨k, h⟩ else 0

def cleanRate (cost : Nat) (L : ℝ) : ℝ := 1 / ((48000 : ℝ) * cost * L)

theorem rational_probability {m : Nat} (hm : 2 ≤ m) :
    0 < (1 : ℚ) / (m : ℚ) ^ 2 ∧ (1 : ℚ) / (m : ℚ) ^ 2 < 1 := by
  have hmr : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℚ) < (m : ℚ) ^ 2 := by positivity
  constructor
  · positivity
  · apply (div_lt_one hp).2
    nlinarith

end
end PerfectCompleteness.FixedBranching


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UniformDifference

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B H : Type*} [Fintype B] [Fintype H] [AddGroup H]

def difference (old : B → H) (p : B × H) : B × H := (p.1, p.2 - old p.1)

end
end PerfectCompleteness.UniformDifference

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArrayInteriorHiddenLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayInteriorHiddenLaw

open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

def reorder (A H V R : Type*) :
    A × (H × (V × R)) ≃ H × (V × (A × R)) where
  toFun z := (z.2.1, (z.2.2.1, (z.1, z.2.2.2)))
  invFun z := (z.2.2.1, (z.1, (z.2.1, z.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.WholeArrayInteriorHiddenLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalOwnBucketSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalOwnBucketSplit

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

def sumEmpty (A : Type*) : A ≃ A ⊕ Empty where
  toFun := Sum.inl
  invFun := Sum.elim id Empty.elim
  left_inv _ := rfl
  right_inv x := by
    cases x with
    | inl a => rfl
    | inr e => exact Empty.elim e

def swapFirstSum (R A O : Type*) : R ⊕ (A ⊕ O) ≃ A ⊕ (R ⊕ O) where
  toFun
    | .inl r => .inr (.inl r)
    | .inr (.inl a) => .inl a
    | .inr (.inr o) => .inr (.inr o)
  invFun
    | .inl a => .inr (.inl a)
    | .inr (.inl r) => .inl r
    | .inr (.inr o) => .inr (.inr o)
  left_inv x := by rcases x with r | (a | o) <;> rfl
  right_inv x := by rcases x with a | (r | o) <;> rfl

end
end PerfectCompleteness.OriginalOwnBucketSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SparseProjection

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def localDensity (β : ℝ) (q : (i : I) → Ω i → ℝ) (i : I) (x : Ω i) : ℝ :=
  1 - β + β * q i x

def density (β : ℝ) (q : (i : I) → Ω i → ℝ) (x : (i : I) → Ω i) : ℝ :=
  ∏ i, localDensity β q i (x i)

end
end PerfectCompleteness.SparseProjection


namespace PerfectCompleteness.ProjectionPosterior

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SparseProjection

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def posterior (β : ℝ) (q : (i : I) → Ω i → ℝ) (i : I) (x : Ω i) : ℝ :=
  β * q i x / localDensity β q i x

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem localDensity_positive (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x) (i : I) (x : Ω i) :
    0 < localDensity β q i x :=
  add_pos_of_pos_of_nonneg (sub_pos.mpr hβ') (mul_nonneg hβ (nonnegative i x))

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem posterior_nonnegative (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x) (i : I) (x : Ω i) :
    0 ≤ posterior β q i x :=
  div_nonneg (mul_nonneg hβ (nonnegative i x))
    (le_of_lt (localDensity_positive β hβ hβ' q nonnegative i x))

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem posterior_le_one (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x) (i : I) (x : Ω i) :
    posterior β q i x ≤ 1 := by
  apply (div_le_iff₀ (localDensity_positive β hβ hβ' q nonnegative i x)).mpr
  unfold localDensity
  linarith

end
end PerfectCompleteness.ProjectionPosterior


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutExteriorTransportLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutZero

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutZero

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutGroupedProjectionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalScalarProjection

open scoped BigOperators Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.OriginalScalarProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayGroupingTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayGroupingTransport

open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedCallBudgetLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedCallBudget

open scoped BigOperators

noncomputable section

def pairCount (rows repeats : Nat → Nat) (root cutoff : Nat) : Nat :=
  rows cutoff + OriginalCutCalls.count rows repeats root cutoff

def budget (depth : Nat) (rows repeats : Nat → Nat) : Nat :=
  1 + ∑ root : Fin (depth + 1), ∑ cutoff : Fin (depth + 1),
    pairCount rows repeats root.val cutoff.val

end
end PerfectCompleteness.FixedCallBudget


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedDecoderCleanRateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedDecoderCleanRate

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.FixedDecoderCleanRate

end

section

namespace PerfectCompleteness.FixedDecoderPairRate

noncomputable section

open scoped Classical
open FixedDecoderCleanRate

abbrev F2 := ZMod 2

end
end PerfectCompleteness.FixedDecoderPairRate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutAssembled

open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.LowerCutAssembled

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutBucketLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutBucketLocality

noncomputable section

open scoped Classical

abbrev F2 := ZMod 2

end
end PerfectCompleteness.LowerCutBucketLocality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutPair

open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.LowerCutPair

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutCalls

open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i depth : Nat}

def count (rows repeats : Nat → Nat) (root upper lower : Nat) : Nat :=
  OriginalCutCalls.count rows repeats root lower +
    ∏ h ∈ Finset.Ioc lower upper, 2 * repeats h

end
end PerfectCompleteness.UpperScalarCutCalls

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarFreshProjectionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperStoppedBuckets

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.UpperStoppedBuckets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_WholeCutGroupedProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutGroupedProjection

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutGroupedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ExtraCutCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExtraCutCall

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

def splitLast (calls : Nat) (A : Type*) :
    (Fin (calls + 1) → A) ≃ (Fin calls → A) × A where
  toFun x := (fun i => x i.castSucc, x (Fin.last calls))
  invFun z := Fin.lastCases z.2 z.1
  left_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last]
    · simp only [Fin.lastCases_castSucc]
  right_inv z := by
    apply Prod.ext
    · funext i
      simp only [Fin.lastCases_castSucc]
    · simp only [Fin.lastCases_last]

def middleSwap (A B C : Type*) : (A × B) × C ≃ (A × C) × B where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.ExtraCutCall

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalUsefulFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat}
  {n t : Nat}
  {O : Type*}
  [Fintype O]
  {Ω : O → Type*}

abbrev Sample (Ω : O → Type*) := (o : O) × Ω o

end
end PerfectCompleteness.HierarchicalUsefulFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceProjectedCanonicalQuery

open scoped Classical

noncomputable section

abbrev F2 := ZMod 2

end
end PerfectCompleteness.SourceProjectedCanonicalQuery


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedCutChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedCutChoices

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat}
  {n t : Nat}
  {Z : Fin (branch n) → Type*}

abbrev Choices := (child : Fin (branch n)) → Bool × Z child

end
end PerfectCompleteness.ProjectedCutChoices

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedCostEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SignedCostEnvelope

def payloadCoeff (w : Nat) : Nat :=
  (1 + 2 ^ (11 ^ w) + 6 * w) * (w + 3) + 1

def streamCoeff (w d : Nat) : Nat := (2 * payloadCoeff w + 2) * d

def endpointCoeff (w d : Nat) : Nat :=
  12 * w + 2 * payloadCoeff w + 3 * (streamCoeff w d) ^ 2 +
    16 * streamCoeff w d + 16

def bodyCoeff (w d : Nat) : Nat := 86 * w + d * (2 * endpointCoeff w d + 4) + 2

def degree (w : Nat) : Nat := 2 * w + 2

theorem le_scaled (a : Nat) {b : Nat} (hb : 1 ≤ b) : a ≤ a * b := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb

theorem one_le_envelope (w T : Nat) : 1 ≤ (T + 1) ^ degree w :=
  Nat.one_le_pow (degree w) (T + 1) (Nat.zero_lt_succ T)

theorem input_le_envelope (w T : Nat) : T + 1 ≤ (T + 1) ^ degree w :=
  Nat.le_pow (show 0 < degree w by unfold degree; omega)

theorem streamPower_le_envelope (w T : Nat) :
    (T + 1) ^ (w + 1) ≤ (T + 1) ^ degree w :=
  Nat.pow_le_pow_right (Nat.zero_lt_succ T) (by unfold degree; omega)

end PerfectCompleteness.SignedCostEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseReaderMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity
abbrev Alphabet {K : Type} (_ : K) := Bool

inductive Label where
  | read (label : NormalizationReadMachine.Label)
  | publish
  deriving DecidableEq, Fintype

def main : Label := .read (.field 0)

end PerfectCompleteness.SourceClauseReaderMachine


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_UnaryBlockCopyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UnaryBlockCopyMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def blockWords (values : Fin 6 → Nat) : List Nat :=
  [values 0, values 1, values 2, values 3, values 4, values 5]

def listValues (words : List Nat) (length_eq : words.length = 6) : Fin 6 → Nat :=
  fun i => words.get (Fin.cast length_eq.symm i)

theorem blockWords_listValues (words : List Nat) (length_eq : words.length = 6) :
    blockWords (listValues words length_eq) = words := by
  have h := (List.ofFn_congr length_eq words.get).symm
  rw [List.ofFn_get] at h
  change List.ofFn (listValues words length_eq) = words at h
  simp only [List.ofFn_succ, List.ofFn_zero] at h
  change blockWords (listValues words length_eq) = words at h
  exact h

section Placement

variable {K Λ A : Type} [DecidableEq K]

def nextField (labels : Fin 6 → Λ) (exit : Option Λ) (slot : Fin 6) : Option Λ :=
  if h : slot.val + 1 < 6 then some (labels ⟨slot.val + 1, h⟩) else exit

@[simp] theorem nextField_zero (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 0 = some (labels 1) := rfl
@[simp] theorem nextField_one (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 1 = some (labels 2) := rfl
@[simp] theorem nextField_two (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 2 = some (labels 3) := rfl
@[simp] theorem nextField_three (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 3 = some (labels 4) := rfl
@[simp] theorem nextField_four (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 4 = some (labels 5) := rfl
@[simp] theorem nextField_five (labels : Fin 6 → Λ) (exit : Option Λ) :
    nextField labels exit 5 = exit := rfl

variable (source destination : K) (distinct : source ≠ destination)
variable (labels : Fin 6 → Λ) (exit rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (base : K → List Bool) (ambient : A)

include distinct

omit [DecidableEq K] distinct in
theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Placement

end PerfectCompleteness.UnaryBlockCopyMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_UnaryBlockSkipMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UnaryBlockSkipMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def nextField {count : Nat} (labels : Fin (count + 1) → Λ) (exit : Option Λ)
    (slot : Fin (count + 1)) : Option Λ :=
  if h : slot.val + 1 < count + 1 then some (labels ⟨slot.val + 1, h⟩) else exit

variable (source : K) {count : Nat} (labels : Fin (count + 1) → Λ)
variable (exit rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (base : K → List Bool) (ambient : A)

omit [DecidableEq K] in
theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Placement

end PerfectCompleteness.UnaryBlockSkipMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseSelectMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseSelectMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
def clean (ambient : A) : State A := (ambient, none)

inductive Label
  | guard
  | skip (slot : Fin 7)
  | index (slot : Fin 1)
  | copy (slot : Fin 6)
  deriving DecidableEq, Fintype

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def selectTapes (tape : Fin 3 → K) (base : K → List Bool) (input : List Bool)
    (offset : Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base (tape 0) input)
    (tape 1) (List.replicate offset true)) (tape 2) output

theorem update_output (tape : Fin 3 → K) (base : K → List Bool)
    (input : List Bool) (offset : Nat) (output replacement : List Bool) :
    Function.update (selectTapes tape base input offset output) (tape 2) replacement =
      selectTapes tape base input offset replacement := by
  simp [selectTapes]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end PerfectCompleteness.SourceClauseSelectMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseLookupMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseLookupMachine


open Turing UniqueGamesTheorem.Foundations Complexity
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
def clean {A : Type} (ambient : A) : State A := (ambient, none)

inductive Label
  | tableOut | tableBack | indexOut | indexBack
  | header (slot : Fin 2)
  | select (label : SourceClauseSelectMachine.Label)
  | drain
  deriving DecidableEq, Fintype

def main : Label := .tableOut

def selectMap : Fin 3 → Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 5

variable {K Λ A : Type} [DecidableEq K]

def selectTapes (tape : Fin 6 → K) : Fin 3 → K := fun i => tape (selectMap i)

omit [DecidableEq K] in
theorem selectTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (selectTapes tape) :=
  distinct.comp (by decide : Function.Injective selectMap)

def workTapes (tape : Fin 6 → K) (base : K → List Bool)
    (input counter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base (tape 2) input)
    (tape 3) counter) (tape 5) output

@[simp] theorem workTapes_output (tape : Fin 6 → K) (base : K → List Bool)
    (input counter output : List Bool) :
    workTapes tape base input counter output (tape 5) = output := by
  simp [workTapes]

theorem workTapes_input (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output : List Bool) :
    workTapes tape base input counter output (tape 2) = input := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [workTapes, hd]

theorem workTapes_counter (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output : List Bool) :
    workTapes tape base input counter output (tape 3) = counter := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [workTapes, hd]

theorem update_input (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output replacement : List Bool) :
    Function.update (workTapes tape base input counter output) (tape 2) replacement =
      workTapes tape base replacement counter output := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 2
  · subst k; simp [workTapes, hd]
  · simp [workTapes, h, Function.update_apply]

theorem update_counter (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input counter output replacement : List Bool) :
    Function.update (workTapes tape base input counter output) (tape 3) replacement =
      workTapes tape base input replacement output := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 3
  · subst k; simp [workTapes, hd]
  · simp [workTapes, h, Function.update_apply]

theorem workTapes_empty (tape : Fin 6 → K) (base : K → List Bool) (output : List Bool)
    (tableCopyEmpty : base (tape 2) = []) (indexCopyEmpty : base (tape 3) = []) :
    workTapes tape base [] [] output = Function.update base (tape 5) output := by
  have tableSelf := Function.update_eq_self (tape 2) base
  have indexSelf := Function.update_eq_self (tape 3) base
  rw [tableCopyEmpty] at tableSelf
  rw [indexCopyEmpty] at indexSelf
  simp only [workTapes, tableSelf, indexSelf]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.SourceClauseLookupMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceCoordinateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceCoordinateMachine


open Turing UniqueGamesTheorem.Foundations Complexity
variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def lookupMap (i : Fin 6) : Fin 10 := ⟨i.val, lt_trans i.isLt (by decide)⟩
def readerMap (i : Fin 4) : Fin 10 := ⟨i.val + 6, by have := i.isLt; omega⟩

def lookupTapes (tape : Fin 10 → K) : Fin 6 → K := fun i => tape (lookupMap i)
def readerTapes (tape : Fin 10 → K) : Fin 4 → K := fun i => tape (readerMap i)

omit [DecidableEq K] in
theorem lookupTapes_injective (tape : Fin 10 → K) (distinct : Function.Injective tape) :
    Function.Injective (lookupTapes tape) := by
  intro i j h
  have hv := congrArg (fun x : Fin 10 => x.val) (distinct h)
  exact Fin.ext hv

omit [DecidableEq K] in
theorem readerTapes_injective (tape : Fin 10 → K) (distinct : Function.Injective tape) :
    Function.Injective (readerTapes tape) := by
  intro i j h
  have hv := congrArg (fun x : Fin 10 => x.val) (distinct h)
  apply Fin.ext
  dsimp [readerMap] at hv
  omega

inductive Label
  | lookup (label : SourceClauseLookupMachine.Label)
  | restore
  | read (label : SourceClauseReaderMachine.Label)
  deriving DecidableEq, Fintype

def main : Label := .lookup SourceClauseLookupMachine.main

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.SourceCoordinateMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceTupleMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleMachine


open Turing UniqueGamesTheorem.Foundations Complexity
abbrev LocalLabel {width : Nat} (_ : Fin width) := SourceCoordinateMachine.Label

def localMain {width : Nat} (_ : Fin width) : SourceCoordinateMachine.Label :=
  SourceCoordinateMachine.main

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


open Turing UniqueGamesTheorem.Foundations Complexity
open MachineCloudPadding

abbrev Alphabet {K : Type} (_ : K) := Bool

end PerfectCompleteness.SourceTuplePlacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleResetPlacementLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleBodyPlacement


open Turing UniqueGamesTheorem.Foundations Complexity
abbrev Alphabet {K : Type} (_ : K) := Bool

abbrev Frame (D : Type) := (Option D × (Bool × Option Bool)) × Option Bool

end PerfectCompleteness.SourceTupleBodyPlacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SignedTupleLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SignedTupleLayout

open UniqueGamesTheorem.Foundations Complexity
open scoped Classical

noncomputable section

variable {width : Nat} {Extra U Desc : Type}

def frame (Desc : Type) : SourceTupleBodyPlacement.Frame Desc := ((none, (false, none)), none)

end
end PerfectCompleteness.SignedTupleLayout

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArrayBucketsLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayBucketsLaw

open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

def reorder (A B C : Type*) : A × (B × C) ≃ B × (A × C) where
  toFun z := (z.2.1, (z.1, z.2.2))
  invFun z := (z.2.1, (z.1, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.WholeArrayBucketsLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketDescriptorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BucketDescriptorLaw

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {D E T V : Type*} [Fintype D] [Fintype E] [Fintype T] [Fintype V]

def reorder (D E B V : Type*) :
    D × ((E × B) × V) ≃ Σ _ : E, D × (B × V) where
  toFun z := ⟨z.2.1.1, (z.1, (z.2.1.2, z.2.2))⟩
  invFun z := (z.2.1, ((z.1, z.2.2.1), z.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.BucketDescriptorLaw

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
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat}
  {n i j t v m : Nat}
  (rows repeats : Nat → Nat)
  (hupper : j + 1 ≤ n)
  (hij : i < j)

def upperLevel : Fin n := ⟨j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hupper⟩

end
end PerfectCompleteness.StoppedProjectedUsefulEvent

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedDescriptorStageMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedDescriptorStageMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat}
  {n t q : Nat}
  {rows repeats : Nat → Nat}
  (hq : 0 < q)

variable (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

variable [Fintype A] [DecidableEq A]

theorem stageBudget (cost : Nat) : 1 + (cost + (1 + 1)) ≤ cost + 3 := by
  omega

end
end PerfectCompleteness.SignedDescriptorStageMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedTupleCleanupMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTuplePreparationMachine


open Turing UniqueGamesTheorem.Foundations Complexity
open SignedTupleLayout
open scoped Classical

noncomputable section

variable {width : Nat} {Extra U Desc Λ : Type}

def variableEquiv (width : Nat) : Fin (width * 3) ≃ Fin width × Fin 3 := finProdFinEquiv.symm

def budget (width tableLength : Nat) : Nat :=
  width * (2 * tableLength + 3) + width * (60 * (tableLength + 1)) +
    (width * 3) * (2 * tableLength + 3)

theorem budget_le (width tableLength : Nat) :
    budget width tableLength ≤ 72 * width * (tableLength + 1) := by
  unfold budget
  nlinarith [Nat.zero_le (width * tableLength)]

end
end PerfectCompleteness.SignedTuplePreparationMachine


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedTupleBodyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedTupleBodyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat}
  {n t q : Nat}
  {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (hn : 0 < n)
  (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

variable {K Λ A : Type} [DecidableEq K]

variable [Fintype A] [DecidableEq A]

theorem bodyBudgetOrder (preparation edges cleanup : Nat) :
    1 + (cleanup + (edges + (preparation + 1))) ≤
      1 + preparation + edges + cleanup + 1 := by
  omega

end
end PerfectCompleteness.SignedTupleBodyMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceIndexMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceIndexMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def clean (ambient : A) : State A := (ambient, none)

inductive Label
  | copyOut
  | copyBack
  | delimiter
  deriving DecidableEq

/-- A list enumerating every element of the type, which are all zero-argument constructors. (Generated by the `Fintype` deriving handler.)-/
protected abbrev Label.enumList : List Label := [.copyOut, .copyBack, .delimiter]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def main : Label := .copyOut

def steps (index : Nat) : Nat := 2 * (index + 1) + 1

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.SourceOccurrenceIndexMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceLoopMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceLoopMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
abbrev clean (ambient : A) : State A := SourceOccurrenceIndexMachine.clean ambient

def indexMap : Fin 3 → Fin 5
  | 0 => 2
  | 1 => 3
  | 2 => 4

def indexTapes (tape : Fin 5 → K) : Fin 3 → K := fun i => tape (indexMap i)

omit [DecidableEq K] in
theorem indexTapes_injective (tape : Fin 5 → K) (distinct : Function.Injective tape) :
    Function.Injective (indexTapes tape) :=
  distinct.comp (by decide : Function.Injective indexMap)

inductive Label
  | guard
  | index (label : SourceOccurrenceIndexMachine.Label)
  | field (slot : Fin 6)
  | tally
  deriving DecidableEq, Fintype

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def loopTapes (tape : Fin 5 → K) (base : K → List Bool) (input : List Bool)
    (remaining first : Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) input) (tape 1) (List.replicate remaining true))
    (tape 2) (List.replicate first true)) (tape 4) output

theorem loopTapes_output (tape : Fin 5 → K) (base : K → List Bool) (input : List Bool)
    (remaining first : Nat) (output : List Bool) :
    loopTapes tape base input remaining first output (tape 4) = output := by
  simp [loopTapes]

theorem update_output (tape : Fin 5 → K) (base : K → List Bool) (input : List Bool)
    (remaining first : Nat) (output replacement : List Bool) :
    Function.update (loopTapes tape base input remaining first output) (tape 4) replacement =
      loopTapes tape base input remaining first replacement := by
  simp [loopTapes]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end PerfectCompleteness.SourceOccurrenceLoopMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceOccurrenceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceOccurrenceMachine


open Turing UniqueGamesTheorem.Foundations Complexity
abbrev Tape := Fin 7
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

def clean : State := ((), none)

inductive Label
  | readVariables | readCount
  | loop (label : SourceOccurrenceLoopMachine.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 5 → Tape
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5

theorem loopTapes_injective : Function.Injective loopTapes := by decide

def tapes (input variableCounter remaining index reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then variableCounter else if k = 2 then remaining
    else if k = 3 then index else if k = 5 then reversed else if k = 6 then output else []

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X + Polynomial.C 1) ^ 2

end PerfectCompleteness.SourceOccurrenceMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOdometer
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

def setCoordinate (digits : Fin width → Fin radix) (depth : Nat) (value : Fin radix) :
    Fin width → Fin radix :=
  fun i => if i.val = depth then value else digits i

@[simp] theorem setCoordinate_self (digits : Fin width → Fin radix)
    (i : Fin width) (value : Fin radix) :
    setCoordinate digits i.val value i = value := by
  simp [setCoordinate]

theorem setCoordinate_eq_update (digits : Fin width → Fin radix)
    (coordinate : Fin width) (value : Fin radix) :
    setCoordinate digits coordinate.val value = Function.update digits coordinate value := by
  funext i
  by_cases same : i = coordinate
  · subst i
    simp [setCoordinate]
  · have different : i.val ≠ coordinate.val := fun h => same (Fin.ext h)
    simp [setCoordinate, same, different]

def fillCoordinates (digits : Fin width → Fin radix) {depth : Nat}
    (tuple : Fin depth → Fin radix) : Fin width → Fin radix :=
  fun i => if h : i.val < depth then tuple ⟨i.val, h⟩ else digits i

@[simp] theorem fillCoordinates_zero (digits : Fin width → Fin radix)
    (tuple : Fin 0 → Fin radix) : fillCoordinates digits tuple = digits := by
  funext i
  simp [fillCoordinates]

@[simp] theorem fillCoordinates_all (digits : Fin width → Fin radix)
    (tuple : Fin width → Fin radix) : fillCoordinates digits tuple = tuple := by
  funext i
  simp [fillCoordinates, i.isLt]

theorem fillCoordinates_snoc (digits : Fin width → Fin radix) {depth : Nat}
    (tuple : Fin depth → Fin radix) (value : Fin radix) :
    fillCoordinates digits (Fin.snoc tuple value) =
      fillCoordinates (setCoordinate digits depth value) tuple := by
  funext i
  by_cases hi : i.val < depth
  · have hi' : i.val < depth + 1 := by omega
    simp [fillCoordinates, hi, hi', Fin.snoc]
  · by_cases same : i.val = depth
    · simp [fillCoordinates, Fin.snoc, setCoordinate, same]
    · have hi' : ¬ i.val < depth + 1 := by omega
      simp [fillCoordinates, hi, hi', setCoordinate, same]

def visits : Nat → (Fin width → Fin radix) → List (Fin width → Fin radix)
  | 0, digits => [digits]
  | depth + 1, digits => (List.ofFn (fun value : Fin radix => value)).flatMap
      (fun value => visits depth (setCoordinate digits depth value))

end

noncomputable section Semantics

theorem foldl_chunks_eq_prefix {α β S : Type*}
    (order : List β) (chunk : α → List β) (step : α → S → S) (pack : List β → S)
    (hstep : ∀ (a : α) (earlier suffix : List β),
      order = earlier ++ chunk a ++ suffix →
        step a (pack earlier) = pack (earlier ++ chunk a))
    (xs : List α) (earlier suffix : List β)
    (split : order = earlier ++ xs.flatMap chunk ++ suffix) :
    xs.foldl (fun state a => step a state) (pack earlier) =
      pack (earlier ++ xs.flatMap chunk) := by
  induction xs generalizing earlier with
  | nil =>
      simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
  | cons a xs ih =>
      have currentSplit : order = earlier ++ chunk a ++ (xs.flatMap chunk ++ suffix) := by
        simpa only [List.flatMap_cons, List.append_assoc] using split
      rw [List.foldl_cons, hstep a earlier (xs.flatMap chunk ++ suffix) currentSplit]
      have restSplit : order = (earlier ++ chunk a) ++ xs.flatMap chunk ++ suffix := by
        simpa only [List.flatMap_cons, List.append_assoc] using split
      simpa only [List.flatMap_cons, List.append_assoc] using
        ih (earlier ++ chunk a) restSplit

end Semantics

end PerfectCompleteness.ExactTargetOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourceClauseCountMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceClauseCountMachine


open Turing UniqueGamesTheorem.Foundations Complexity
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool
def clean {A : Type} (ambient : A) : State A := (ambient, none)

inductive Label
  | tableOut | tableBack
  | skip (slot : Fin 1)
  | readCount | drain
  deriving DecidableEq, Fintype

def main : Label := .tableOut

variable {K Λ A : Type} [DecidableEq K]

def workTapes (tape : Fin 4 → K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 1) input) (tape 3) output

theorem workTapes_input (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input output : List Bool) :
    workTapes tape base input output (tape 1) = input := by
  have different : tape 1 ≠ tape 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (distinct h)
  simp [workTapes, different]

@[simp] theorem workTapes_output (tape : Fin 4 → K) (base : K → List Bool)
    (input output : List Bool) : workTapes tape base input output (tape 3) = output := by
  simp [workTapes]

theorem update_input (tape : Fin 4 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (workTapes tape base input output) (tape 1) replacement =
      workTapes tape base replacement output := by
  have different : tape 1 ≠ tape 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [workTapes, different]
  · simp [workTapes, h, Function.update_apply]

theorem workTapes_empty (tape : Fin 4 → K) (base : K → List Bool) (output : List Bool)
    (copyEmpty : base (tape 1) = []) :
    workTapes tape base [] output = Function.update base (tape 3) output := by
  have copySelf := Function.update_eq_self (tape 1) base
  rw [copyEmpty] at copySelf
  simp only [workTapes, copySelf]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.SourceClauseCountMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_StoppedCleanOwnInputGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanOwnInputGeometry

noncomputable section

abbrev F2 := ZMod 2

end
end PerfectCompleteness.StoppedCleanOwnInputGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TargetHeaderMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TargetHeaderMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

inductive Label
  | copyLast | restoreLast | pushAlphabet
  | copyRight | restoreRight | copyLeft | restoreLeft
  deriving DecidableEq

/-- A list enumerating every element of the type, which are all zero-argument constructors. (Generated by the `Fintype` deriving handler.)-/
protected abbrev Label.enumList : List Label := [.copyLast, .restoreLast, .pushAlphabet,
  .copyRight, .restoreRight, .copyLeft, .restoreLeft]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def main : Label := .copyLast

variable {K Λ A : Type} [DecidableEq K]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.TargetHeaderMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TargetFinalizeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TargetFinalizeMachine


open Turing UniqueGamesTheorem.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K] {stackCount : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def headerTape (tape : Fin 4 → K) : Fin 3 → K
  | 0 => tape 1
  | 1 => tape 2
  | 2 => tape 3

inductive Label (Cleanup : Type)
  | reverse
  | header (label : TargetHeaderMachine.Label)
  | cleanup (label : Cleanup)
  | finish
  deriving DecidableEq, Fintype

def bodyTapes (tape : Fin 4 → K) (base : K → List Bool) (body : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 0) []) (tape 3) body

end PerfectCompleteness.TargetFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TargetTapeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TargetTapeEnvelope

def outputBound (q E : Nat) : Nat :=
  2 * E + q + E + 4 + E * (2 * E + 2 * q * q + 2 * q + 2)

def coeff (w q D : Nat) : Nat :=
  SignedCostEnvelope.streamCoeff w D + 2 * D ^ 2 +
    (2 * q * q + 2 * q + 6) * D + q + 6

theorem le_scaled (a : Nat) {b : Nat} (hb : 1 ≤ b) : a ≤ a * b := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb

end PerfectCompleteness.TargetTapeEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_NormalizedTargetInitialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizedTargetInitialization


open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

abbrev State (A : Type) := A × Option Bool

def clean {A : Type} (ambient : A) : State A := (ambient, none)

variable {width : Nat}

inductive Label
  | seed
  | count (label : SourceClauseCountMachine.Label)
  | tuple (label : TupleInitializationMachine.Label)
  deriving DecidableEq, Fintype

end
end PerfectCompleteness.NormalizedTargetInitialization

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalCutBucketLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketLaw

open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

section Regrouping

def reorder (D U B F : Type*) :
    D × ((U × B) × F) ≃ B × (D × (U × F)) where
  toFun z := (z.2.1.2, (z.1, (z.2.1.1, z.2.2)))
  invFun z := (z.2.1, ((z.2.2.1, z.1), z.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Regrouping

end
end PerfectCompleteness.OriginalCutBucketLaw

end

end OAI
end


