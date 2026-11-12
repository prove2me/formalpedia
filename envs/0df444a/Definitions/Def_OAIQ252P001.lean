-- Prove2me | Definitions.Def_OAIQ252P001
-- name    : OAIQ252P001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:29:18.238698+00:00
-- url     : https://prove2.me/theorems/8b0b9c3d-961f-4eb6-8b80-2e022345d86e
-- title:
--   Definitions bundle OAIQ252P001 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1409 declarations of OpenAI's Lean: 759 definitions, 64 inductive types or structures, 28 instances and 558 theorems. The definitions and types are `OAI.PerfectCompleteness.BlockQuotient.JointOutput`, `OAI.PerfectCompleteness.BlockQuotient.OtherBlocks`, `OAI.PerfectCompleteness.BlockQuotient.splitOutput`, `OAI.PerfectCompleteness.BucketSampler.Direction`, `OAI.PerfectCompleteness.BucketSampler.F2`, `OAI.PerfectCompleteness.BucketSampler.Tape`, `OAI.PerfectCompleteness.BucketSampler.evaluate`, `OAI.PerfectCompleteness.BucketSampler.rankOne`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.Alphabet`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.Label`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.Label.enumList`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.payload`, `OAI.PerfectCompleteness.CanonicalDictionaryAppendMachine.steps`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.Alphabet`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.appendMap`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.appendTapes`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.searchMap`, `OAI.PerfectCompleteness.CanonicalDictionaryMachine.searchTapes`, `OAI.PerfectCompleteness.CanonicalDictionaryNames.streamBound`, `OAI.PerfectCompleteness.CanonicalEndpointMachine.Alphabet`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.Assignment`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.boolWord`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.instFintypeReducedValue`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.partEnum`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.partitionMask`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.partitionOfMask`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.partitionWidth`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.partitionWords`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.reducedValueEquiv`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.sideWord`, `OAI.PerfectCompleteness.CanonicalKeyEncoding.words`, `OAI.PerfectCompleteness.CanonicalKeyMachine.Alphabet`, `OAI.PerfectCompleteness.CanonicalKeyMachine.Command`, `OAI.PerfectCompleteness.CanonicalKeyMachine.Label`, `OAI.PerfectCompleteness.CanonicalKeyMachine.LocalLabel`, `OAI.PerfectCompleteness.CanonicalKeyMachine.commands`, `OAI.PerfectCompleteness.CanonicalKeyMachine.entry`, `OAI.PerfectCompleteness.CanonicalKeyMachine.main`, `OAI.PerfectCompleteness.CanonicalKeyMachine.sourceLength`, `OAI.PerfectCompleteness.CanonicalKeyShape.Shape` and 783 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_BilinearGramCompressionLemmas`, `PerfectCompleteness_Algebra_EvaluationMatrix`, `PerfectCompleteness_Algebra_MatrixInverseConstantsLemmas`, `PerfectCompleteness_Construction_AscendingBranchingLemmas`, `PerfectCompleteness_Construction_CanonicalLocalCompletion`, `PerfectCompleteness_Construction_CutChildGrouping`, `PerfectCompleteness_Construction_DescendantSpacesLemmas`, `PerfectCompleteness_Construction_FactoredFunctionsLemmas`, `PerfectCompleteness_Construction_LocalCompletionFamily`, `PerfectCompleteness_Construction_SourceLocalOddLists`, `PerfectCompleteness_Construction_SourceQuestionReconstruction`, `PerfectCompleteness_Construction_TreeSourceSpaces`, `PerfectCompleteness_Decoding_CleanDecoderRateLemmas`, `PerfectCompleteness_Decoding_CleanDecoderSeedLawLemmas`, `PerfectCompleteness_Decoding_CleanLeftDecoderLemmas`, `PerfectCompleteness_Decoding_CleanPhysicalDecoderLaw`, `PerfectCompleteness_Decoding_CutGroupedProjectionLemmas`, `PerfectCompleteness_Decoding_DecoderContraction`, `PerfectCompleteness_Decoding_DecoderSourcePullback`, `PerfectCompleteness_Decoding_DecoderTableCoupling`, `PerfectCompleteness_Decoding_DependentDecoderSampling`, `PerfectCompleteness_Decoding_LeftDecoder`, `PerfectCompleteness_Decoding_LowerCutPairBackground`, `PerfectCompleteness_Decoding_LowerCutRowsLemmas`, `PerfectCompleteness_Decoding_LowerDirectionFiber`, `PerfectCompleteness_Decoding_Projection`, `PerfectCompleteness_Decoding_RightDecoderLemmas`, `PerfectCompleteness_Decoding_TwoResponseCollisionLemmas`, `PerfectCompleteness_Foundations_CanonicalDictionaryNames`, `PerfectCompleteness_Foundations_CanonicalEdgesLemmas`, `PerfectCompleteness_Foundations_CanonicalKeys`, `PerfectCompleteness_Foundations_CanonicalVertexNames`, `PerfectCompleteness_Foundations_ClauseSupportLemmas`, `PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas`, `PerfectCompleteness_Foundations_DesignatedLeavesLemmas`, `PerfectCompleteness_Foundations_DummyEliminationLemmas`, `PerfectCompleteness_Foundations_ExactConditionalOutput`, `PerfectCompleteness_Foundations_GlobalityLemmas`, `PerfectCompleteness_Foundations_HierarchicalArrays`, `PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas`, `PerfectCompleteness_Foundations_KeyFiniteness`, `PerfectCompleteness_Foundations_LinearEvaluationLemmas`, `PerfectCompleteness_Foundations_ManyGoodRowsLemmas`, `PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas`, `PerfectCompleteness_Foundations_OddListExtraction`, `PerfectCompleteness_Foundations_OddLists`, `PerfectCompleteness_Foundations_PartialTableInverse`, `PerfectCompleteness_Foundations_PartitionsLemmas`, `PerfectCompleteness_Foundations_QuarterBalanceLemmas`, `PerfectCompleteness_Foundations_QuotientTableAgreementLemmas`, `PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas`, `PerfectCompleteness_Foundations_ReducedDomains`, `PerfectCompleteness_Foundations_SourceClause`, `PerfectCompleteness_Foundations_SourceOddListsLemmas`, `PerfectCompleteness_Foundations_SourceProjectedTag`, `PerfectCompleteness_Foundations_SourceStrategy`, `PerfectCompleteness_Foundations_SourceTupleData`, `PerfectCompleteness_Foundations_WholeCutExteriorTransportLemmas`, `PerfectCompleteness_Foundations_WholeCutGrouping`, `PerfectCompleteness_Foundations_WholeCutReplayLemmas`, `PerfectCompleteness_Foundations_WholeReplaySubtreeLemmas`, `PerfectCompleteness_Machines_CanonicalDictionaryAppendMachine`, `PerfectCompleteness_Machines_CanonicalDictionaryMachine`, `PerfectCompleteness_Machines_CanonicalEndpointMachine`, `PerfectCompleteness_Machines_CanonicalKeyMachine`, `PerfectCompleteness_Machines_CanonicalKeyShapeMachineLemmas`, `PerfectCompleteness_Machines_CanonicalLabelEncoding`, `PerfectCompleteness_Machines_CircuitLemmas`, `PerfectCompleteness_Machines_CompletedEdgeMachine`, `PerfectCompleteness_Machines_DescriptorProjectionMachine`, `PerfectCompleteness_Machines_DomainEncoding`, `PerfectCompleteness_Machines_EncodingLemmas`, `PerfectCompleteness_Machines_FiniteBlockMachineLemmas`, `PerfectCompleteness_Machines_ForestStage`, `PerfectCompleteness_Machines_InitializationMachine`, `PerfectCompleteness_Machines_InitializationStageLemmas`, `PerfectCompleteness_Machines_KeyMetadataMachine`, `PerfectCompleteness_Machines_LocalCompletionMachineLemmas`, `PerfectCompleteness_Machines_NormalizationReadMachine`, `PerfectCompleteness_Machines_OriginalWholeCutTape`, `PerfectCompleteness_Machines_OwnInputAffineSliceLemmas`, `PerfectCompleteness_Machines_OwnInputReferenceLemmas`, `PerfectCompleteness_Machines_PositionLemmas`, `PerfectCompleteness_Machines_PostfixMachine`, `PerfectCompleteness_Machines_ProducerInvariant`, `PerfectCompleteness_Machines_SourceClauseReaderMachineLemmas`, `PerfectCompleteness_Machines_TermMachine`, `PerfectCompleteness_Machines_TupleEnumerationMachine`, `PerfectCompleteness_Machines_WholeArrayInteriorOwnInputLaw`, `PerfectCompleteness_Reduction_CanonicalGameLemmas`, `PerfectCompleteness_Reduction_CompletedVisitOrder`, `PerfectCompleteness_Reduction_CompletionAlphabetLemmas`, `PerfectCompleteness_Reduction_CompletionLemmas`, `PerfectCompleteness_Reduction_CompletionOutputLemmas`, `PerfectCompleteness_Reduction_CompletionSoundness`, `PerfectCompleteness_Reduction_SourceGame`, `PerfectCompleteness_Reduction_Target`, `PerfectCompleteness_Reduction_TargetGameLemmas`, `PerfectCompleteness_Reduction_Value`, `PerfectCompleteness_Repetition_CleanConditioning`, `PerfectCompleteness_Repetition_CleanCountingLemmas`, `PerfectCompleteness_Repetition_CleanPhysicalProjectedMeeting`, `PerfectCompleteness_Repetition_CutChildCleanLawLemmas`, `PerfectCompleteness_Sampling_BucketSampler`, `PerfectCompleteness_Sampling_BucketUniformLemmas`, `PerfectCompleteness_Sampling_CompletionProbability`, `PerfectCompleteness_Sampling_CutSamplerReplayGroupingTransport`, `PerfectCompleteness_Sampling_RecordSeedSamplingLemmas`, `PerfectCompleteness_Sampling_UniformLatent`, `PerfectCompleteness_Sampling_UniformLatentSupportLemmas`, `PerfectCompleteness_Sampling_WholeCutSampler`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Games_FactorizationLemmas`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_FinalCNFMachineLemmas`, `UniqueGames_Machines_FinalCNFPattern`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineExpanderRowCleanup`, `UniqueGames_Machines_MachineExpanderRowDivision`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineFiniteAlphabet`, `UniqueGames_Machines_MachineFixedDivMod`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineLookupCore`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachineProductFieldLemmas`, `UniqueGames_Machines_MachineProductGatherBoundsLemmas`, `UniqueGames_Machines_MachineSubroutineLemmas`, `UniqueGames_Machines_MachineTransducerCopy`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUnaryAddAt`, `UniqueGames_Machines_PoweringMachineRow`, `UniqueGames_PCP_AlphabetGraphLemmas`, `UniqueGames_PCP_AlphabetReductionLemmas`, `UniqueGames_PCP_AlphabetRetractionLemmas`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_AmplificationIteration`, `UniqueGames_PCP_AssignmentTester`, `UniqueGames_PCP_CayleySampling`, `UniqueGames_PCP_CayleyTailCount`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_CloudRoundingLemmas`, `UniqueGames_PCP_CodeComposition`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_ExpanderRowControlLemmas`, `UniqueGames_PCP_ExpanderTables`, `UniqueGames_PCP_ExpandersLemmas`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_FinalConstantsLemmas`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_GenericGraphTables`, `UniqueGames_PCP_GraphTables`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_InputLemmas`, `UniqueGames_PCP_OverlayLemmas`, `UniqueGames_PCP_PoweringLabelsLemmas`, `UniqueGames_PCP_PoweringOpinionTables`, `UniqueGames_PCP_PoweringOpinionsLemmas`, `UniqueGames_PCP_PoweringPortReindexLemmas`, `UniqueGames_PCP_PoweringTableSemanticsLemmas`, `UniqueGames_PCP_PoweringTablesLemmas`, `UniqueGames_PCP_Preprocessing`, `UniqueGames_PCP_PreprocessingOverlayTables`, `UniqueGames_PCP_PreprocessingPaddingTables`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularTablesLemmas`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_QueriesLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceHeaderAccumulate`, `UniqueGames_PCP_SourceHeaderCounts`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceMachine`, `UniqueGames_PCP_SourceNoiseParameterLemmas`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_VertexPadding`, `UniqueGames_PCP_ZigzagGraphsLemmas`, `UniqueGames_Reduction_ActualCanonicalLemmas`, `UniqueGames_Reduction_BinaryCoordinates`, `UniqueGames_Reduction_ExplicitLemmas`, `UniqueGames_Reduction_FinalParametersLemmas`, `UniqueGames_Soundness_PartnerLinearLemmas`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P003`, `OAIQ252P004`, `OAIQ252P005` and `OAIQ252P006`.
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_BinaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Dimension-independent transport between the compact bit-vector coordinates of
the finite motif and the coordinate functions used by the later constructions.
The vector-space addition involved here is XOR, not modular integer addition.
-/
namespace UniqueGamesTheorem.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

end UniqueGamesTheorem.Integration.BinaryCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixRowQuotient

noncomputable section

variable {𝕜 H K : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]

theorem exists_section (W : Submodule 𝕜 H) :
    ∃ s : (H ⧸ W) →ₗ[𝕜] H, W.mkQ.comp s = LinearMap.id :=
  W.mkQ.exists_rightInverse_of_surjective W.range_mkQ

end
end PerfectCompleteness.MatrixRowQuotient

end

section

namespace PerfectCompleteness.TensorCosetEvaluation

noncomputable section

open scoped TensorProduct

section GeneralField

variable {𝕜 U H : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup H] [Module 𝕜 H]

def pureFrequency (a : Module.Dual 𝕜 U) (q : Module.Dual 𝕜 H) :
    Module.Dual 𝕜 (U ⊗[𝕜] H) :=
  TensorProduct.lift (a.smulRight q)

end GeneralField

end
end PerfectCompleteness.TensorCosetEvaluation

end

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

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] Classical.propDecidable

def node : ℕ → ℝ
  | 0 => 1
  | n + 1 => node n / 2

theorem node_pos (n : ℕ) : 0 < node n := by
  induction n with
  | zero => norm_num [node]
  | succ n ih => exact div_pos ih (by norm_num)

theorem node_eq_inv_pow (n : ℕ) : node n = ((2 : ℝ) ^ n)⁻¹ := by
  induction n with
  | zero => simp [node]
  | succ n ih => rw [node, ih, pow_succ, mul_inv_rev]; ring

theorem node_add_le (i k : ℕ) : node (i + k) ≤ node i := by
  induction k with
  | zero => simp
  | succ k ih =>
    change node (i + k) / 2 ≤ node i
    linarith [node_pos (i + k)]

theorem node_antitone {i j : ℕ} (h : i ≤ j) : node j ≤ node i := by
  have he : i + (j - i) = j := by omega
  simpa only [he] using node_add_le i (j - i)

end UniqueGamesTheorem.Appendix.RankLevelFilter

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixLevelBridge

open scoped BigOperators Classical

def levelCutoffConstant (r : Nat) (ρ : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (r + 1),
    if d = 0 then ρ else (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4)

end UniqueGamesTheorem.Fourier.MatrixLevelBridge

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartitionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProductReduction

variable {I : Type*} {X R W : I → Type*} {Y : Type*}

def CoordinateInvariant (r : ∀ i, X i → R i) (f : (∀ i, X i) → Y) : Prop :=
  ∀ (i : I) (x x' : ∀ i, X i),
    (∀ j, j ≠ i → x j = x' j) →
    r i (x i) = r i (x' i) → f x = f x'

theorem coordinateInvariant_of_update [DecidableEq I]
    (r : ∀ i, X i → R i) (f : (∀ i, X i) → Y)
    (hf : ∀ (i : I) (x : ∀ i, X i) (u : X i),
      r i (x i) = r i u → f x = f (Function.update x i u)) :
    CoordinateInvariant r f := by
  intro i x x' hfixed hr
  have hupdate : Function.update x i (x' i) = x' :=
    Function.update_eq_iff.2 ⟨rfl, hfixed⟩
  exact (hf i x (x' i) hr).trans (congrArg f hupdate)

end PerfectCompleteness.ProductReduction

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
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

abbrev Strategy (Q₁ Q₂ A₁ A₂ : Type*) := (Q₁ → A₁) × (Q₂ → A₂)

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ReducedPartition

variable {X W R Y : Type*}

def ConstantOnFibers (r : X → R) (f : X → Y) : Prop :=
  ∀ x x', r x = r x' → f x = f x'

def fiber (r : X → R) (f : X → Y) (x : X) : Set R :=
  {v | ∃ z, r z = v ∧ f z = f x}

def parts (r : X → R) (f : X → Y) : Set (Set R) :=
  Set.range (fiber r f)

theorem self_mem_fiber (r : X → R) (f : X → Y) (x : X) :
    r x ∈ fiber r f x :=
  ⟨x, rfl, rfl⟩

theorem mem_fiber_iff (r : X → R) (f : X → Y)
    (hf : ConstantOnFibers r f) (z x : X) :
    r z ∈ fiber r f x ↔ f z = f x := by
  constructor
  · rintro ⟨w, hw, hfw⟩
    exact (hf w z hw).symm.trans hfw
  · intro h
    exact ⟨z, rfl, h⟩

theorem fiber_eq_of_output_eq (r : X → R) (f : X → Y) {x x' : X}
    (h : f x = f x') : fiber r f x = fiber r f x' := by
  ext v
  constructor
  · rintro ⟨z, hz, hfz⟩
    exact ⟨z, hz, hfz.trans h⟩
  · rintro ⟨z, hz, hfz⟩
    exact ⟨z, hz, hfz.trans h.symm⟩

abbrev Part (r : X → R) (f : X → Y) := ↥(parts r f)

def label (r : X → R) (f : X → Y) (x : X) : Part r f :=
  ⟨fiber r f x, ⟨x, rfl⟩⟩

instance instNonemptyPart [Nonempty X] (r : X → R) (f : X → Y) : Nonempty (Part r f) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨label r f x⟩

noncomputable def representative (r : X → R) (f : X → Y) (P : Part r f) : X :=
  P.property.choose

theorem representative_spec (r : X → R) (f : X → Y) (P : Part r f) :
    fiber r f (representative r f P) = P.val :=
  P.property.choose_spec

theorem representative_mem (r : X → R) (f : X → Y) (P : Part r f) :
    r (representative r f P) ∈ P.val := by
  rw [← representative_spec r f P]
  exact self_mem_fiber r f _

noncomputable def output (r : X → R) (f : X → Y) (P : Part r f) : Y :=
  f (representative r f P)

theorem mem_iff (r : X → R) (f : X → Y) (hf : ConstantOnFibers r f)
    (P : Part r f) (x : X) : r x ∈ P.val ↔ f x = output r f P := by
  rw [← representative_spec r f P]
  exact mem_fiber_iff r f hf x (representative r f P)

theorem fiber_eq_of_pullback
    (π : X → W) (hπ : Function.Surjective π)
    (rX : X → R) (rW : W → R) (fX : X → Y) (fW : W → Y)
    (hr : ∀ x, rX x = rW (π x)) (hf : ∀ x, fX x = fW (π x)) (x : X) :
    fiber rX fX x = fiber rW fW (π x) := by
  ext v
  constructor
  · rintro ⟨z, hz, hfz⟩
    exact ⟨π z, (hr z).symm.trans hz, (hf z).symm.trans (hfz.trans (hf x))⟩
  · rintro ⟨w, hw, hfw⟩
    obtain ⟨z, hz⟩ := hπ w
    refine ⟨z, (hr z).trans ((congrArg rW hz).trans hw), ?_⟩
    exact (hf z).trans ((congrArg fW hz).trans (hfw.trans (hf x).symm))

theorem parts_eq_of_pullback
    (π : X → W) (hπ : Function.Surjective π)
    (rX : X → R) (rW : W → R) (fX : X → Y) (fW : W → Y)
    (hr : ∀ x, rX x = rW (π x)) (hf : ∀ x, fX x = fW (π x)) :
    parts rX fX = parts rW fW := by
  apply Set.ext
  intro P
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨π x, (fiber_eq_of_pullback π hπ rX rW fX fW hr hf x).symm.trans hx⟩
  · rintro ⟨w, hw⟩
    obtain ⟨x, hx⟩ := hπ w
    refine ⟨x, ?_⟩
    calc
      fiber rX fX x = fiber rW fW (π x) :=
        fiber_eq_of_pullback π hπ rX rW fX fW hr hf x
      _ = fiber rW fW w := congrArg (fiber rW fW) hx
      _ = P := hw

end PerfectCompleteness.ReducedPartition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceClause
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceClause

abbrev Triple := Bool × Bool × Bool

def Triple.at (t : Triple) (i : Fin 3) : Bool :=
  match i.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

def literalTruth (positive value : Bool) : Bool :=
  if positive then value else !value

def localEval (signs values : Triple) : Bool :=
  (literalTruth signs.1 values.1 || literalTruth signs.2.1 values.2.1) ||
    literalTruth signs.2.2 values.2.2

def allTriples : List Triple :=
  [(false, false, false), (false, false, true),
   (false, true, false), (false, true, true),
   (true, false, false), (true, false, true),
   (true, true, false), (true, true, true)]

def satisfyingTriples (signs : Triple) : List Triple :=
  allTriples.filter (localEval signs)

theorem mem_allTriples (t : Triple) : t ∈ allTriples := by
  rcases t with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem mem_satisfyingTriples (signs values : Triple) :
    values ∈ satisfyingTriples signs ↔ localEval signs values = true := by
  simp [satisfyingTriples, mem_allTriples]

theorem satisfyingTriples_nodup (signs : Triple) :
    (satisfyingTriples signs).Nodup := by
  rcases signs with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem satisfyingTriples_length (signs : Triple) :
    (satisfyingTriples signs).length = 7 := by
  rcases signs with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem coordinate_truth_table :
    ∀ s₀ s₁ s₂ : Bool, ∀ i : Fin 3, ∀ value : Bool,
      ∃ a b c : Bool,
        localEval (s₀, s₁, s₂) (a, b, c) = true ∧
        Triple.at (a, b, c) i = value := by
  decide

theorem coordinate_surjective (signs : Triple) (i : Fin 3) (value : Bool) :
    ∃ t ∈ satisfyingTriples signs, t.at i = value := by
  obtain ⟨a, b, c, hs, hv⟩ :=
    coordinate_truth_table signs.1 signs.2.1 signs.2.2 i value
  exact ⟨(a, b, c), (mem_satisfyingTriples signs _).mpr hs, hv⟩

theorem pair_truth_table :
    ∀ s₀ s₁ s₂ : Bool, ∀ i j : Fin 3, i ≠ j → ∀ first second : Bool,
      ∃ a b c : Bool,
        localEval (s₀, s₁, s₂) (a, b, c) = true ∧
        Triple.at (a, b, c) i = first ∧ Triple.at (a, b, c) j = second := by
  decide

theorem pair_surjective (signs : Triple) (i j : Fin 3) (distinct : i ≠ j)
    (first second : Bool) :
    ∃ t ∈ satisfyingTriples signs, t.at i = first ∧ t.at j = second := by
  obtain ⟨a, b, c, hs, hv⟩ :=
    pair_truth_table signs.1 signs.2.1 signs.2.2 i j distinct first second
  exact ⟨(a, b, c), (mem_satisfyingTriples signs _).mpr hs, hv⟩

abbrev Occurrence (clauseCount : Nat) := Fin clauseCount × Fin 3

end PerfectCompleteness.SourceClause

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ClauseSupportLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ClauseSupport

open SourceClause

variable {C C' D E Y Z : Type*}

abbrev Answer (signs : Triple) := {u : Triple // u ∈ satisfyingTriples signs}

def coordinate {signs : Triple} (i : Fin 3) (u : Answer signs) : Bool :=
  u.val.at i

theorem coordinate_surjective (signs : Triple) (i : Fin 3) :
    Function.Surjective (coordinate (signs := signs) i) := by
  intro b
  obtain ⟨u, hu, hb⟩ := SourceClause.coordinate_surjective signs i b
  exact ⟨⟨u, hu⟩, hb⟩

theorem pair_surjective (signs : Triple) (i j : Fin 3) (hij : i ≠ j)
    (a b : Bool) : ∃ u : Answer signs, coordinate i u = a ∧ coordinate j u = b := by
  obtain ⟨u, hu, hi, hj⟩ := SourceClause.pair_surjective signs i j hij a b
  exact ⟨⟨u, hu⟩, hi, hj⟩

instance instNonemptyAnswer (signs : Triple) : Nonempty (Answer signs) := by
  obtain ⟨u, _⟩ := coordinate_surjective signs 0 false
  exact ⟨u⟩

def Unused (f : C → D → Y) : Prop := ∀ c u v, f c u = f c v

def Factors (f : C → D → Y) (p : D → E) : Prop :=
  ∀ c u v, p u = p v → f c u = f c v

abbrev Reducible {signs : Triple} (f : C → Answer signs → Y) (i : Fin 3) :=
  Factors f (coordinate i)

theorem unused_of_two_reductions {signs : Triple} (f : C → Answer signs → Y)
    {i j : Fin 3} (hij : i ≠ j) (hi : Reducible f i) (hj : Reducible f j) :
    Unused f := by
  intro c u v
  obtain ⟨w, hw₁, hw₂⟩ := pair_surjective signs i j hij (coordinate i u) (coordinate j v)
  exact (hi c u w hw₁.symm).trans (hj c w v hw₂)

theorem used_reduction_unique {signs : Triple} (f : C → Answer signs → Y)
    (hused : ¬ Unused f) {i j : Fin 3} (hi : Reducible f i) (hj : Reducible f j) :
    i = j := by
  by_contra hij
  exact hused (unused_of_two_reductions f hij hi hj)

def pull (f : C → D → Y) (context : C' → C) (localMap : E → D) : C' → E → Y :=
  fun c u => f (context c) (localMap u)

theorem unused_pull_iff (f : C → D → Y) (context : C' → C) (localMap : E → D)
    (hcontext : Function.Surjective context) (hlocal : Function.Surjective localMap) :
    Unused (pull f context localMap) ↔ Unused f := by
  constructor
  · intro h c u v
    obtain ⟨c', rfl⟩ := hcontext c
    obtain ⟨u', rfl⟩ := hlocal u
    obtain ⟨v', rfl⟩ := hlocal v
    exact h c' u' v'
  · intro h c u v
    exact h (context c) (localMap u) (localMap v)

theorem factors_pull_iff (f : C → D → Y) (context : C' → C) (localMap : E → D)
    (p : D → Z) (hcontext : Function.Surjective context)
    (hlocal : Function.Surjective localMap) :
    Factors (pull f context localMap) (p ∘ localMap) ↔ Factors f p := by
  constructor
  · intro h c u v huv
    obtain ⟨c', rfl⟩ := hcontext c
    obtain ⟨u', rfl⟩ := hlocal u
    obtain ⟨v', rfl⟩ := hlocal v
    exact h c' u' v' huv
  · intro h c u v huv
    exact h (context c) (localMap u) (localMap v) huv

theorem unused_kernel_invariant (f : C → D → Y) (g : C → D → Z)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    Unused f ↔ Unused g := by
  exact ⟨fun h c u v => (hkernel c u v).1 (h c u v),
    fun h c u v => (hkernel c u v).2 (h c u v)⟩

theorem factors_kernel_invariant (f : C → D → Y) (g : C → D → Z) (p : D → E)
    (hkernel : ∀ c u v, f c u = f c v ↔ g c u = g c v) :
    Factors f p ↔ Factors g p := by
  exact ⟨fun h c u v hp => (hkernel c u v).1 (h c u v hp),
    fun h c u v hp => (hkernel c u v).2 (h c u v hp)⟩

inductive Mode where
  | dropped
  | bit (position : Fin 3)
  | full
  deriving DecidableEq

noncomputable def clauseMode {signs : Triple} (f : C → Answer signs → Y) : Mode := by
  classical
  exact if Unused f then .dropped else
    if h : ∃ i, Reducible f i then .bit h.choose else .full

theorem clauseMode_unused {signs : Triple} (f : C → Answer signs → Y)
    (h : Unused f) : clauseMode f = .dropped := by
  simp [clauseMode, h]

theorem clauseMode_full {signs : Triple} (f : C → Answer signs → Y)
    (hused : ¬ Unused f) (hfull : ¬ ∃ i, Reducible f i) : clauseMode f = .full := by
  simp [clauseMode, hused, hfull]

inductive ReducedValue where
  | dropped
  | bit (value : Bool)
  | full (value : Triple)
  deriving DecidableEq

def reduceByMode {signs : Triple} (mode : Mode) (u : Answer signs) : ReducedValue :=
  match mode with
  | .dropped => .dropped
  | .bit i => .bit (coordinate i u)
  | .full => .full u.val

noncomputable def clauseReduction {signs : Triple} (f : C → Answer signs → Y) :
    Answer signs → ReducedValue := reduceByMode (clauseMode f)

noncomputable def bitReduction (f : C → Bool → Y) (b : Bool) : ReducedValue := by
  classical
  exact if Unused f then .dropped else .bit b

theorem bitReduction_sound (f : C → Bool → Y) (c : C) (u v : Bool)
    (h : bitReduction f u = bitReduction f v) : f c u = f c v := by
  classical
  by_cases hu : Unused f
  · exact hu c u v
  · have huv : u = v := by simpa [bitReduction, hu] using h
    exact congrArg (f c) huv

inductive SlotKey where
  | dropped
  | bit (variableID : Nat)
  | full (clauseOccurrence : Nat) (signs : Triple)
  deriving DecidableEq

noncomputable def clauseKey {signs : Triple} (occurrence : Nat) (variableIDs : Fin 3 → Nat)
    (f : C → Answer signs → Y) : SlotKey :=
  match clauseMode f with
  | .dropped => .dropped
  | .bit i => .bit (variableIDs i)
  | .full => .full occurrence signs

noncomputable def bitKey (variableID : Nat) (f : C → Bool → Y) : SlotKey := by
  classical
  exact if Unused f then .dropped else .bit variableID

theorem unprojected_bit_reduction_eq (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (b : Bool) :
    bitReduction (pull f context id) b = bitReduction f b := by
  classical
  simp only [bitReduction, unused_pull_iff f context id hcontext Function.surjective_id]

theorem projected_reducible {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (i : Fin 3) :
    Reducible (pull f context (coordinate (signs := signs) i)) i := by
  intro c u v h
  exact congrArg (f (context c)) h

theorem projected_unused_iff {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (i : Fin 3) :
    Unused (pull f context (coordinate (signs := signs) i)) ↔ Unused f :=
  unused_pull_iff f context (coordinate i) hcontext (coordinate_surjective signs i)

end PerfectCompleteness.ClauseSupport

end

section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {I C C' Y : Type*}

inductive Slot where
  | clause (occurrence : Nat) (variableIDs : Fin 3 → Nat) (signs : SourceClause.Triple)
  | bit (variableID : Nat)

def Slot.Domain : Slot → Type
  | .clause _ _ signs => Answer signs
  | .bit _ => Bool

instance instNonemptyDomain (s : Slot) : Nonempty s.Domain := by
  cases s <;> dsimp [Slot.Domain] <;> infer_instance

abbrev Assignment (slots : I → Slot) := ∀ i, (slots i).Domain

inductive Projection : Slot → Slot → Type
  | keep (s : Slot) : Projection s s
  | select (occurrence : Nat) (variableIDs : Fin 3 → Nat)
      (signs : SourceClause.Triple) (position : Fin 3) :
      Projection (.clause occurrence variableIDs signs) (.bit (variableIDs position))

def Projection.map {s t : Slot} : Projection s t → s.Domain → t.Domain
  | .keep _ => id
  | .select _ _ _ i => coordinate i

theorem Projection.surjective {s t : Slot} (p : Projection s t) :
    Function.Surjective p.map := by
  cases p with
  | keep s => exact Function.surjective_id
  | select occurrence variableIDs signs i => exact coordinate_surjective signs i

variable [DecidableEq I]

def sectionFunction (slots : I → Slot) (f : Assignment slots → Y) (i : I) :
    Assignment slots → (slots i).Domain → Y :=
  fun context u => f (Function.update context i u)

noncomputable def localKey (s : Slot) : (C → s.Domain → Y) → SlotKey :=
  match s with
  | .clause occurrence variableIDs _ => clauseKey occurrence variableIDs
  | .bit variableID => bitKey variableID

noncomputable def localReduction (s : Slot) : (C → s.Domain → Y) → s.Domain → ReducedValue :=
  match s with
  | .clause _ _ _ => clauseReduction
  | .bit _ => bitReduction

noncomputable def keyFields (slots : I → Slot) (f : Assignment slots → Y) : I → SlotKey :=
  fun i => localKey (slots i) (sectionFunction slots f i)

noncomputable def coordinateReduction (slots : I → Slot) (f : Assignment slots → Y)
    (i : I) : (slots i).Domain → ReducedValue :=
  localReduction (slots i) (sectionFunction slots f i)

noncomputable def retainedKeys {n : Nat} (slots : Fin n → Slot)
    (f : Assignment slots → Y) : List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, keyFields slots f i))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

end PerfectCompleteness.MixedSupport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ReducedDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ReducedDomains

open ClauseSupport

variable {I C Y : Type*}

def valueCode : ReducedValue → Option (Bool ⊕ SourceClause.Triple)
  | .dropped => none
  | .bit b => some (.inl b)
  | .full triple => some (.inr triple)

theorem valueCode_injective : Function.Injective valueCode := by
  intro u v h
  cases u <;> cases v <;> simp_all [valueCode]

theorem reducedValue_finite : Finite ReducedValue :=
  Finite.of_injective valueCode valueCode_injective

end PerfectCompleteness.ReducedDomains

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport

variable {n : Nat} {Y : Type*}

inductive Side where
  | left
  | right
  deriving DecidableEq

structure Key (n : Nat) where
  side : Side
  retained : List (Fin n × SlotKey)
  partition : Set (Set (Fin n → ReducedValue))

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalEdgesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeyShape

open ClauseSupport MixedSupport
open scoped Classical

noncomputable section

inductive Shape where
  | clause (signs : SourceClause.Triple)
  | bit
  deriving DecidableEq, Fintype

inductive SupportMode where
  | dropped
  | clauseBit (position : Fin 3)
  | full
  | bit
  deriving DecidableEq, Fintype

end
end PerfectCompleteness.CanonicalKeyShape

end

section

namespace PerfectCompleteness.SourceKeys

open SourceClause MixedSupport CanonicalKeys

variable {v m n : Nat} {I Y Z : Type*}

inductive Endpoint (v m : Nat) where
  | clause (occurrence : Fin m)
  | variable (variableID : Fin v)
  deriving DecidableEq

end PerfectCompleteness.SourceKeys

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

/-! The actual single-coordinate dependency-breaking reveal distribution.
The tag records which endpoint of the question pair was revealed. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

end
end UniqueGamesTheorem.Foundations.Repetition

end

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

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

open Turing

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

instance labelFintype [∀ command, Fintype (LocalLabel command)]
    (commands : List Command) : Fintype (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (Fintype (LocalLabel command ⊕ Label LocalLabel commands))

instance labelDecidableEq [∀ command, DecidableEq (LocalLabel command)]
    (commands : List Command) : DecidableEq (Label LocalLabel commands) := by
  induction commands with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons command commands ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (LocalLabel command ⊕ Label LocalLabel commands))

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

def entry : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | command :: _, labels, _ => some (labels (.inl (main command)))

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

def instruction : (commands : List Command) → (Label LocalLabel commands → Λ) → Option Λ →
    Label LocalLabel commands → TM2.Stmt Γ Λ σ
  | [], _, _, label => nomatch label
  | command :: commands, labels, exit, .inl label =>
      localInstruction command (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit) label
  | _ :: commands, labels, exit, .inr label =>
      instruction commands (fun l => labels (.inr l)) exit label

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

def resultOf : List Command → Data → Data
  | [], data => data
  | command :: commands, data => resultOf commands (result command data)

def steps : List Command → Data → Nat
  | [], _ => 0
  | command :: commands, data => cost command data + steps commands (result command data)

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

end

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

abbrev Buffer (N : Nat) := Fin N → Bool

section Chains

variable {K Λ σ : Type} {N : Nat}

/-- Proof-level description of the finite register updates. -/
def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

end Chains

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineSubroutineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Concrete forward-table serialization of unique games. The parser reconstructs
an inverse by finite search and checks both inverse laws. Constraint occurrences,
including repeated parallel edges, are preserved in their original list order. -/

namespace UniqueGamesTheorem.Foundations.Complexity

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

end UniqueGamesTheorem.Foundations.Complexity

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
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- A single finite statement: inspect the counter, decrement a positive
counter, and jump to the body or exit. The zero delimiter is never consumed. -/
def guard (counter : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek counter (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop counter (fun state _ => (state.1, none)) (.goto fun _ => bodyLabel))
      (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_ActualCanonicalLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.CloneGap

variable {α : Type*} {β : Type*} {Name : Type}

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

end UniqueGamesTheorem.Reduction.CloneGap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Soundness_PartnerLinearLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Soundness.RepetitionUpper

/-- An elementary Archimedean bound for rational parameters. -/
theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

/-- The estimate `b^n ≤ 1 / (1+n(1-b))` without division. -/
theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

/-- Positive powers of a rational base below one eventually fall below every
positive rational threshold; this supplies the search target in (4.4). -/
theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

end UniqueGamesTheorem.Soundness.RepetitionUpper

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

/-! Existence of the finite numerical choices in Section 4.1. All errors and
search tests here are rational, including the fourth-power test in (4.1). -/

namespace UniqueGamesTheorem.Integration.FinalParameters

open UniqueGamesTheorem.Soundness.RepetitionUpper

def rho (r s : Nat) : ℚ := (1 / 2 : ℚ) ^ (s - (r + 1))
def levelConstant (r : Nat) : ℚ := (r + 1 : ℚ) * 2 ^ (30 * r ^ 2)

theorem levelConstant_pos (r : Nat) : 0 < levelConstant r := by
  unfold levelConstant
  positivity

theorem rho_pos (r s : Nat) : 0 < rho r s := by
  unfold rho
  positivity

/-- Selecting the exponent as a multiple of four supplies an exact rational
fourth root. No approximation of a real root enters the parameter search. -/
theorem exists_symbol_dimension (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧ ∃ u : ℚ,
      0 < u ∧ u ^ 4 = rho r s ∧ levelConstant r * u ≤ δ / 8 := by
  have hA := levelConstant_pos r
  have ht : 0 < δ / (8 * levelConstant r) := by positivity
  obtain ⟨n, hn, hsmall⟩ := exists_power_lt (1 / 2 : ℚ)
    (δ / (8 * levelConstant r)) (by norm_num) (by norm_num) ht
  refine ⟨r + 1 + 4 * n, by omega, (1 / 2 : ℚ) ^ n, by positivity, ?_, ?_⟩
  · unfold rho
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    congr 1
    omega
  · have hbound : (1 / 2 : ℚ) ^ n * (8 * levelConstant r) < δ :=
      (lt_div_iff₀ (by positivity)).mp hsmall
    linarith

end UniqueGamesTheorem.Integration.FinalParameters

end

section

/-! Exact passage from the rational construction parameters and experiments to
the real inequalities used by the Fourier and soundness proofs. -/

namespace UniqueGamesTheorem.Integration.RealBounds

open FinalParameters

theorem fourth_root_as_rpow {u ρ : ℚ} (hu : 0 < u) (hfour : u ^ 4 = ρ) :
    (ρ : ℝ) ^ (1 / 4 : ℝ) = (u : ℝ) := by
  have hpow : (u : ℝ) ^ 4 = (ρ : ℝ) := by exact_mod_cast hfour
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast (le_of_lt hu)
  rw [← hpow, one_div]
  exact Real.pow_rpow_inv_natCast hu' (by decide : (4 : Nat) ≠ 0)

theorem exists_symbol_dimension_real (r : Nat) {δ : ℚ} (hδ : 0 < δ) :
    ∃ s : Nat, r + 1 < s ∧
      (levelConstant r : ℝ) * (rho r s : ℝ) ^ (1 / 4 : ℝ) ≤ (δ : ℝ) / 8 := by
  obtain ⟨s, hs, u, hu, hfour, hbound⟩ := exists_symbol_dimension r hδ
  refine ⟨s, hs, ?_⟩
  rw [fourth_root_as_rpow hu hfour]
  exact_mod_cast hbound

end UniqueGamesTheorem.Integration.RealBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_LinearEvaluationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.LinearEvaluation

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

def fiberEquivKernel (f : V →ₗ[ZMod 2] P) (a : P) (v : V) (hv : f v = a) :
    {x : V // f x = a} ≃ f.ker where
  toFun x := ⟨x.val - v, by simp [x.property, hv]⟩
  invFun k := ⟨k.val + v, by simp [hv]⟩
  left_inv x := by ext; simp
  right_inv k := by ext; simp

theorem fiber_card_eq_kernel_of_surjective (f : V →ₗ[ZMod 2] P)
    (hf : Function.Surjective f) (a : P) :
    Nat.card {x : V // f x = a} = Nat.card f.ker := by
  obtain ⟨v, hv⟩ := hf a
  exact Nat.card_congr (fiberEquivKernel f a v hv)

variable [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) P]

def evaluation (x : V) : (V →ₗ[ZMod 2] P) →ₗ[ZMod 2] P := LinearMap.applyₗ x

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) P] in
@[simp] theorem evaluation_apply (x : V) (f : V →ₗ[ZMod 2] P) :
    evaluation x f = f x := rfl

end UniqueGamesTheorem.Gadget.LinearEvaluation

end

section

namespace PerfectCompleteness.BlockQuotient

variable {I B : Type*} {V : I → Type*} [DecidableEq I]

abbrev JointOutput (V : I → Type*) (B : Type*) := (∀ i, V i) × B

abbrev OtherBlocks (V : I → Type*) (selected : I) := ∀ i : {i // i ≠ selected}, V i.val

def splitOutput (V : I → Type*) (B : Type*) (selected : I) :
    JointOutput V B ≃ V selected × (OtherBlocks V selected × B) :=
  ((Equiv.piSplitAt selected V).prodCongr (Equiv.refl B)).trans (Equiv.prodAssoc _ _ _)

@[simp] theorem splitOutput_selected (selected : I) (x : JointOutput V B) :
    (splitOutput V B selected x).1 = x.1 selected := rfl

@[simp] theorem splitOutput_other (selected : I) (x : JointOutput V B)
    (i : {i // i ≠ selected}) :
    (splitOutput V B selected x).2.1 i = x.1 i.val := rfl

@[simp] theorem splitOutput_side (selected : I) (x : JointOutput V B) :
    (splitOutput V B selected x).2.2 = x.2 := rfl

open MixedSupport CanonicalKeys

end PerfectCompleteness.BlockQuotient

end

section

namespace UniqueGamesTheorem.Integration.CutoffBudget

open scoped BigOperators

noncomputable def cutoffSum (r : Nat) (ρ : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (r + 1),
    if d = 0 then ρ else (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4)

end UniqueGamesTheorem.Integration.CutoffBudget

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixInverseConstantsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerRankParameters

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

theorem power_ratio_le {a b k : Nat} (h : a + k ≤ b) :
    (2 : ℝ) ^ a / (2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ k := by
  rw [div_pow, one_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul, ← pow_add] using
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h)

theorem exists_cross_parameters (r : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m s : Nat, 0 < m ∧ 1 ≤ s ∧ ∀ s' : Nat, s ≤ s' →
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s' - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) < ρ := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (show 0 < ρ / 2 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  let m := k + 3
  let s := 2 * r + m + k + 1
  refine ⟨m, s, by dsimp [m]; omega, by dsimp [s]; omega, ?_⟩
  intro s' hs'
  have hfirst : m + k ≤ s' - 2 * r := by dsimp [s] at hs'; omega
  have hsecond : 2 * m + k ≤ m * m := by dsimp [m] <;> nlinarith
  have h₁ := power_ratio_le hfirst
  have h₂ := power_ratio_le hsecond
  linarith

end PerfectCompleteness.LowerRankParameters

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DummyEliminationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExactRationalMultiplicity

open scoped BigOperators

noncomputable section

variable {S : Type*} {E : S → Type*} [Fintype S] [∀ s, Fintype (E s)]

def commonDenominator (w : ∀ s, E s → ℚ) : Nat :=
  ∏ x : Sigma E, (w x.1 x.2).den

def multiplicity (w : ∀ s, E s → ℚ) (s : S) (e : E s) : Nat :=
  (w s e).num.natAbs * (commonDenominator w / (w s e).den)

theorem commonDenominator_pos (w : ∀ s, E s → ℚ) : 0 < commonDenominator w := by
  apply Finset.prod_pos
  intro x _
  exact (w x.1 x.2).den_pos

theorem denominator_dvd (w : ∀ s, E s → ℚ) (s : S) (e : E s) :
    (w s e).den ∣ commonDenominator w :=
  Finset.dvd_prod_of_mem (fun x : Sigma E => (w x.1 x.2).den)
    (Finset.mem_univ (⟨s, e⟩ : Sigma E))

@[simp] theorem commonDenominator_of_isEmpty [IsEmpty S] (w : ∀ s, E s → ℚ) :
    commonDenominator w = 1 := by
  classical
  simp [commonDenominator]

theorem multiplicity_cast (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (s : S) (e : E s) :
    (multiplicity w s e : ℚ) = (commonDenominator w : ℚ) * w s e := by
  have habs : ((w s e).num.natAbs : ℚ) = ((w s e).num : ℚ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℚ))
        (Int.natAbs_of_nonneg (Rat.num_pos.mpr (positive s e)).le)
  rw [multiplicity, Nat.cast_mul, Nat.cast_div_charZero (denominator_dvd w s e), habs]
  calc
    ((w s e).num : ℚ) * ((commonDenominator w : ℚ) / (w s e).den) =
        (commonDenominator w : ℚ) * (((w s e).num : ℚ) / (w s e).den) := by ring
    _ = (commonDenominator w : ℚ) * w s e := by rw [Rat.num_div_den]

theorem multiplicity_pos (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (s : S) (e : E s) : 0 < multiplicity w s e := by
  have h : (0 : ℚ) < (multiplicity w s e : ℚ) := by
    rw [multiplicity_cast w positive]
    exact mul_pos (Nat.cast_pos.mpr (commonDenominator_pos w)) (positive s e)
  exact_mod_cast h

theorem multiplicity_sum (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) (s : S) :
    ∑ e, multiplicity w s e = commonDenominator w := by
  have h : ((∑ e, multiplicity w s e : Nat) : ℚ) = (commonDenominator w : ℚ) := by
    rw [Nat.cast_sum]
    simp_rw [multiplicity_cast w positive]
    rw [← Finset.mul_sum, normalized s, mul_one]
  exact_mod_cast h

theorem multiplicity_div (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (s : S) (e : E s) :
    (multiplicity w s e : ℚ) / (commonDenominator w : ℚ) = w s e := by
  have hD : (commonDenominator w : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (commonDenominator_pos w))
  apply (div_eq_iff hD).mpr
  rw [multiplicity_cast w positive, mul_comm]

structure Uniformization (w : ∀ s, E s → ℚ) where
  denominator : Nat
  denominator_pos : 0 < denominator
  count : ∀ s, E s → Nat
  count_pos : ∀ s e, 0 < count s e
  count_total : ∀ s, ∑ e, count s e = denominator
  fraction : ∀ s e, (count s e : ℚ) / (denominator : ℚ) = w s e

def build (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) : Uniformization w where
  denominator := commonDenominator w
  denominator_pos := commonDenominator_pos w
  count := multiplicity w
  count_pos := multiplicity_pos w positive
  count_total := multiplicity_sum w positive normalized
  fraction := multiplicity_div w positive

@[simp] theorem build_denominator (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) :
    (build w positive normalized).denominator = commonDenominator w := rfl

@[simp] theorem build_count (w : ∀ s, E s → ℚ) (positive : ∀ s e, 0 < w s e)
    (normalized : ∀ s, ∑ e, w s e = 1) (s : S) (e : E s) :
    (build w positive normalized).count s e = multiplicity w s e := rfl

end

end PerfectCompleteness.ExactRationalMultiplicity

end

section

namespace PerfectCompleteness.ExactSeedMultiplicity

open scoped BigOperators

def factor (M : Nat) : Nat := M.factorial

def denominator (D M : Nat) : Nat := D * factor M

def perSeed (M count copies : Nat) : Nat := copies * (factor M / count)

theorem factor_positive (M : Nat) : 0 < factor M := Nat.factorial_pos M

theorem denominator_positive {D : Nat} (hD : 0 < D) (M : Nat) :
    0 < denominator D M := Nat.mul_pos hD (factor_positive M)

theorem count_dvd_factor {M count : Nat} (positive : 0 < count) (bounded : count ≤ M) :
    count ∣ factor M := Nat.dvd_factorial positive bounded

theorem seed_total {M count : Nat} (positive : 0 < count) (bounded : count ≤ M)
    (copies : Nat) : count * perSeed M count copies = copies * factor M := by
  unfold perSeed
  calc
    count * (copies * (factor M / count)) = copies * (count * (factor M / count)) := by ring
    _ = copies * factor M := by rw [Nat.mul_div_cancel' (count_dvd_factor positive bounded)]

theorem perSeed_positive {M count copies : Nat}
    (positive : 0 < count) (bounded : count ≤ M) (hcopies : 0 < copies) :
    0 < perSeed M count copies :=
  Nat.mul_pos hcopies (Nat.div_pos
    (Nat.le_of_dvd (factor_positive M) (count_dvd_factor positive bounded)) positive)

theorem perSeed_cast {M count : Nat} (positive : 0 < count) (bounded : count ≤ M)
    (copies : Nat) :
    (perSeed M count copies : ℚ) = (copies : ℚ) * factor M / count := by
  have hn : (count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  apply (eq_div_iff hn).mpr
  have h := seed_total positive bounded copies
  have hc : (count : ℚ) * (perSeed M count copies : ℚ) =
      (copies : ℚ) * (factor M : ℚ) := by exact_mod_cast h
  simpa only [mul_comm] using hc

theorem perSeed_ratio {D M count : Nat} (hD : 0 < D)
    (positive : 0 < count) (bounded : count ≤ M) (copies : Nat) :
    (perSeed M count copies : ℚ) / denominator D M = ((copies : ℚ) / D) / count := by
  rw [perSeed_cast positive bounded copies]
  have hDc : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hnc : (count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)
  have hfactor : (factor M : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (factor_positive M))
  simp only [denominator, Nat.cast_mul]
  field_simp [hDc, hnc, hfactor]

abbrev Seeded {E : Type*} (count : E → Nat) := Σ e : E, Fin (count e)

section Family

variable {E : Type*} [Fintype E] {D M : Nat}
    (copies count : E → Nat) (positive : ∀ e, 0 < count e) (bounded : ∀ e, count e ≤ M)

def multiplicity (outcome : Seeded count) : Nat :=
  perSeed M (count outcome.1) (copies outcome.1)

include positive bounded

theorem sum_multiplicity (total : ∑ e, copies e = D) :
    (∑ outcome : Seeded count, multiplicity (M := M) copies count outcome) = denominator D M := by
  rw [Fintype.sum_sigma]
  simp only [multiplicity, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = ∑ e, copies e * factor M := by
      apply Finset.sum_congr rfl
      intro e _
      exact seed_total (positive e) (bounded e) (copies e)
    _ = denominator D M := by
      rw [← Finset.sum_mul, total]
      rfl

end Family
end PerfectCompleteness.ExactSeedMultiplicity

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
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

variable {Ω Y : Type*} [Fintype Y]

def indicator (f : Ω → Option Y) (y : Y) (X : Ω) : ℝ :=
  if f X = some y then 1 else 0

end
end PerfectCompleteness.PartialTableInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_EvaluationMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.EvaluationMatrix

noncomputable section

variable {𝕜 Ω K : Type*} [Field 𝕜] [AddCommGroup K] [Module 𝕜 K]

def evaluation (H : Submodule 𝕜 (Ω → 𝕜)) (x : Ω) : Module.Dual 𝕜 H where
  toFun h := h.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluation_apply (H : Submodule 𝕜 (Ω → 𝕜)) (x : Ω) (h : H) :
    evaluation H x h = h.val x := rfl

def evaluate (H : Submodule 𝕜 (Ω → 𝕜)) (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (x : Ω) : K :=
  X (evaluation H x)

def shift (H : Submodule 𝕜 (Ω → 𝕜)) (X : Module.Dual 𝕜 H →ₗ[𝕜] K)
    (a : K) (h : H) : Module.Dual 𝕜 H →ₗ[𝕜] K :=
  X + (Module.Dual.eval 𝕜 H h).smulRight a

@[simp] theorem evaluate_shift (H : Submodule 𝕜 (Ω → 𝕜))
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (a : K) (h : H) (x : Ω) :
    evaluate H (shift H X a h) x = evaluate H X x + h.val x • a := rfl

def joint {Z : Type*} (H : Submodule 𝕜 (Ω → 𝕜)) (other : Ω → Z)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (x : Ω) : K × Z :=
  (evaluate H X x, other x)

@[simp] theorem joint_shift {Z : Type*} (H : Submodule 𝕜 (Ω → 𝕜))
    (other : Ω → Z) (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (a : K) (h : H) (x : Ω) :
    joint H other (shift H X a h) x = (evaluate H X x + h.val x • a, other x) := rfl

section Rows

variable (H : Submodule 𝕜 (Ω → 𝕜)) [FiniteDimensional 𝕜 H] {ℓ : Nat}

def rows (X : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) : Fin ℓ → H :=
  fun i => (Module.evalEquiv 𝕜 H).symm ((LinearMap.proj i).comp X)

def ofRows (v : Fin ℓ → H) : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜) :=
  LinearMap.pi (fun i => Module.Dual.eval 𝕜 H (v i))

omit [FiniteDimensional 𝕜 H] in
@[simp] theorem ofRows_apply (v : Fin ℓ → H) (q : Module.Dual 𝕜 H) (i : Fin ℓ) :
    ofRows H v q i = q (v i) := rfl

@[simp] theorem ofRows_rows (X : Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) :
    ofRows H (rows H X) = X := by
  ext q i
  exact Module.apply_evalEquiv_symm_apply 𝕜 H q ((LinearMap.proj i).comp X)

@[simp] theorem rows_ofRows (v : Fin ℓ → H) : rows H (ofRows H v) = v := by
  funext i
  exact (Module.evalEquiv 𝕜 H).symm_apply_apply (v i)

def rowsEquiv : (Module.Dual 𝕜 H →ₗ[𝕜] (Fin ℓ → 𝕜)) ≃ (Fin ℓ → H) where
  toFun := rows H
  invFun := ofRows H
  left_inv := ofRows_rows H
  right_inv := rows_ofRows H

omit [FiniteDimensional 𝕜 H] in
@[simp] theorem evaluate_ofRows (v : Fin ℓ → H) (x : Ω) :
    evaluate H (ofRows H v) x = fun i => (v i).val x := rfl

end Rows
end
end PerfectCompleteness.EvaluationMatrix

end

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

def collision (f : Ω → Option Y) (p : Ω × Ω) : Bool :=
  decide (∃ y, f p.1 = some y ∧ f p.2 = some y)

end
end PerfectCompleteness.TwoResponseCollision



namespace PerfectCompleteness.DecoderTableAdmissibility

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]

def Admissible (valid : Q → A → Prop) (answers : Q → Option A) : Prop :=
  ∀ q a, answers q = some a → valid q a

end
end PerfectCompleteness.DecoderTableAdmissibility



namespace PerfectCompleteness.UpperParameterScalars

noncomputable section

def h (r ℓ : Nat) : ℝ := 1 / (2 : ℝ) ^ (r * ℓ)

def g (η : ℝ) (r ℓ : Nat) : ℝ := (η ^ 2 / 4) * h r ℓ

def q (η : ℝ) (r ℓ : Nat) : ℝ := g η r ℓ * h r ℓ

def rhoPred (κ α : ℝ) : ℝ := κ * α / 4

def b (κ α η : ℝ) (r ℓ : Nat) : ℝ := rhoPred κ α * q η r ℓ

def tau (κ α : ℝ) (r ℓ : Nat) : ℝ := rhoPred κ α * h r ℓ / 4

def gamma (κ α η : ℝ) (r ℓ : Nat) : ℝ :=
  b κ α η r ℓ * (1 / (2 : ℝ) ^ (ℓ + r)) * tau κ α r ℓ ^ 2 / 2

theorem h_pos (r ℓ : Nat) : 0 < h r ℓ := by unfold h; positivity

theorem g_pos {η : ℝ} (hη : 0 < η) (r ℓ : Nat) : 0 < g η r ℓ := by
  unfold g
  exact mul_pos (by positivity) (h_pos r ℓ)

theorem q_pos {η : ℝ} (hη : 0 < η) (r ℓ : Nat) : 0 < q η r ℓ :=
  mul_pos (g_pos hη r ℓ) (h_pos r ℓ)

theorem rhoPred_pos {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α) : 0 < rhoPred κ α := by
  unfold rhoPred
  positivity

theorem b_pos {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)
    (r ℓ : Nat) : 0 < b κ α η r ℓ :=
  mul_pos (rhoPred_pos hκ hα) (q_pos hη r ℓ)

theorem tau_pos {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    (r ℓ : Nat) : 0 < tau κ α r ℓ := by
  unfold tau
  exact div_pos (mul_pos (rhoPred_pos hκ hα) (h_pos r ℓ)) (by norm_num)

theorem gamma_pos {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)
    (r ℓ : Nat) : 0 < gamma κ α η r ℓ := by
  unfold gamma
  have hb := b_pos hκ hα hη r ℓ
  have ht := tau_pos hκ hα r ℓ
  positivity

end
end PerfectCompleteness.UpperParameterScalars

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_AscendingBranchingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.DescendingRows

open scoped BigOperators Classical
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier
open UpperParameterScalars

noncomputable section

structure Exclusion (threshold : ℝ) where
  order : Nat
  crossSize : Nat
  cutoff : Nat
  minimumRows : Nat
  density : ℝ
  order_pos : 1 ≤ order
  cross_pos : 0 < crossSize
  cutoff_pos : 1 ≤ cutoff
  density_pos : 0 < density
  density_lt_one : density < 1
  spectral : MatrixLevelBridge.levelCutoffConstant order density +
    RankLevelFilter.node (order + 1) < threshold
  row_bound : ∀ ℓ, minimumRows ≤ ℓ → 2 * crossSize + order ≤ ℓ
  error_bound : ∀ s, cutoff ≤ s →
    (2 : ℝ) ^ crossSize / (2 : ℝ) ^ (s - 2 * order) +
      (2 : ℝ) ^ (2 * crossSize) / (2 : ℝ) ^ (crossSize * crossSize) < density

variable {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)

def treeRows (depth : Nat) (rows : Nat → Nat) : Nat → Nat :=
  fun height => rows (depth - height)

end
end PerfectCompleteness.DescendingRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness

theorem countSatisfied_le_length {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) (es : List (Edge l r q)) :
    countSatisfied a b es ≤ es.length := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    simp only [countSatisfied, List.length_cons]
    split <;> omega

theorem countSatisfied_eq_length_iff {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) (es : List (Edge l r q)) :
    countSatisfied a b es = es.length ↔ ∀ e ∈ es, e.satisfied a b = true := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    have bound := countSatisfied_le_length a b es
    cases h : e.satisfied a b <;> simp_all [countSatisfied, Nat.add_comm]
    omega

theorem Instance.edgeCount_positive {q : Nat} (G : Instance q) :
    0 < G.edges.length := by
  cases h : G.edges with
  | nil => exact False.elim (G.nonempty h)
  | cons e es => simp

def PerfectlyComplete {q : Nat} (G : Instance q) : Prop :=
  ∃ s : Labeling G, ∀ e ∈ G.edges, e.satisfied s.1 s.2 = true

end PerfectCompleteness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness

theorem fiber_card_eq_filter_length {n : Nat} (p : Fin n → Prop)
    [DecidablePred p] :
    Fintype.card {a : Fin n // p a} =
      ((List.finRange n).filter (fun a => decide (p a))).length := by
  rw [Fintype.card_of_subtype
    (((List.finRange n).filter (fun a => decide (p a))).toFinset)
    (by intro a; simp)]
  exact List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)

def ProjectionTable.ofMap {q : Nat} (p : Fin (2 * q) → Fin q)
    (h : ∀ b, Fintype.card {a : Fin (2 * q) // p a = b} = 2) : ProjectionTable q where
  images := Vector.ofFn p
  exactlyTwo b := by
    simpa [fiber_card_eq_filter_length] using h b

@[simp] theorem ProjectionTable.ofMap_apply {q : Nat} (p : Fin (2 * q) → Fin q)
    (h : ∀ b, Fintype.card {a : Fin (2 * q) // p a = b} = 2) (a : Fin (2 * q)) :
    (ProjectionTable.ofMap p h).images[a] = p a := by
  simp [ProjectionTable.ofMap]

end PerfectCompleteness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeSourceSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeSourceSpaces

open MixedSupport

variable {branch : Nat → Nat} {n t : Nat}

instance slotDomainFintype (s : Slot) : Fintype s.Domain := by
  cases s with
  | clause occurrence variableIDs signs =>
      exact inferInstanceAs (Fintype (ClauseSupport.Answer signs))
  | bit variableID => exact inferInstanceAs (Fintype Bool)

end PerfectCompleteness.TreeSourceSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_SourceGame
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceGame

open SourceClause UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

def decodeLabel (signs : Triple) (label : Fin 7) : Triple :=
  (satisfyingTriples signs)[label.val]'(by
    rw [satisfyingTriples_length]
    exact label.isLt)

theorem decodeLabel_mem (signs : Triple) (label : Fin 7) :
    decodeLabel signs label ∈ satisfyingTriples signs := by
  exact List.getElem_mem _

theorem decodeLabel_injective (signs : Triple) : Function.Injective (decodeLabel signs) := by
  intro a b same
  apply Fin.ext
  exact (List.Nodup.getElem_inj_iff (satisfyingTriples_nodup signs)).mp same

end PerfectCompleteness.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_KeyFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport
open scoped BigOperators

variable {n : Nat} {Y : Type*}

abbrev KeyLabel (k : Key n) := ↥k.partition

instance KeyLabel_finite (k : Key n) : Finite (KeyLabel k) := by
  let : Finite ReducedValue := ReducedDomains.reducedValue_finite
  exact Finite.of_injective (fun P : KeyLabel k => P.val) Subtype.val_injective

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuotientTableAgreementLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ReducedPartition

variable {X R Y Z : Type*}

theorem fiber_kernel_invariant (r : X → R) (f : X → Y) (g : X → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') (x : X) :
    fiber r f x = fiber r g x := by
  ext v
  constructor
  · rintro ⟨z, hz, hfz⟩
    exact ⟨z, hz, (hkernel z x).1 hfz⟩
  · rintro ⟨z, hz, hgz⟩
    exact ⟨z, hz, (hkernel z x).2 hgz⟩

theorem parts_kernel_invariant (r : X → R) (f : X → Y) (g : X → Z)
    (hkernel : ∀ x x', f x = f x' ↔ g x = g x') :
    parts r f = parts r g := by
  have hfiber : fiber r f = fiber r g :=
    funext (fiber_kernel_invariant r f g hkernel)
  unfold parts
  rw [hfiber]

end PerfectCompleteness.ReducedPartition

end

section

namespace PerfectCompleteness.KeyStrategy

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys

abbrev NonemptyKey (n : Nat) := {k : Key n // k.partition.Nonempty}

abbrev Strategy (n : Nat) :=
  (k : NonemptyKey n) → {P : Set (Fin n → ReducedValue) // P ∈ k.val.partition}

variable {n : Nat} {Y Z : Type*}

def extend (vertices : Set (Key n))
    (σ : (k : ↥vertices) → {P : Set (Fin n → ReducedValue) // P ∈ k.val.partition}) :
    Strategy n := fun k =>
  if h : k.val ∈ vertices then σ ⟨k.val, h⟩
  else ⟨Classical.choose k.property, Classical.choose_spec k.property⟩

end
end PerfectCompleteness.KeyStrategy

end

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

abbrev Alphabet (_ : K) := Bool
abbrev LocalLabel (_ : K) := Unit
abbrev Label (chosen : List K) := MachineFiniteSequence.Label (LocalLabel (K := K)) chosen

def entry (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel (K := K)) (fun _ => ()) chosen labels exit

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceNoiseParameterLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The third queried Boolean table is `g * (f ∘ π) * μ` in sign notation. -/
def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

def representative (i₀ : I) (f : Cube I) : Cube I :=
  if f i₀ then cubeFlip f else f

omit [Fintype I] [DecidableEq I] in
theorem representative_at (i₀ : I) (f : Cube I) :
    representative i₀ f i₀ = false := by
  cases hf : f i₀ <;> simp [representative, cubeFlip, hf]

abbrev HalfCube (i₀ : I) := {f : Cube I // f i₀ = false}

def canonicalInput (i₀ : I) (f : Cube I) : HalfCube i₀ :=
  ⟨representative i₀ f, representative_at i₀ f⟩

/-- One stored bit and one explicit sign correction for every queried table. -/
def foldedAnswer (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) : Bool :=
  table (canonicalInput i₀ f) ^^ f i₀

def restrictQuery (valid : I → Bool) (f : Cube I) :
    Cube {i : I // valid i = true} := fun i => f i.val

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! The parity projection and finite Fourier decoder used in Håstad's
three-query argument. Probabilities are explicit finite sums. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem sign_power_parity (b : Bool) (n : Nat) :
    bitSign b ^ n = bitSign (decide (Odd n) && b) := by
  cases b
  · simp [bitSign]
  · simp only [Bool.and_true, bitSign, ite_true, if_true, decide_eq_true_eq]
    rw [neg_one_pow_eq_ite]
    by_cases h : Even n
    · simp [h, Nat.not_odd_iff_even.mpr h]
    · simp [h, Nat.not_even_iff_odd.mp h]

end UniqueGamesTheorem.Foundations.Hastad

end

end

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

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def parity (s f : Cube A) : Bool :=
  decide (Odd ((Finset.univ.filter fun a => s a && f a = true).card))

theorem bitSign_parity (s f : Cube A) : bitSign (parity s f) = walsh s f := by
  have hw : walsh s f = (-1 : ℝ) ^
      (Finset.univ.filter fun a => s a && f a = true).card := by
    simp [walsh, bitSign, Finset.prod_ite]
  rw [hw]
  simpa [parity, bitSign] using
    (sign_power_parity true (Finset.univ.filter fun a => s a && f a = true).card).symm

theorem bitSign_injective : Function.Injective bitSign := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitSign] <;> linarith

theorem parity_xor (s f g : Cube A) :
    parity s (cubeXor f g) = (parity s f ^^ parity s g) := by
  apply bitSign_injective
  rw [bitSign_parity, bitSign_xor, bitSign_parity, bitSign_parity, walsh_xor]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

def singleMask (i : A) : Cube A := fun j => decide (j = i)

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

omit [Fintype A] in
theorem flipAt_eq_xor (i : A) (f : Cube A) : flipAt i f = cubeXor f (singleMask i) := by
  funext j
  by_cases h : j = i <;> simp [flipAt, cubeXor, singleMask, h]

theorem walsh_singleMask (s : Cube A) (i : A) :
    walsh s (singleMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [singleMask]
  · intro j _ hj
    simp [singleMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem parity_singleMask (s : Cube A) (i : A) : parity s (singleMask i) = s i := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_singleMask]

theorem parity_flipAt (s : Cube A) (i : A) (f : Cube A) (hs : s i = true) :
    parity s (flipAt i f) = !(parity s f) := by
  rw [flipAt_eq_xor, parity_xor, parity_singleMask, hs]
  cases parity s f <;> rfl

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

variable {K : Type*} [Fintype K] [Nonempty K]

/-- The actual six oracle addresses for each test. Unused slots repeat an
address already queried, so every event has the same fixed six-slot format. -/
def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

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
open UniqueGamesTheorem.Foundations.Hastad

/-- The encoding is a literal coordinate read from a finite Boolean truth table. -/
def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

/-- Two equal-sized blocks, indexed by a side bit and a common coordinate. -/
def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

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

/-!
The explicit assignment tester applied to the encoded satisfying pairs of an
actual finite edge predicate.  The resulting soundness loss is independent of
the alphabet size.  Uniform padding of the finite sample space and assembly of
the global incidence graph are separate constructions.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

open UniqueGamesTheorem.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

abbrev InputCoordinate (A : Type*) := Bool × Cube A

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

end UniqueGamesTheorem.Foundations.PCP.AlphabetReduction

end

end

section

namespace UniqueGamesTheorem.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end UniqueGamesTheorem.Foundations.PCP

end

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Reindex

variable {W D B : Type*}

/-- Explicit changes of vertex, dart, and label coordinates. -/
def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

end Reindex

end UniqueGamesTheorem.Foundations.PCP.ConstraintGraph

end

end

section

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.FiniteGraph

/-- Graphs of different finite sizes inhabit one fixed type for iteration. -/
structure Bundle (A : Type) where
  Vertex : Type
  Dart : Type
  vertexFintype : Fintype Vertex
  dartFintype : Fintype Dart
  vertexDecidableEq : DecidableEq Vertex
  dartDecidableEq : DecidableEq Dart
  dartNonempty : Nonempty Dart
  graph : ConstraintGraph Vertex Dart A

namespace Bundle

variable {A : Type}

instance instFintypeVertex (G : Bundle A) : Fintype G.Vertex := G.vertexFintype
instance instFintypeDart (G : Bundle A) : Fintype G.Dart := G.dartFintype

def ofGraph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) : Bundle A where
  Vertex := V
  Dart := E
  vertexFintype := inferInstance
  dartFintype := inferInstance
  vertexDecidableEq := inferInstance
  dartDecidableEq := inferInstance
  dartNonempty := inferInstance
  graph := G

def size (G : Bundle A) : Nat := Fintype.card G.Vertex + Fintype.card G.Dart

def rejectionCount (G : Bundle A) (labeling : G.Vertex → A) : Nat :=
  G.graph.rejectionCount labeling

@[simp] theorem ofGraph_graph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).graph = G := rfl

@[simp] theorem ofGraph_size {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).size = Fintype.card V + Fintype.card E := rfl

@[simp] theorem ofGraph_rejectionCount {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) (labeling : V → A) :
    (ofGraph G).rejectionCount labeling = G.rejectionCount labeling := rfl

end Bundle

end UniqueGamesTheorem.Foundations.PCP.FiniteGraph

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ClauseVerifierLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open PCP

abbrev I (u : ℕ) := Fin u → Bool

@[simp] theorem card_I (u : ℕ) : Fintype.card (I u) = 2 ^ u := by simp [I]

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

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

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.InitialGraph

abbrev Label := Bool × Bool × Bool
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

section

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

/-- Exposes the first dart and the independent remaining port word. -/
def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- Advance across the first edge while retaining its reverse port. -/
def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

/-- The dart at the indicated time, computed by the actual preceding steps. -/
def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

end UniqueGamesTheorem.Foundations.PCP.PoweringWalks

end

section

/-!
Cloud replacement for arbitrary finite constraint graphs. The new vertices are
the old darts; internal ports enforce equality inside each cloud, and one
external port applies the original constraint. Dummy loop darts allow padding
each cloud independently before replacement.

The supplied cloud port graphs are explicit parameters; no expansion or
soundness claim is assumed.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

/-- The darts departing a specified vertex. -/
abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

/-- Conjugate the disjoint union of cloud rotations into global dart coordinates. -/
def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

/-- Internal ports rotate inside a cloud; the extra port reverses an old dart. -/
def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

/-- The equality constraints and inherited original constraints on the actual rotation. -/
def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

/-- Additional darts are attached to their specified original vertex. -/
abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

/-- Dummy darts are self-reversing loops with an always-accepting constraint. -/
def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

def paddedReplacementPortGraph (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    PortGraph (PaddedDart G dummy) (D ⊕ Unit) :=
  replacementPortGraph (paddedGraph G dummy) H

def paddedReplacementGraph [DecidableEq A]
    (G : ConstraintGraph V E A) (dummy : V → Type*)
    (H : ∀ v, PortGraph (Cloud (paddedGraph G dummy) v) D) :
    ConstraintGraph (PaddedDart G dummy) (PaddedDart G dummy × (D ⊕ Unit)) A :=
  replacementGraph (paddedGraph G dummy) H

end UniqueGamesTheorem.Foundations.PCP.DegreeReplacement

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

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

abbrev PortWords (D : Type*) (t : Nat) := (n : Fin (t + 1)) × (Fin n.val → D)

def Ball (G : PortGraph V D) (t : Nat) (v : V) :=
  {u : V // ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u}

def wordToBall (G : PortGraph V D) (t : Nat) (v : V) (w : PortWords D t) : Ball G t v :=
  ⟨wordEnd G w.1.val v w.2, w.1.val, Nat.le_of_lt_succ w.1.isLt, w.2, rfl⟩

theorem wordToBall_surjective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Surjective (wordToBall G t v) := by
  intro u
  obtain ⟨n, hn, p, hp⟩ := u.property
  refine ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, p⟩, ?_⟩
  exact Subtype.ext hp

structure AddressSelector (G : PortGraph V D) (t : Nat) (v : V) where
  address : Ball G t v → PortWords D t
  correct : ∀ u, wordToBall G t v (address u) = u

/-- Executable first-match search, with a proof that a match is present. -/
def scanWitness {A : Type*} (p : A → Prop) [DecidablePred p] :
    (xs : List A) → (∃ a ∈ xs, p a) → {a // p a}
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨a, ha⟩ else
      scanWitness p xs (by
        obtain ⟨b, hb, hp⟩ := h
        rcases List.mem_cons.mp hb with he | hm
        · exact False.elim (ha (he ▸ hp))
        · exact ⟨b, hm, hp⟩)

/-- A concrete complete address list supplies a computational selector. Its
length depends on the degree and radius, not on the ambient vertex count. -/
def listSelector [DecidableEq V] (G : PortGraph V D) (t : Nat) (v : V)
    (addresses : List (PortWords D t)) (complete : ∀ w, w ∈ addresses) :
    AddressSelector G t v where
  address u := (scanWitness (fun w => (wordToBall G t v w).val = u.val) addresses (by
    obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
    exact ⟨w, complete w, congrArg Subtype.val hw⟩)).val
  correct u := Subtype.ext (scanWitness
    (fun w => (wordToBall G t v w).val = u.val) addresses (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
      exact ⟨w, complete w, congrArg Subtype.val hw⟩)).property

abbrev PaddedLabel (D : Type*) (t : Nat) (A : Type*) := PortWords D t → A

def decode {G : PortGraph V D} {t : Nat} {v : V} (S : AddressSelector G t v)
    (a : PaddedLabel D t A) : Ball G t v → A := fun u => a (S.address u)

end UniqueGamesTheorem.Foundations.PCP.PoweringLabels

end

section

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

/-- All words of a specified length, ordered first by their head port. -/
def allWords (d : Nat) : (n : Nat) → List (Fin n → Fin d)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange d).flatMap fun a =>
      (allWords d n).map fun p => Fin.cases a p

theorem mem_allWords (d : Nat) :
    ∀ n (p : Fin n → Fin d), p ∈ allWords d n := by
  intro n
  induction n with
  | zero =>
    intro p
    simp only [allWords, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro p
    simp only [allWords, List.mem_flatMap, List.mem_map]
    refine ⟨p 0, List.mem_finRange (p 0), (fun j => p j.succ), ih _, ?_⟩
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

/-- The complete address list, including the unique empty word. -/
def allAddresses (d t : Nat) : List (PortWords (Fin d) t) :=
  (List.finRange (t + 1)).flatMap fun n =>
    (allWords d n.val).map fun p => Sigma.mk n p

theorem mem_allAddresses (d t : Nat) (w : PortWords (Fin d) t) :
    w ∈ allAddresses d t := by
  rcases w with ⟨n, p⟩
  unfold allAddresses
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_finRange n, ?_⟩
  exact List.mem_map.mpr ⟨p, mem_allWords d n.val p, rfl⟩

/-- A fully executable selector from the explicit bounded address list. -/
def finitePortSelector {d : Nat} [DecidableEq V] (G : PortGraph V (Fin d))
    (t : Nat) (v : V) : AddressSelector G t v :=
  listSelector G t v (allAddresses d t) (mem_allAddresses d t)

end UniqueGamesTheorem.Foundations.PCP.PoweringAddresses

end

section

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

/-- The number of words with length at most `t`, including the empty word. -/
def addressCount (d t : Nat) : Nat := ∑ i : Fin (t + 1), d ^ i.val

/-- Reverse the digit positions before using the little-endian arithmetic
encoding from mathlib. Both directions are the same executable operation. -/
def reverseWordEquiv (d n : Nat) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun p i := p i.rev
  invFun p i := p i.rev
  left_inv p := by funext i; simp only [Fin.rev_rev]
  right_inv p := by funext i; simp only [Fin.rev_rev]

/-- An executable bijection from fixed-length port words to their ranks. -/
def wordEquiv (d n : Nat) : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (reverseWordEquiv d n).trans finFunctionFinEquiv

/-- Arithmetic prefix sums give a rank for every bounded-length address. -/
def addressEquiv (d t : Nat) : PortWords (Fin d) t ≃ Fin (addressCount d t) :=
  (Equiv.sigmaCongrRight (fun i : Fin (t + 1) => wordEquiv d i.val)).trans
    finSigmaFinEquiv

/-- A padded label is a base-`q` integer whose digits are indexed by the
explicit bounded-address equivalence. -/
def paddedLabelEquiv (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) ≃ Fin (q ^ addressCount d t) :=
  ((addressEquiv d t).arrowCongr (Equiv.refl (Fin q))).trans
    (wordEquiv q (addressCount d t))

/-- False and true are the adjacent orientation digits zero and one. -/
def orientationEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem orientationEquiv_false : orientationEquiv false = 0 := rfl
@[simp] theorem orientationEquiv_true : orientationEquiv true = 1 := rfl

/-- A vertex's block consists of one adjacent orientation pair per word. -/
def dartBlockEquiv (d n : Nat) :
    ((Fin (n + 1) → Fin d) × Bool) ≃ Fin (2 * d ^ (n + 1)) :=
  ((wordEquiv d (n + 1)).prodCongr orientationEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (d ^ (n + 1)) 2)))

/-- The tuple permutation putting the vertex before its word and orientation. -/
def dartVertexEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      (Fin vertices × ((Fin (n + 1) → Fin d) × Bool)) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv x := by rcases x with ⟨b, v, p⟩; rfl
  right_inv x := by rcases x with ⟨v, p, b⟩; rfl

/-- Executable vertex-major dart numbering, with adjacent orientations. -/
def dartEquiv (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) ≃
      Fin (2 * vertices * d ^ (n + 1)) :=
  (dartVertexEquiv vertices d n).trans
    (((Equiv.refl (Fin vertices)).prodCongr (dartBlockEquiv d n)).trans
      (finProdFinEquiv.trans
        (finCongr (show vertices * (2 * d ^ (n + 1)) =
          2 * vertices * d ^ (n + 1) by ac_rfl))))

def decodeWord (d n : Nat) : Fin (d ^ n) → (Fin n → Fin d) := (wordEquiv d n).symm

def encodeAddress (d t : Nat) : PortWords (Fin d) t → Fin (addressCount d t) :=
  addressEquiv d t

def encodeLabel (d t q : Nat) :
    PaddedLabel (Fin d) t (Fin q) → Fin (q ^ addressCount d t) := paddedLabelEquiv d t q

def decodeLabel (d t q : Nat) :
    Fin (q ^ addressCount d t) → PaddedLabel (Fin d) t (Fin q) :=
  (paddedLabelEquiv d t q).symm

@[simp] theorem decodeLabel_encodeLabel (d t q : Nat) (a : PaddedLabel (Fin d) t (Fin q)) :
    decodeLabel d t q (encodeLabel d t q a) = a := (paddedLabelEquiv d t q).symm_apply_apply a

@[simp] theorem encodeLabel_decodeLabel (d t q : Nat) (i : Fin (q ^ addressCount d t)) :
    encodeLabel d t q (decodeLabel d t q i) = i := (paddedLabelEquiv d t q).apply_symm_apply i

@[simp] theorem decodeLabel_apply (d t q : Nat) (i : Fin (q ^ addressCount d t))
    (w : PortWords (Fin d) t) :
    decodeLabel d t q i w = decodeWord q (addressCount d t) i (encodeAddress d t w) := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringEnumeration

end

section

/-!
# Full-radius access to the endpoints of each actual walk edge

The tail of each traversed edge is reachable from the walk's start. Its head
is reachable from the walk's end by reversing the remaining suffix with the
actual arrival ports. These facts supply values in the two neighborhood-ball
types used by the endpoint label decoders.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringReach

open PoweringWalks PoweringLabels

variable {V D : Type*}

def ReachLE (G : PortGraph V D) (t : Nat) (u v : V) : Prop :=
  ∃ l, l ≤ t ∧ ∃ p : Fin l → D, wordEnd G l u p = v

theorem reach_refl (G : PortGraph V D) (t : Nat) (u : V) : ReachLE G t u u :=
  ⟨0, Nat.zero_le t, Fin.elim0, rfl⟩

theorem reach_mono {G : PortGraph V D} {s t : Nat} {u v : V}
    (hst : s ≤ t) (h : ReachLE G s u v) : ReachLE G t u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  exact ⟨l, hl.trans hst, p, hp⟩

theorem reach_prepend (G : PortGraph V D) {t : Nat} (u : V) (d : D) {v : V}
    (h : ReachLE G t (next G u d) v) : ReachLE G (t + 1) u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨l + 1, Nat.succ_le_succ hl,
    (fun i : Fin (l + 1) => Fin.cases d p i), ?_⟩
  simpa only [wordEnd, Fin.cases_zero, Fin.cases_succ] using hp

/-- Reversal records each arrival port, not the original outgoing port. -/
def reversePorts (G : PortGraph V D) : V → List D → List D
  | _, [] => []
  | v, d :: ds => reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]

theorem reversePorts_length (G : PortGraph V D) (v : V) (ds : List D) :
    (reversePorts G v ds).length = ds.length := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih => simp [reversePorts, ih]

theorem walkEnd_reversePorts (G : PortGraph V D) (v : V) (ds : List D) :
    walkEnd G (walkEnd G v ds) (reversePorts G v ds) = v := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    change walkEnd G (walkEnd G (next G v d) ds)
      (reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]) = v
    rw [walkEnd_append, ih]
    change (G.rot (G.rot (v, d))).1 = v
    exact congrArg Prod.fst (G.rot_involutive (v, d))

theorem wordEnd_eq_walkEnd_ofFn (G : PortGraph V D) :
    ∀ n v (p : Fin n → D), wordEnd G n v p = walkEnd G v (List.ofFn p) := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    rw [List.ofFn_succ, walkEnd_cons]
    exact ih (next G v (p 0)) (fun j => p j.succ)

theorem reach_reverse {G : PortGraph V D} {t : Nat} {u v : V}
    (h : ReachLE G t u v) : ReachLE G t v u := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨(reversePorts G u (List.ofFn p)).length, ?_,
    (reversePorts G u (List.ofFn p)).get, ?_⟩
  · simpa only [reversePorts_length, List.length_ofFn] using hl
  · rw [wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
    have hlist : walkEnd G u (List.ofFn p) = v := by
      rw [← wordEnd_eq_walkEnd_ofFn]
      exact hp
    rw [← hlist, walkEnd_reversePorts]

/-- The actual prefix places each traversed edge's tail in the start ball. -/
theorem tail_reach (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) w.1 (edgeAt G n w k).1 := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 w.1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact reach_refl G (n + 2) w.1
    · exact reach_prepend G w.1 (w.2 0) (ih (advanceTail G w) j)

/-- The suffix proceeds from the traversed edge's head to the walk endpoint. -/
theorem head_reach_endpoint (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) (G.rot (edgeAt G n w k)).1 (endpoint G w) := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 (G.rot (w.1, w.2 0)).1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨n + 1, Nat.le_succ (n + 1), (fun j => w.2 j.succ), rfl⟩
    · exact reach_mono (Nat.le_succ (n + 1)) (ih (advanceTail G w) j)

def tailFromStart (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) w.1 :=
  ⟨(edgeAt G n w k).1, tail_reach G n w k⟩

def headFromEnd (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) (endpoint G w) :=
  ⟨(G.rot (edgeAt G n w k)).1, reach_reverse (head_reach_endpoint G n w k)⟩

@[simp] theorem tailFromStart_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (tailFromStart G n w k).val = (edgeAt G n w k).1 := rfl

@[simp] theorem headFromEnd_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (headFromEnd G n w k).val = (G.rot (edgeAt G n w k)).1 := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringReach

end

section

/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace UniqueGamesTheorem.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def incidenceAccept [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q) : Bool :=
  decide (LeftValid T event left) &&
    decide (left (canonicalSlot T event slot) = decodeRight positive right)

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

def predicate [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    Dart E q → Label q → Label q → Bool
  | ((event, slot), false), a, b => incidenceAccept T positive event slot a b
  | ((event, slot), true), a, b => incidenceAccept T positive event slot b a

def graph [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    ConstraintGraph (Vertex E X) (Dart E q) (Label q) where
  reverse := reverseEquiv
  reverse_involutive := reverse_involutive
  tail := tail T
  accepts := predicate T positive
  reverse_accepts := by
    rintro ⟨⟨event, slot⟩, orientation⟩ a b
    cases orientation <;> rfl

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

@[simp] theorem card_vertex [Fintype E] [Fintype X] :
    Fintype.card (Vertex E X) = Fintype.card E + Fintype.card X := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart [Fintype E] :
    Fintype.card (Dart E q) = 2 * q * Fintype.card E := by
  simp [Dart, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end UniqueGamesTheorem.Foundations.PCP.QueryIncidence

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

/-!
Pull a graph predicate back through a surjective label decoder.  This preserves
every rejection count after decoding.  A concrete section embeds the initial
eight-label graph into the fixed 64-label alphabet used throughout amplification.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b c => G.accepts e (decode b) (decode c)
  reverse_accepts := fun e b c => G.reverse_accepts e (decode b) (decode c)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction

end

section

namespace UniqueGamesTheorem.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

def mean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := Finset.univ.expect f

def energy {A : Type*} [Fintype A] (f : A → ℝ) : ℝ := mean (fun x => (f x) ^ 2)

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

structure SpectralCertificate {V D : Type*} [Fintype V] [Fintype D]
    (G : PortGraph V D) (lambda : ℝ) : Prop where
  nonnegative : 0 ≤ lambda
  lt_one : lambda < 1
  contraction : ∀ f : V → ℝ, mean f = 0 →
    energy (averagingOperator G f) ≤ lambda ^ 2 * energy f

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem mean_prod (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simpa only [mean, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

@[simp] theorem mean_const [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c :=
  Fintype.expect_const c

end Averages

end

end UniqueGamesTheorem.Foundations.PCP.SpectralReturn

end

section

/-!
# Walsh diagonalization of actual Boolean-cube Cayley graphs

Every port is an indexed generator. The rotation keeps the port and adds its
generator by pointwise xor, so loops and repeated generators keep their full
multiplicity. The Fourier multiplier and energy estimate are proved for this
actual averaging operator; no Fourier/operator compatibility is assumed.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

/-- Uniform cube measure is invariant under this explicit xor translation. -/
def xorTranslation (y : Cube I) : Cube I ≃ Cube I where
  toFun x := cubeXor x y
  invFun x := cubeXor x y
  left_inv x := cubeXor_cancel_right x y
  right_inv x := cubeXor_cancel_right x y

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

/-- The undirected regular port graph generated by the indexed cube vectors. -/
def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

/-- Expose the first actual port in a finite port word. -/
def splitPortWord (n : Nat) : (Fin (n + 1) → D) ≃ D × (Fin n → D) where
  toFun p := (p 0, fun j => p j.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv p := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

/-- The generator of a powered port is the xor of its original port word. -/
def powerGenerators (g : D → Cube I) : (n : Nat) → (Fin n → D) → Cube I
  | 0, _ => zeroFrequency
  | n + 1, p => cubeXor (g (p 0)) (powerGenerators g n (fun j => p j.succ))

section Finite

variable [Fintype I] [DecidableEq I] [Fintype D]

/-- Average along the actual outgoing ports of the Cayley graph. -/
def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

/-- The eigenvalue is the empirical bias of the generator characters. -/
def eigenvalue (g : D → Cube I) (s : Cube I) : ℝ :=
  𝔼 d, walsh s (g d)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

@[simp] theorem coefficient_zeroFrequency (f : Cube I → ℝ) :
    coefficient f zeroFrequency = 𝔼 x, f x := by
  simp [coefficient, zeroFrequency, walsh, bitSign]

/-- Change variables through xor translation in the actual Fourier average. -/
theorem coefficient_xorTranslation (f : Cube I → ℝ) (s v : Cube I) :
    coefficient (fun x => f (cubeXor x v)) s = walsh s v * coefficient f s := by
  calc
    coefficient (fun x => f (cubeXor x v)) s =
        𝔼 x, f x * walsh s (cubeXor x v) := by
      unfold coefficient
      apply Fintype.expect_equiv (xorTranslation v)
      intro x
      change f (cubeXor x v) * walsh s x =
        f (cubeXor x v) * walsh s (cubeXor (cubeXor x v) v)
      rw [cubeXor_cancel_right]
    _ = 𝔼 x, (f x * walsh s x) * walsh s v := by
      apply Finset.expect_congr rfl
      intro x _
      rw [walsh_xor]
      ring
    _ = coefficient f s * walsh s v := by
      rw [← Finset.expect_mul]
      rfl
    _ = walsh s v * coefficient f s := mul_comm _ _

/-- Full Walsh diagonalization, obtained by swapping the two finite averages. -/
theorem coefficient_cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (s : Cube I) :
    coefficient (cayleyAverage g f) s = eigenvalue g s * coefficient f s := by
  calc
    coefficient (cayleyAverage g f) s =
        𝔼 x, 𝔼 d, f (cubeXor x (g d)) * walsh s x := by
      unfold coefficient cayleyAverage
      simp only [cayleyGraph_rot, Finset.expect_mul]
    _ = 𝔼 d, 𝔼 x, f (cubeXor x (g d)) * walsh s x := by
      rw [Finset.expect_comm]
    _ = 𝔼 d, walsh s (g d) * coefficient f s := by
      apply Finset.expect_congr rfl
      intro d _
      exact coefficient_xorTranslation f s (g d)
    _ = eigenvalue g s * coefficient f s := by
      rw [← Finset.expect_mul]
      rfl

/-- Uniform finite port-word splitting multiplies the actual eigenvalues. -/
theorem eigenvalue_powerGenerators (g : D → Cube I) (n : Nat) (s : Cube I) :
    eigenvalue (powerGenerators g n) s = eigenvalue g s ^ n := by
  induction n with
  | zero =>
    let : Nonempty (Fin 0 → D) := ⟨fun i => Fin.elim0 i⟩
    simp [eigenvalue, powerGenerators, zeroFrequency, walsh, bitSign]
  | succ n ih =>
    calc
      eigenvalue (powerGenerators g (n + 1)) s =
          𝔼 z : D × (Fin n → D),
            walsh s (cubeXor (g z.1) (powerGenerators g n z.2)) := by
        unfold eigenvalue
        apply Fintype.expect_equiv (splitPortWord n)
        intro p
        rfl
      _ = 𝔼 d, 𝔼 p : Fin n → D,
          walsh s (cubeXor (g d) (powerGenerators g n p)) := by
        exact SpectralReturn.mean_prod _
      _ = eigenvalue g s * eigenvalue (powerGenerators g n) s := by
        simp_rw [walsh_xor, ← Finset.mul_expect]
        rw [← Finset.expect_mul]
        rfl
      _ = eigenvalue g s ^ (n + 1) := by
        rw [ih, pow_succ, mul_comm]

theorem power_eigenvalue_bound (g : D → Cube I) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hbias : ∀ s : Cube I, s ≠ zeroFrequency → |eigenvalue g s| ≤ lambda)
    (n : Nat) (s : Cube I) (hs : s ≠ zeroFrequency) :
    |eigenvalue (powerGenerators g n) s| ≤ lambda ^ n := by
  rw [eigenvalue_powerGenerators, abs_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih (hbias s hs) (abs_nonneg _) (pow_nonneg hlambda _)

end Finite

end UniqueGamesTheorem.Foundations.PCP.CayleySpectral

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CayleySampling
attribute [-instance] _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Hastad

variable {V D : Type*}

/-- The common fiber left after separating a Boolean character's sign. -/
abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

theorem expect_boolean_samples [Fintype V] [Nonempty V] [Fintype D] [DecidableEq D]
    (χ : V → Bool) (flip : V → V) (hflip : Function.Involutive flip)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (F : (D → Bool) → ℝ) :
    (𝔼 g : D → V, F (fun d => χ (g d))) = 𝔼 b : D → Bool, F b := by
  classical
  have : Nonempty (FalseFiber χ) :=
    ⟨falseRepresentative χ flip hχ (Classical.choice ‹Nonempty V›)⟩
  calc
    (𝔼 g : D → V, F (fun d => χ (g d))) =
        𝔼 p : (D → Bool) × (D → FalseFiber χ), F p.1 := by
      apply Fintype.expect_equiv (sampleSplitEquiv χ flip hflip hχ)
      intro g
      rfl
    _ = 𝔼 b : D → Bool, F b := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

section Walsh

variable {I : Type*} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
theorem exists_true_of_ne_zero (s : Cube I) (hs : s ≠ fun _ => false) :
    ∃ i, s i = true := by
  by_contra h
  apply hs
  funext i
  cases hi : s i
  · rfl
  · exact False.elim (h ⟨i, hi⟩)

/-- Actual parity words from independently indexed uniform cube vectors have
exactly the uniform Boolean-word distribution. -/
theorem expect_parity_samples (s : Cube I) (hs : s ≠ fun _ => false)
    (F : (D → Bool) → ℝ) :
    (𝔼 g : D → Cube I, F (fun d => AssignmentTester.parity s (g d))) =
      𝔼 b : D → Bool, F b := by
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero s hs
  exact expect_boolean_samples (AssignmentTester.parity s) (AssignmentTester.flipAt i)
    (AssignmentTester.flipAt_twice i)
    (fun x => AssignmentTester.parity_flipAt s i x hi) F

end Walsh

end UniqueGamesTheorem.Foundations.PCP.CayleySampling

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CayleyTailCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite binary-word tail counts for the proposed Cayley base graph.

No expander, independence, spectral, or random-generator existence result is
assumed here.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CayleyTailCount

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad (bitSign)

variable {α : Type*} [DecidableEq α]

def upperMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => 3 * m ≤ t.card

def lowerMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  s.powerset.filter fun t => t.card ≤ m

def badMasks (s : Finset α) (m : ℕ) : Finset (Finset α) :=
  lowerMasks s m ∪ upperMasks s m

omit [DecidableEq α] in
/-- Weight every actual upper-tail mask by at least `3 ^ (3 * m)`. -/
theorem upperMasks_weight (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    (upperMasks s m).card * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by
  calc
    _ = ∑ _t ∈ upperMasks s m, 3 ^ (3 * m) := by simp
    _ ≤ ∑ t ∈ upperMasks s m, 3 ^ t.card := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.pow_le_pow_right (by decide) (Finset.mem_filter.mp ht).2
    _ ≤ ∑ t ∈ s.powerset, 3 ^ t.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t _ _
        exact Nat.zero_le _
    _ = 4 ^ s.card := by
      simpa using Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 s
    _ = 4 ^ (4 * m) := by rw [hcard]

/-- Complementation preserves multiplicity and exchanges the two closed tails. -/
theorem lowerMasks_complement_image (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).image (fun t => s \ t) = upperMasks s m := by
  ext u
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hts, htlo⟩ := Finset.mem_filter.mp ht
    have hsub := Finset.mem_powerset.mp hts
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  · intro hu
    obtain ⟨hus, huhi⟩ := Finset.mem_filter.mp hu
    have hsub := Finset.mem_powerset.mp hus
    apply Finset.mem_image.mpr
    refine ⟨s \ u, ?_, Finset.sdiff_sdiff_eq_self hsub⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega

theorem lowerMasks_card_eq_upperMasks (s : Finset α) (m : ℕ)
    (hcard : s.card = 4 * m) :
    (lowerMasks s m).card = (upperMasks s m).card := by
  have hinj : Set.InjOn (fun t : Finset α => s \ t) (lowerMasks s m) := by
    intro a ha b hb hab
    have has := Finset.mem_powerset.mp (Finset.mem_filter.mp ha).1
    have hbs := Finset.mem_powerset.mp (Finset.mem_filter.mp hb).1
    have h := congrArg (fun t : Finset α => s \ t) hab
    simpa only [Finset.sdiff_sdiff_eq_self has, Finset.sdiff_sdiff_eq_self hbs] using h
  calc
    _ = ((lowerMasks s m).image (fun t => s \ t)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = _ := congrArg Finset.card (lowerMasks_complement_image s m hcard)

theorem ratio_le_of_weight (c m : ℕ)
    (h : c * 3 ^ (3 * m) ≤ 4 ^ (4 * m)) :
    (c : ℝ) / 2 ^ (4 * m) ≤ (16 / 27 : ℝ) ^ m := by
  have hc : (c : ℝ) * 3 ^ (3 * m) ≤ 4 ^ (4 * m) := by exact_mod_cast h
  have h3 : 0 < (3 : ℝ) ^ (3 * m) := by positivity
  have h2 : 0 < (2 : ℝ) ^ (4 * m) := by positivity
  calc
    _ ≤ ((4 : ℝ) ^ (4 * m) / 3 ^ (3 * m)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ h3).mpr hc) h2.le
    _ = _ := by
      rw [pow_mul, pow_mul, pow_mul, ← div_pow, ← div_pow]
      norm_num

omit [DecidableEq α] in
theorem upperMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((upperMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [hcard]
  exact ratio_le_of_weight _ m (upperMasks_weight s m hcard)

theorem lowerMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((lowerMasks s m).card : ℝ) / 2 ^ s.card ≤ (16 / 27 : ℝ) ^ m := by
  rw [lowerMasks_card_eq_upperMasks s m hcard]
  exact upperMasks_ratio_le s m hcard

theorem badMasks_ratio_le_sharp (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (16 / 27 : ℝ) ^ m := by
  have hc : ((badMasks s m).card : ℝ) ≤
      (lowerMasks s m).card + (upperMasks s m).card := by
    exact_mod_cast (Finset.card_union_le (lowerMasks s m) (upperMasks s m))
  have hpos : 0 < (2 : ℝ) ^ s.card := by positivity
  calc
    _ ≤ ((lowerMasks s m).card + (upperMasks s m).card : ℝ) / 2 ^ s.card :=
      div_le_div_of_nonneg_right hc hpos.le
    _ = ((lowerMasks s m).card : ℝ) / 2 ^ s.card +
        ((upperMasks s m).card : ℝ) / 2 ^ s.card := add_div _ _ _
    _ ≤ (16 / 27 : ℝ) ^ m + (16 / 27 : ℝ) ^ m :=
      add_le_add (lowerMasks_ratio_le s m hcard) (upperMasks_ratio_le s m hcard)
    _ = _ := by ring

theorem badMasks_ratio_le (s : Finset α) (m : ℕ) (hcard : s.card = 4 * m) :
    ((badMasks s m).card : ℝ) / 2 ^ s.card ≤ 2 * (2 / 3 : ℝ) ^ m := by
  apply (badMasks_ratio_le_sharp s m hcard).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num) (by norm_num) m) (by norm_num)

section Words

variable {D : Type*} [Fintype D]

def trueMask (word : D → Bool) : Finset D :=
  Finset.univ.filter fun i => word i = true

def countTrue (word : D → Bool) : ℕ := (trueMask word).card

def badWord (m : ℕ) (word : D → Bool) : Prop :=
  countTrue word ≤ m ∨ 3 * m ≤ countTrue word

instance instDecidableBadWord (m : ℕ) (word : D → Bool) : Decidable (badWord m word) :=
  inferInstanceAs (Decidable (countTrue word ≤ m ∨ 3 * m ≤ countTrue word))

/-- The sign convention is the existing Walsh convention: false is +1, true is -1. -/
theorem bitSign_mean_eq [Nonempty D] (word : D → Bool) :
    (𝔼 i, bitSign (word i)) =
      1 - 2 * ((countTrue word : ℝ) / Fintype.card D) := by
  have hsign (b : Bool) : bitSign b = 1 - 2 * (if b = true then (1 : ℝ) else 0) := by
    cases b <;> norm_num [bitSign]
  calc
    _ = (𝔼 i : D, (1 - 2 * (if word i = true then (1 : ℝ) else 0))) := by
      apply Finset.expect_congr rfl
      intro i _
      exact hsign (word i)
    _ = 1 - 2 * (𝔼 i, if word i = true then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
      rfl

/-- Excluding both closed integer tails bounds the actual mean Walsh sign. -/
theorem not_badWord_bias (m : ℕ) (hcard : Fintype.card D = 4 * m) (hm : 0 < m)
    (word : D → Bool) (hword : ¬ badWord m word) :
    |𝔼 i, bitSign (word i)| ≤ (1 / 2 : ℝ) := by
  have hD : 0 < Fintype.card D := by rw [hcard]; omega
  let : Nonempty D := Fintype.card_pos_iff.mp hD
  have hlo : m < countTrue word := lt_of_not_ge (not_or.mp hword).1
  have hhi : countTrue word < 3 * m := lt_of_not_ge (not_or.mp hword).2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlor : (m : ℝ) ≤ countTrue word := by exact_mod_cast hlo.le
  have hhir : (countTrue word : ℝ) ≤ 3 * m := by exact_mod_cast hhi.le
  have hden : 0 < 4 * (m : ℝ) := by positivity
  have hratioLo : (1 / 4 : ℝ) ≤ (countTrue word : ℝ) / (4 * m) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hratioHi : (countTrue word : ℝ) / (4 * m) ≤ (3 / 4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  rw [bitSign_mean_eq word, hcard]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  apply abs_le.mpr
  constructor <;> linarith

/-- All words occur once, so subset counting keeps the actual uniform law. -/
def wordMaskEquiv [DecidableEq D] : (D → Bool) ≃ Finset D where
  toFun := trueMask
  invFun s i := decide (i ∈ s)
  left_inv word := by
    funext i
    cases h : word i <;> simp [trueMask, h]
  right_inv s := by
    ext i
    simp [trueMask]

/-- Actual real uniform expectation on binary words, including both closed tails. -/
theorem twoTail_probability [DecidableEq D] (m : ℕ) (hcard : Fintype.card D = 4 * m) :
    (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) ≤
      2 * (2 / 3 : ℝ) ^ m := by
  classical
  have he : (𝔼 word : D → Bool, if badWord m word then (1 : ℝ) else 0) =
      (𝔼 s : Finset D, if s.card ≤ m ∨ 3 * m ≤ s.card then (1 : ℝ) else 0) := by
    apply Finset.expect_equiv (wordMaskEquiv (D := D))
    · intro word
      simp
    · intro word _
      rfl
  have hs : (Finset.univ.filter fun s : Finset D => s.card ≤ m ∨ 3 * m ≤ s.card) =
      badMasks (Finset.univ : Finset D) m := by
    ext s
    simp [badMasks, lowerMasks, upperMasks]
  rw [he, Fintype.expect_eq_sum_div_card, Finset.sum_boole, hs, Fintype.card_finset]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Finset.card_univ] using
    badMasks_ratio_le (Finset.univ : Finset D) m (by simpa using hcard)

end Words

/-- Numerical budget for a union bound over at most `2 ^ n` frequencies. -/
theorem union_bound_le_half (n m : ℕ) (hm : 3 * (n + 2) ≤ m) :
    (2 : ℝ) ^ n * (2 * (2 / 3 : ℝ) ^ m) ≤ 1 / 2 := by
  have hpow : (2 / 3 : ℝ) ^ m ≤ (2 / 3 : ℝ) ^ (3 * (n + 2)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hbase : (2 / 3 : ℝ) ^ (3 * (n + 2)) ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) (n + 2)
  calc
    _ ≤ (2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hpow.trans hbase) (by norm_num)) (by positivity)
    _ = 1 / 2 := by
      rw [pow_add, div_pow]
      norm_num
      field_simp
      norm_num

end UniqueGamesTheorem.Foundations.PCP.CayleyTailCount

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_GraphTables
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTables

open UniqueGamesTheorem.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

/-- The fixed row-major ordering of the complete predicate table. -/
def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

/-- The row itself is finite data; index bounds are checked while parsing. -/
structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

/-- The two graph laws are decidable finite checks on the stored rows. -/
def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance instDecidableValid {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

/-- The ordered list serialized by the codec. Equal rows remain separate. -/
def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

/-- Decode validated finite data into the actual constraint-graph semantics. -/
def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

/-- Complete semantic graph roundtrip, including its actual reversal map. -/
@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : RelationTable) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : RelationTable) :
    (relationWords relation).length = 4096 := by simp [relationWords]

def parseRelation (words : List Nat) : Option RelationTable := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = 4096 then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : RelationTable) :
    parseRelation (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

end UniqueGamesTheorem.Foundations.PCP.GraphTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_GenericGraphTables
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.padded_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.DegreeReplacement.replacement_satisfied_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

open UniqueGamesTheorem.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

/-- The fixed row-major ordering of the complete predicate table. -/
def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

@[simp] theorem relationAt_relationOf (predicate : (Label q) → (Label q) → Bool) (a b : (Label q)) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

/-- The row itself is finite data; index bounds are checked while parsing. -/
structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

/-- The two graph laws are decidable finite checks on the stored rows. -/
def Valid {n m : Nat} (rows : Rows q n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance instDecidableValid {n m : Nat} (rows : Rows q n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table (q : Nat) where
  vertices : Nat
  darts : Nat
  rows : Rows q vertices darts
  valid : Valid rows

/-- The ordered list serialized by the codec. Equal rows remain separate. -/
def rowList (table : (Table q)) : List (DartRow q table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : (Table q)) : (rowList table).length = table.darts := by
  simp [rowList]

/-- Decode validated finite data into the actual constraint-graph semantics. -/
def semantics (table : (Table q)) : ConstraintGraph (Fin table.vertices) (Fin table.darts) (Label q) where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : (Table q)) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : (Table q)) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : (Table q)) (e : Fin table.darts) (a b : (Label q)) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : Rows q n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : (Table q) :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

/-- Complete semantic graph roundtrip, including its actual reversal map. -/
@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) :
    ConstraintGraph (Fin n) (Fin m) (Label q) where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) : (Table q) :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : (RelationTable q)) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : (RelationTable q)) :
    (relationWords relation).length = (q * q) := by simp [relationWords]

def parseRelation (q : Nat) (words : List Nat) : Option (RelationTable q) := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = (q * q) then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : (RelationTable q)) :
    (parseRelation q) (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow q n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

end UniqueGamesTheorem.Foundations.PCP.GenericGraphTables

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
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

open UniqueGamesTheorem.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords parseRelation parseRelation_encoded )

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Input

end

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
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

/-- The relation register is a finite tuple of bits, with no unbounded storage. -/
def relationEquiv (q : Nat) : RelationTable q ≃ (Fin (q * q) → Bool) where
  toFun relation i := relation[i.val]
  invFun := Vector.ofFn
  left_inv relation := Vector.ofFn_getElem
  right_inv bits := by funext i; simp

/-- Executable enumeration used when assembling the finite machine state. -/
@[instance_reducible] def relationFintype (q : Nat) : Fintype (RelationTable q) :=
  Fintype.ofEquiv (Fin (q * q) → Bool) (relationEquiv q).symm

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.ReadRelation

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

namespace UniqueGamesTheorem.Foundations.PCP.Expanders

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Hastad
open CayleySpectral

abbrev Generators (n m : Nat) := Fin (4 * m) → Cube (Fin n)

/-- The zero character is excluded from the bad-event count. -/
def badFrequency {n m : Nat} (g : Generators n m) (s : Cube (Fin n)) : ℝ :=
  if s = zeroFrequency then 0 else
    if CayleyTailCount.badWord m (fun d => AssignmentTester.parity s (g d)) then 1 else 0

def badMass {n m : Nat} (g : Generators n m) : ℝ :=
  ∑ s : Cube (Fin n), badFrequency g s

theorem badFrequency_nonnegative {n m : Nat}
    (g : Generators n m) (s : Cube (Fin n)) : 0 ≤ badFrequency g s := by
  unfold badFrequency
  split_ifs <;> norm_num

def baseDimension : Nat := 448
def initialDegree : Nat := 2 ^ 16
def initialQuarterDegree : Nat := 2 ^ 14
def basePower : Nat := 7

theorem base_arithmetic :
    4 * initialQuarterDegree = initialDegree ∧
    3 * (baseDimension + 2) ≤ initialQuarterDegree ∧
    (2 : Nat) ^ baseDimension = (initialDegree ^ basePower) ^ 4 ∧
    (1 / 2 : ℝ) ^ basePower ≤ 1 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [initialDegree, initialQuarterDegree]
  · norm_num [baseDimension, initialQuarterDegree]
  · unfold baseDimension initialDegree basePower
    rw [← pow_mul, ← pow_mul]
  · norm_num [basePower]

abbrev BaseVertex := Cube (Fin baseDimension)
abbrev BasePort := Fin basePower → Fin (4 * initialQuarterDegree)
def baseDegree : Nat := initialDegree ^ basePower

theorem card_basePort : Fintype.card BasePort = baseDegree := by
  simp only [BasePort, Fintype.card_fun, Fintype.card_fin]
  rw [base_arithmetic.1]
  rfl

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

end UniqueGamesTheorem.Foundations.PCP.Expanders

/-! Exact changes of finite vertex and port coordinates. The graph rotation and
its normalized averaging operator are transported by the same equivalences. -/

namespace UniqueGamesTheorem.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

/-- A coordinate change preserves the actual spectral certificate, including
the uniform measure on the port alphabet. -/
theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h

end UniqueGamesTheorem.Foundations.PCP.GraphTransport

section

/-! The actual half-lazy port graph retains a Boolean stay/step flag and an
ordinary port. This supplies the concrete graph underlying Boolean-tape
length smoothing. -/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def lazyRotate (G : PortGraph V D) : Edge V (Bool × D) → Edge V (Bool × D)
  | (v, (false, d)) => (v, (false, d))
  | (v, (true, d)) => ((G.rot (v, d)).1, (true, (G.rot (v, d)).2))

theorem lazyRotate_involutive (G : PortGraph V D) :
    Function.Involutive (lazyRotate G) := by
  rintro ⟨v, b, d⟩
  cases b with
  | false => rfl
  | true =>
    exact congrArg (fun e : V × D => (e.1, (true, e.2))) (rot_rot G (v, d))

def lazyGraph (G : PortGraph V D) : PortGraph V (Bool × D) where
  rot := {
    toFun := lazyRotate G
    invFun := lazyRotate G
    left_inv := lazyRotate_involutive G
    right_inv := lazyRotate_involutive G }
  rot_involutive := lazyRotate_involutive G

@[simp] theorem lazyGraph_rot_false (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (false, d)) = (v, (false, d)) := rfl

@[simp] theorem lazyGraph_rot_true (G : PortGraph V D) (v : V) (d : D) :
    (lazyGraph G).rot (v, (true, d)) = ((G.rot (v, d)).1, (true, (G.rot (v, d)).2)) := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringWalks

end

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

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
# Actual graph squares and zigzag products

Rotations operate on actual vertex-port pairs. All returned ports are retained,
including ports belonging to loops and parallel edges. Each construction is a
palindrome of involutions and hence defines a reversible regular port graph.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

/-- Regard a checked involution as a permutation with the same inverse. -/
def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

/-- A palindrome of two involutions is itself an involution. -/
theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

/-- Cross an original edge using the first port; retain its return port. -/
def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

/-- The actual graph square. The two return ports appear in reverse order. -/
def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

/-- One inner step in a cloud, retaining its return port and the unused port. -/
def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

/-- Cross the outer graph edge and swap the two inner ports. -/
def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

/-- The actual zigzag product: inner step, outer edge, inner step. -/
def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

/-! ## Exact averaging operators -/

end UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs

end

section

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

/-- The family is a recursive rotation algorithm when its fixed base is given. -/
def graph (H : PortGraph CloudPort BasePort) : (n : Nat) → PortGraph (Vertex n) Port
  | 0 => { rot := Equiv.refl _, rot_involutive := fun _ => rfl }
  | n + 1 => ZigzagGraphs.zigzag (ZigzagGraphs.square (graph H n)) H

theorem card_vertex (n : Nat) : Fintype.card (Vertex n) = growth ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × CloudPort) = growth ^ (n + 1)
    rw [Fintype.card_prod, ih, card_cloudPort, pow_succ]

/-- The least geometric level covering a requested size. `Nat.clog` is the
ordinary finite ceiling logarithm algorithm. -/
def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

end UniqueGamesTheorem.Foundations.PCP.ExpanderFamily

end

section

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

namespace UniqueGamesTheorem.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

/-- Leave empty clouds empty; pad every positive size to a geometric level. -/
def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

/-- The actual padded tail fiber contains old darts and exactly the dummy
darts indexed by that tail, with transport along the sigma index equality. -/
def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

section Finite

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem card_padded_cloud (G : ConstraintGraph V E A) (dummy : V → Type*)
    [∀ v, Fintype (dummy v)] (v : V) :
    Fintype.card (Cloud (paddedGraph G dummy) v) =
      Fintype.card (Cloud G v) + Fintype.card (dummy v) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (paddedCloudEquiv G dummy v)

/-- The precise number of always-accepting loop darts to add at each vertex. -/
abbrev dummy (G : ConstraintGraph V E A) (v : V) :=
  Fin (paddedSize (Fintype.card (Cloud G v)) - Fintype.card (Cloud G v))

end Finite

end UniqueGamesTheorem.Foundations.PCP.CloudPadding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpanderTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

/-- Stored reverse-dart indices, with a proof of the finite involution law. -/
structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

def graph {v d : Nat} (table : Table v d) : PortGraph (Fin v) (Fin d) where
  rot := ZigzagGraphs.involutionEquiv (lookup table) (lookup_involutive table)
  rot_involutive := lookup_involutive table

@[simp] theorem graph_rot {v d : Nat} (table : Table v d) (x : Fin v × Fin d) :
    (graph table).rot x = lookup table x := rfl

def ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) : Table v d where
  rows := Vector.ofFn (fun i => rowIndex v d (G.rot ((rowIndex v d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
    exact (congrArg (rowIndex v d) (G.rot_involutive ((rowIndex v d).symm i))).trans
      ((rowIndex v d).apply_symm_apply i)

@[simp] theorem lookup_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d))
    (x : Fin v × Fin d) : lookup (ofGraph G) x = G.rot x := by
  simp only [lookup, reverseIndex, ofGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

theorem graph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

@[simp] theorem graph_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) :
    graph (ofGraph G) = G := graph_ext (lookup_ofGraph G)

/-- Explicit mixed-radix vertex coordinates for one square/zigzag step. -/
def vertexIndex (v q : Nat) : Fin v × (Fin q × Fin q) ≃ Fin (v * (q * q)) :=
  (Equiv.prodCongr (Equiv.refl _) (rowIndex q q)).trans (rowIndex v (q * q))

/-- The actual square/zigzag graph, expressed in the table's integer coordinates. -/
def stepGraph {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    PortGraph (Fin (v * ((d * d) * (d * d)))) (Fin (d * d)) :=
  GraphTransport.reindex
    (ZigzagGraphs.zigzag (ZigzagGraphs.square (graph G))
      (GraphTransport.reindex (graph H) (rowIndex (d * d) (d * d)).symm (Equiv.refl _)))
    (vertexIndex v (d * d)) (rowIndex d d)

/-- Materialize every row of the next table in the declared order. -/
def step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    Table (v * ((d * d) * (d * d))) (d * d) := ofGraph (stepGraph G H)

def initial (d : Nat) : Table 1 (d * d) :=
  ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

def vertexCount (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => vertexCount q n * (q * q)

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

/-- A bottom-up vector of rotation rows. The recursive result is passed once
to `step`, whose row formula reads only that already materialized table. -/
def family {d : Nat} (H : Table ((d * d) * (d * d)) d) :
    (n : Nat) → Table (vertexCount (d * d) n) (d * d)
  | 0 => initial d
  | n + 1 => step (family H n) H

end UniqueGamesTheorem.Foundations.PCP.ExpanderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_OverlayLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Overlay a regular constraint graph with an actual regular port graph whose
new constraints always accept. The port sets are disjoint, so all original
rejected darts are retained exactly. The averaging operator is the actual
degree-weighted mixture of the two graph averages.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

/-- Keep the original tests and add always-accepting tests on the overlay ports. -/
def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

end UniqueGamesTheorem.Foundations.PCP.Overlay

end

section

/-! Lazification of the actual constraint graph. Original ports retain their
tests; the equally many stay-put ports always accept. The reverse is precisely
the existing lazy port-graph rotation used by the spectral and walk lemmas. -/
namespace UniqueGamesTheorem.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a c
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a c

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

end UniqueGamesTheorem.Foundations.PCP.LazyConstraint

end

section

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

/-- An explicit complete list supplies both directions of a finite encoding.
The forward direction searches the list; its inverse performs list indexing. -/
def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

end

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

/-- The carried size remains the exact power of the carried exponent. -/
theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

/-- The search never passes an exponent whose power already covers the
request. This remains true even without a sufficient fuel budget. -/
theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

def searchResult (k : Nat) : Nat × Nat :=
  levelLoop ExpanderFamily.growth k k 0 1

/-- An executable exponent, computed with at most `k` multiplications. -/
def boundedLevel (k : Nat) : Nat := (searchResult k).1

/-- The algorithm returns the power it has already computed. -/
def paddedSize (k : Nat) : Nat := (searchResult k).2

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

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

inductive Tape
  | input | work | power | saved | level | fuel | spare | product
  deriving DecidableEq

def memory (input work power saved level fuel spare product : List Bool) : Tape → List Bool
  | .input => input
  | .work => work
  | .power => power
  | .saved => saved
  | .level => level
  | .fuel => fuel
  | .spare => spare
  | .product => product

@[simp] theorem update_work (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .work x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_saved (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .saved x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_level (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .level x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e x g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_product (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .product x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Seed the destination delimiter before scanning the unary payload. -/
def fieldStart (destination : K) (loopLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push destination (fun _ => false) (.goto fun _ => loopLabel)

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

end UniqueGamesTheorem.Foundations.Hastad.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLookupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def discard (source : K) (loopLabel returnLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => returnLabel)))

/-- Check that a field exists before seeding its destination delimiter. -/
def select (source destination : K) (copyLabel rejected : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (Hastad.SourceMachine.fieldStart destination copyLabel)
      (.load (fun state => (state.1, none)) (.goto fun _ => rejected)))

inductive Label
  | guard | skip | select | copy | accepted | rejected
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skip, .select, .copy, .accepted,
  .rejected]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Three caller tapes with every other tape retained verbatim. -/
def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

@[simp] theorem tapes_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output index = counter := by
  simp [tapes, his, hid]

@[simp] theorem tapes_source (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) :
    tapes index source destination base counter input output source = input := by
  simp [tapes, hsd]

@[simp] theorem tapes_destination (index source destination : K)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output destination = output := by
  simp [tapes]

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

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

inductive Tape
  | original | work | target | scratch | count | spare
  deriving DecidableEq

def memory (original work target scratch count spare : List Bool) : Tape → List Bool
  | .original => original
  | .work => work
  | .target => target
  | .scratch => scratch
  | .count => count
  | .spare => spare

@[simp] theorem memory_original (a b c d e f : List Bool) :
    memory a b c d e f .original = a := rfl
@[simp] theorem memory_work (a b c d e f : List Bool) :
    memory a b c d e f .work = b := rfl
@[simp] theorem memory_target (a b c d e f : List Bool) :
    memory a b c d e f .target = c := rfl
@[simp] theorem memory_scratch (a b c d e f : List Bool) :
    memory a b c d e f .scratch = d := rfl
@[simp] theorem memory_count (a b c d e f : List Bool) :
    memory a b c d e f .count = e := rfl
@[simp] theorem memory_spare (a b c d e f : List Bool) :
    memory a b c d e f .spare = f := rfl

@[simp] theorem update_memory_work (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .work x = memory a x c d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_target (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .target x = memory a b x d e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_scratch (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .scratch x = memory a b c x e f := by
  funext k
  cases k <;> rfl
@[simp] theorem update_memory_count (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .count x = memory a b c d x f := by
  funext k
  cases k <;> rfl

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
namespace Placement

variable {K K' Λ Λ' σ : Type}

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

end Placement

inductive Tape
  | table | query | count | work | scratch | spare | power | level | fuel | product
  deriving DecidableEq

def memory (table query count work scratch spare power level fuel product : List Bool) :
    Tape → List Bool
  | .table => table
  | .query => query
  | .count => count
  | .work => work
  | .scratch => scratch
  | .spare => spare
  | .power => power
  | .level => level
  | .fuel => fuel
  | .product => product

@[simp] theorem update_count (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .count x = memory a b x d e f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_scratch (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .scratch x = memory a b c d x f g h i j := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .power x = memory a b c d e f x h i j := by
  funext k; cases k <;> rfl

@[simp] theorem update_level (a b c d e f g h i j x : List Bool) :
    Function.update (memory a b c d e f g h i j) .level x = memory a b c d e f g x i j := by
  funext k; cases k <;> rfl

def countView : Tape → Option MachineCloudCount.Tape
  | .table => some .original
  | .query => some .target
  | .count => some .count
  | .work => some .work
  | .scratch => some .scratch
  | .spare => some .spare
  | _ => none

@[simp] theorem countMemory (a b c d e f g h i j : List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f)
      (memory a b c d e f g h i j) = memory a b c d e f g h i j := by
  funext k; cases k <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.Completion

variable {L A B : Type*}

def fiberEquivTwo (e : A ≃ B × Fin 2) (b : B) :
    {a : A // (e a).1 = b} ≃ Fin 2 where
  toFun a := (e a.val).2
  invFun j := ⟨e.symm (b, j), by simp⟩
  left_inv a := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl
  right_inv j := by simp

theorem exists_slot_embedding [Fintype L] [Fintype B] [DecidableEq B]
    (p : L → B) (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2) :
    ∃ slots : L ↪ B × Fin 2, ∀ l, (slots l).1 = p l := by
  classical
  have hslots (b : B) : Nonempty ({l : L // p l = b} ↪ Fin 2) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hsmall b)
  let fiberSlots (b : B) : {l : L // p l = b} ↪ Fin 2 :=
    Classical.choice (hslots b)
  let fiberMap : (Σ b : B, {l : L // p l = b}) ↪ Σ _ : B, Fin 2 :=
    Function.Embedding.sigmaMap (Function.Embedding.refl B) fiberSlots
  let slots : L ↪ B × Fin 2 :=
    (Equiv.sigmaFiberEquiv p).symm.toEmbedding.trans
      (fiberMap.trans (Equiv.sigmaEquivProd B (Fin 2)).toEmbedding)
  exact ⟨slots, fun _ => rfl⟩

theorem exists_exact_two_completion [Fintype L] [Fintype A] [Fintype B]
    [DecidableEq B] (legal : L ↪ A) (p : L → B)
    (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    ∃ pHat : A → B,
      (∀ l, pHat (legal l) = p l) ∧
      ∀ b, Fintype.card {a : A // pHat a = b} = 2 := by
  classical
  obtain ⟨slots, hslots⟩ := exists_slot_embedding p hsmall
  have hcardSlots : Fintype.card A = Fintype.card (B × Fin 2) := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]
    exact hcard
  let base : A ≃ B × Fin 2 := Fintype.equivOfCardEq hcardSlots
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun l : L => base (legal l)) (fun l : L => slots l)
    (base.injective.comp legal.injective) slots.injective
  let e : A ≃ B × Fin 2 := base.trans σ
  refine ⟨fun a => (e a).1, ?_, ?_⟩
  · intro l
    change (σ (base (legal l))).1 = p l
    rw [hσ l]
    exact hslots l
  · intro b
    exact (Fintype.card_congr (fiberEquivTwo e b)).trans (Fintype.card_fin 2)

end PerfectCompleteness.Completion



namespace PerfectCompleteness.InitialParameters

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

def epsilon (δ : ℚ) : ℝ := (δ : ℝ) / 3
def simultaneous (δ : ℚ) : ℝ := epsilon δ ^ 2 / 2
def useful (δ : ℚ) : ℝ := simultaneous δ / 2
def inverse (δ : ℚ) : ℝ := simultaneous δ ^ 2 / 32

theorem epsilon_pos {δ : ℚ} (hδ : 0 < δ) : 0 < epsilon δ := by
  have : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold epsilon
  positivity

theorem simultaneous_pos {δ : ℚ} (hδ : 0 < δ) : 0 < simultaneous δ := by
  have := epsilon_pos hδ
  unfold simultaneous
  positivity

theorem useful_pos {δ : ℚ} (hδ : 0 < δ) : 0 < useful δ := by
  have := simultaneous_pos hδ
  unfold useful
  positivity

theorem inverse_pos {δ : ℚ} (hδ : 0 < δ) : 0 < inverse δ := by
  have := simultaneous_pos hδ
  unfold inverse
  positivity

end
end PerfectCompleteness.InitialParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CompletionProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open scoped Classical

namespace PerfectCompleteness.CompletionProbability

variable {L A B : Type*}

abbrev Illegal (legal : L ↪ A) := {a : A // a ∉ Set.range legal}

def uniformProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ :=
  (Fintype.card {ω : Ω // event ω} : ℝ) / Fintype.card Ω

theorem card_illegal [Fintype L] [Fintype A] (legal : L ↪ A) :
    Fintype.card (Illegal legal) = Fintype.card A - Fintype.card L := by
  rw [Fintype.card_subtype_compl, Fintype.card_range legal]

def rotate {n : ℕ} [NeZero n] (legal : L ↪ A)
    (enum : Illegal legal ≃ Fin n) (seed : Fin n) : Equiv.Perm (Illegal legal) where
  toFun a := enum.symm (seed + enum a)
  invFun a := enum.symm (-seed + enum a)
  left_inv a := by simp [← add_assoc]
  right_inv a := by simp [← add_assoc]

def rotateAll {n : ℕ} [NeZero n] (legal : L ↪ A)
    (enum : Illegal legal ≃ Fin n) (seed : Fin n) : Equiv.Perm A :=
  (Equiv.refl {a : A // a ∈ Set.range legal}).subtypeCongr (rotate legal enum seed)

def sample {n : ℕ} [NeZero n] (legal : L ↪ A) (pHat : A → B)
    (enum : Illegal legal ≃ Fin n) (seed : Fin n) (a : A) : B :=
  pHat (rotateAll legal enum seed a)

@[simp] theorem sample_legal {n : ℕ} [NeZero n] (legal : L ↪ A)
    (pHat : A → B) (enum : Illegal legal ≃ Fin n) (seed : Fin n) (l : L) :
    sample legal pHat enum seed (legal l) = pHat (legal l) := by
  have hl : legal l ∈ Set.range legal := ⟨l, rfl⟩
  exact congrArg pHat (Equiv.Perm.subtypeCongr.left_apply
    (Equiv.refl {a : A // a ∈ Set.range legal}) (rotate legal enum seed) hl)

theorem sample_exact_two [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2) (seed : Fin n) (b : B) :
    Fintype.card {a : A // sample legal pHat enum seed a = b} = 2 := by
  exact (Fintype.card_congr ((rotateAll legal enum seed).subtypeEquivOfSubtype
    (p := fun a : A => pHat a = b))).trans (hexact b)

def seedEquiv {n : ℕ} [NeZero n] (legal : L ↪ A)
    (enum : Illegal legal ≃ Fin n) (a : Illegal legal) : Fin n ≃ Illegal legal where
  toFun seed := enum.symm (seed + enum a)
  invFun j := enum j - enum a
  left_inv seed := by simp
  right_inv j := by simp

@[simp] theorem sample_illegal {n : ℕ} [NeZero n] (legal : L ↪ A)
    (pHat : A → B) (enum : Illegal legal ≃ Fin n) (seed : Fin n) (a : Illegal legal) :
    sample legal pHat enum seed a.val = pHat ((seedEquiv legal enum a) seed).val := by
  exact congrArg pHat (Equiv.Perm.subtypeCongr.right_apply
    (Equiv.refl {a : A // a ∈ Set.range legal}) (rotate legal enum seed) a.property)

theorem sample_event_card [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (a : Illegal legal) (b : B) :
    Fintype.card {seed : Fin n // sample legal pHat enum seed a.val = b} =
      Fintype.card {j : Illegal legal // pHat j.val = b} := by
  exact Fintype.card_congr ((seedEquiv legal enum a).subtypeEquiv
    (fun seed => by simp))

theorem sample_probability [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (a : Illegal legal) (b : B) :
    uniformProbability (fun seed : Fin n => sample legal pHat enum seed a.val = b) =
      (Fintype.card {j : Illegal legal // pHat j.val = b} : ℝ) / n := by
  rw [uniformProbability, sample_event_card, Fintype.card_fin]

theorem residual_fiber_le_two [Fintype A] (legal : L ↪ A) (pHat : A → B)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2) (b : B) :
    Fintype.card {j : Illegal legal // pHat j.val = b} ≤ 2 := by
  let incl : {j : Illegal legal // pHat j.val = b} ↪ {a : A // pHat a = b} :=
    ⟨fun j => ⟨j.val.val, j.property⟩, by
      intro j k h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {a : A // pHat a = b} => z.val) h⟩
  exact (Fintype.card_le_of_embedding incl).trans (le_of_eq (hexact b))

theorem residual_fiber_card [Fintype L] [Fintype A]
    (legal : L ↪ A) (p : L → B) (pHat : A → B)
    (hext : ∀ l, pHat (legal l) = p l)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2) (b : B) :
    Fintype.card {a : Illegal legal // pHat a.val = b} =
      2 - Fintype.card {l : L // p l = b} := by
  let F := {a : A // pHat a = b}
  let P : F → Prop := fun a => a.val ∈ Set.range legal
  let eLegal : {l : L // p l = b} ≃ {a : F // P a} := by
    refine Equiv.ofBijective
      (fun l : {l : L // p l = b} =>
        (⟨⟨legal l.val, (hext l.val).trans l.property⟩,
          ⟨l.val, rfl⟩⟩ : {a : F // P a})) ⟨?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply legal.injective
      exact congrArg (fun a : {a : F // P a} => a.val.val) h
    · intro a
      obtain ⟨l, hl⟩ := (a.property : a.val.val ∈ Set.range legal)
      have hpl : p l = b :=
        (hext l).symm.trans ((congrArg pHat hl).trans a.val.property)
      refine ⟨⟨l, hpl⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hl
  let eResidual : {a : Illegal legal // pHat a.val = b} ≃ {a : F // ¬P a} := {
    toFun := fun a => ⟨⟨a.val.val, a.property⟩, a.val.property⟩
    invFun := fun a => ⟨⟨a.val.val, a.property⟩, a.val.property⟩
    left_inv := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := fun a => by
      apply Subtype.ext
      apply Subtype.ext
      rfl
  }
  have hF : Fintype.card F = 2 := hexact b
  calc
    _ = Fintype.card {a : F // ¬P a} := Fintype.card_congr eResidual
    _ = Fintype.card F - Fintype.card {a : F // P a} :=
      Fintype.card_subtype_compl P
    _ = 2 - Fintype.card {l : L // p l = b} := by
      rw [hF, ← Fintype.card_congr eLegal]

theorem sample_probability_residual [Fintype L] [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (p : L → B) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (hext : ∀ l, pHat (legal l) = p l)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2)
    (a : Illegal legal) (b : B) :
    uniformProbability (fun seed : Fin n => sample legal pHat enum seed a.val = b) =
      ((2 - Fintype.card {l : L // p l = b} : ℕ) : ℝ) /
        (Fintype.card A - Fintype.card L : ℕ) := by
  rw [sample_probability]
  have hn : n = Fintype.card A - Fintype.card L := by
    rw [← card_illegal legal]
    simpa only [Fintype.card_fin] using (Fintype.card_congr enum).symm
  rw [← hn]
  simpa only [← Nat.card_eq_fintype_card] using
    congrArg (fun k : ℕ => (k : ℝ) / (n : ℝ))
      (residual_fiber_card legal p pHat hext hexact b)

theorem sample_probability_le [Fintype L] [Fintype A] {n : ℕ} [NeZero n]
    (legal : L ↪ A) (pHat : A → B) (enum : Illegal legal ≃ Fin n)
    (hexact : ∀ b, Fintype.card {a : A // pHat a = b} = 2)
    (a : Illegal legal) (b : B) :
    uniformProbability (fun seed : Fin n => sample legal pHat enum seed a.val = b) ≤
      2 / (Fintype.card A - Fintype.card L : ℕ) := by
  have hn : n = Fintype.card A - Fintype.card L := by
    rw [← card_illegal legal]
    simpa only [Fintype.card_fin] using (Fintype.card_congr enum).symm
  rw [sample_probability, hn]
  apply div_le_div_of_nonneg_right
  · exact Nat.cast_le.mpr (residual_fiber_le_two legal pHat hexact b)
  · exact Nat.cast_nonneg _

end PerfectCompleteness.CompletionProbability

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CompletionSoundness

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionProbability

noncomputable section

def roundLabel {L A : Type*} (legal : L ↪ A) (default : L) (a : A) : L :=
  if h : ∃ l, legal l = a then Classical.choose h else default

abbrev LegalStrategy {Q₁ Q₂ : Type*} (L : Q₁ → Type*) (R : Q₂ → Type*) :=
  (∀ x, L x) × (∀ y, R y)

namespace LegalProjectionGame

variable {E Q₁ Q₂ : Type*}
  {L : Q₁ → Type*}
  {R : Q₂ → Type*}
  [Fintype E]

variable [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)]
  {A B : Type*} [Fintype A] [Fintype B]

theorem embedded_fiber_le_two {L₀ R₀ B₀ : Type*} [Fintype L₀]
    (j : R₀ ↪ B₀) (p : L₀ → R₀)
    (hsmall : ∀ r, Fintype.card {l : L₀ // p l = r} ≤ 2) (b : B₀) :
    Fintype.card {l : L₀ // j (p l) = b} ≤ 2 := by
  by_cases hb : ∃ r : R₀, j r = b
  · obtain ⟨r, rfl⟩ := hb
    let e : {l : L₀ // j (p l) = j r} ≃ {l : L₀ // p l = r} :=
      Equiv.subtypeEquivRight (fun l =>
        ⟨fun h => j.injective h, fun h => congrArg j h⟩)
    exact (Fintype.card_congr e).le.trans (hsmall r)
  · have hzero : Fintype.card {l : L₀ // j (p l) = b} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun l => hb ⟨p l.val, l.property⟩⟩
    rw [hzero]
    exact Nat.zero_le 2

end LegalProjectionGame

end
end PerfectCompleteness.CompletionSoundness

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_DomainEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DomainEncoding

open ClauseSupport ReducedDomains

variable {I C Y Z : Type*}

def retainedFields {n : Nat} (keys : Fin n → SlotKey) : List (Fin n × SlotKey) :=
  ((List.finRange n).map (fun i => (i, keys i))).filter
    (fun entry => decide (entry.2 ≠ .dropped))

theorem mem_retainedFields {n : Nat} (keys : Fin n → SlotKey) (i : Fin n)
    (key : SlotKey) :
    (i, key) ∈ retainedFields keys ↔ key = keys i ∧ key ≠ .dropped := by
  constructor
  · intro h
    obtain ⟨hm, hretained⟩ := List.mem_filter.mp h
    obtain ⟨j, _, hpair⟩ := List.mem_map.mp hm
    have hji : j = i := congrArg Prod.fst hpair
    subst j
    have hkey : keys i = key := congrArg Prod.snd hpair
    exact ⟨hkey.symm, of_decide_eq_true hretained⟩
  · rintro ⟨rfl, hretained⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨i, ?_, rfl⟩, ?_⟩
    · simp
    · exact decide_eq_true hretained

def lookupField [DecidableEq I] (fields : List (I × SlotKey)) (i : I) : SlotKey :=
  match fields with
  | [] => .dropped
  | (j, key) :: rest => if i = j then key else lookupField rest i

end PerfectCompleteness.DomainEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceStrategy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceKeys

open SourceClause ClauseSupport MixedSupport CanonicalKeys

variable {v m n : Nat} {C Y Z : Type*}

def assignmentAt (assignment : Fin v → Bool) (j : Nat) : Bool :=
  if h : j < v then assignment ⟨j, h⟩ else false

@[simp] theorem assignmentAt_fin (assignment : Fin v → Bool) (j : Fin v) :
    assignmentAt assignment j.val = assignment j := by
  simp [assignmentAt, j.isLt]

end PerfectCompleteness.SourceKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_Value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness

namespace Instance

theorem countSatisfied_le_maxSatisfied {q : Nat} (G : Instance q) (s : Labeling G) :
    countSatisfied s.1 s.2 G.edges ≤ G.maxSatisfied := by
  exact Finset.le_sup (f := fun s : Labeling G => countSatisfied s.1 s.2 G.edges)
    (Finset.mem_univ s)

theorem maxSatisfied_le_length {q : Nat} (G : Instance q) :
    G.maxSatisfied ≤ G.edges.length := by
  apply Finset.sup_le
  intro s _
  exact countSatisfied_le_length s.1 s.2 G.edges

theorem maxSatisfied_attained {q : Nat} (G : Instance q) (hq : 0 < q) :
    ∃ s : Labeling G, countSatisfied s.1 s.2 G.edges = G.maxSatisfied := by
  have hne : (Finset.univ : Finset (Labeling G)).Nonempty :=
    ⟨(fun _ => ⟨0, by omega⟩, fun _ => ⟨0, hq⟩), Finset.mem_univ _⟩
  obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun s : Labeling G => countSatisfied s.1 s.2 G.edges)
  exact ⟨s, h.symm⟩

theorem rate_le_value {q : Nat} (G : Instance q) (s : Labeling G) :
    (countSatisfied s.1 s.2 G.edges : ℝ) / G.edges.length ≤ G.value := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast G.countSatisfied_le_maxSatisfied s
  · exact Nat.cast_nonneg _

theorem perfectlyComplete_iff_value_eq_one {q : Nat} (G : Instance q) (hq : 0 < q) :
    PerfectlyComplete G ↔ G.value = 1 := by
  have hlen : (0 : ℝ) < G.edges.length := by exact_mod_cast G.edgeCount_positive
  constructor
  · rintro ⟨s, hs⟩
    have hc := (countSatisfied_eq_length_iff s.1 s.2 G.edges).2 hs
    have hm : G.maxSatisfied = G.edges.length :=
      le_antisymm G.maxSatisfied_le_length (hc ▸ G.countSatisfied_le_maxSatisfied s)
    simp [value, hm, ne_of_gt hlen]
  · intro hv
    obtain ⟨s, hs⟩ := G.maxSatisfied_attained hq
    have hm : G.maxSatisfied = G.edges.length := by
      have hreal : (G.maxSatisfied : ℝ) = G.edges.length := by
        have := (div_eq_one_iff_eq (ne_of_gt hlen)).1 hv
        exact this
      exact_mod_cast hreal
    exact ⟨s, (countSatisfied_eq_length_iff s.1 s.2 G.edges).1 (hs.trans hm)⟩

end Instance
end PerfectCompleteness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_TargetGameLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RoundedTarget

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {m l r q : Nat}

theorem countSatisfied_eq_filter (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q)
    (es : List (Edge l r q)) :
    countSatisfied a b es = (es.filter fun e => e.satisfied a b).length := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    cases h : e.satisfied a b <;> simp [countSatisfied, h, ih, Nat.add_comm]

end PerfectCompleteness.RoundedTarget

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CanonicalGameLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped Classical

namespace PerfectCompleteness.CompletionProbability

variable {L A B : Type*}

theorem exists_completion_sampler_bounded [Fintype L] [Fintype A] [Fintype B]
    (legal : L ↪ A) (p : L → B)
    (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    ∃ n : ℕ, 0 < n ∧ n ≤ max 1 (Fintype.card A - Fintype.card L) ∧
      ∃ sampler : Fin n → A → B,
        (∀ seed l, sampler seed (legal l) = p l) ∧
        (∀ seed b, Fintype.card {a : A // sampler seed a = b} = 2) ∧
        ∀ (a : Illegal legal) (b : B),
          uniformProbability (fun seed => sampler seed a.val = b) =
            ((2 - Fintype.card {l : L // p l = b} : ℕ) : ℝ) /
              (Fintype.card A - Fintype.card L : ℕ) ∧
          uniformProbability (fun seed => sampler seed a.val = b) ≤
            2 / (Fintype.card A - Fintype.card L : ℕ) := by
  obtain ⟨pHat, hext, hexact⟩ :=
    Completion.exists_exact_two_completion legal p hsmall hcard
  by_cases hz : Fintype.card (Illegal legal) = 0
  · refine ⟨1, Nat.zero_lt_one,
      le_max_left 1 (Fintype.card A - Fintype.card L), (fun _ => pHat), ?_, ?_, ?_⟩
    · intro seed l
      exact hext l
    · intro seed b
      exact hexact b
    · intro a b
      have hp : 0 < Fintype.card (Illegal legal) := Fintype.card_pos_iff.mpr ⟨a⟩
      exact False.elim (Nat.ne_of_gt hp hz)
  · let : NeZero (Fintype.card (Illegal legal)) := ⟨hz⟩
    let enum := Fintype.equivFin (Illegal legal)
    refine ⟨Fintype.card (Illegal legal), Nat.pos_of_ne_zero hz,
      (card_illegal legal).le.trans
        (le_max_right 1 (Fintype.card A - Fintype.card L)),
      sample legal pHat enum, ?_, ?_, ?_⟩
    · intro seed l
      simpa only [sample_legal] using hext l
    · intro seed b
      exact sample_exact_two legal pHat enum hexact seed b
    · intro a b
      exact ⟨sample_probability_residual legal p pHat enum hext hexact a b,
        sample_probability_le legal pHat enum hexact a b⟩

end PerfectCompleteness.CompletionProbability

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_LocalCompletionFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LocalCompletionFamily

open scoped Classical
open CompletionProbability

noncomputable section

abbrev Input (q : Nat) := (Fin (2 * q) → Bool) × (Fin (2 * q) → Fin q)

abbrev Result (q : Nat) := Fin (2 * q) × (Fin (2 * q) → Fin (2 * q) → Fin q)

abbrev Legal {q : Nat} (input : Input q) := {a : Fin (2 * q) // input.1 a = true}

def legalEmbedding {q : Nat} (input : Input q) : Legal input ↪ Fin (2 * q) :=
  ⟨Subtype.val, Subtype.val_injective⟩

def legalProjection {q : Nat} (input : Input q) (a : Legal input) : Fin q := input.2 a.val

def Admissible {q : Nat} (input : Input q) : Prop :=
  ∀ b, Fintype.card {a : Legal input // input.2 a.val = b} ≤ 2

def activeCount {q : Nat} (result : Result q) : Nat := result.1.val + 1

theorem activeCount_positive {q : Nat} (result : Result q) : 0 < activeCount result :=
  Nat.succ_pos _

theorem activeCount_le {q : Nat} (result : Result q) : activeCount result ≤ 2 * q :=
  Nat.succ_le_of_lt result.1.isLt

def table {q : Nat} (result : Result q) (seed : Fin (activeCount result)) :
    Fin (2 * q) → Fin q :=
  result.2 ⟨seed.val, lt_of_lt_of_le seed.isLt (activeCount_le result)⟩

structure Correct {q : Nat} (input : Input q) (result : Result q) : Prop where
  agrees : ∀ seed a, input.1 a = true → table result seed a = input.2 a
  exact_two : ∀ seed b, Fintype.card {a : Fin (2 * q) // table result seed a = b} = 2
  illegal_probability : ∀ a, input.1 a ≠ true → ∀ b,
    uniformProbability (fun seed : Fin (activeCount result) => table result seed a = b) ≤
      2 / (2 * q - Fintype.card (Legal input) : Nat)

def packSampler {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) : Result q :=
  (⟨n - 1, by omega⟩,
    fun slot => if h : slot.val < n then sampler ⟨slot.val, h⟩ else sampler ⟨0, hn⟩)

@[simp] theorem activeCount_packSampler {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) :
    activeCount (packSampler hn hbound sampler) = n := by
  change n - 1 + 1 = n
  omega

def packedSeedEquiv {q n : Nat} (hn : 0 < n) (hbound : n ≤ 2 * q)
    (sampler : Fin n → Fin (2 * q) → Fin q) :
    Fin (activeCount (packSampler hn hbound sampler)) ≃ Fin n where
  toFun seed := ⟨seed.val, by simpa only [activeCount_packSampler] using seed.isLt⟩
  invFun seed := ⟨seed.val, by simpa only [activeCount_packSampler] using seed.isLt⟩
  left_inv seed := Fin.ext rfl
  right_inv seed := Fin.ext rfl

theorem uniformProbability_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (equiv : Ω ≃ Γ) (event : Γ → Prop) :
    uniformProbability (fun seed => event (equiv seed)) = uniformProbability event := by
  let restricted : {seed : Ω // event (equiv seed)} ≃ {seed : Γ // event seed} :=
    equiv.subtypeEquiv (fun _ => Iff.rfl)
  unfold uniformProbability
  rw [Fintype.card_congr restricted, Fintype.card_congr equiv]

def fallback {q : Nat} (hq : 0 < q) : Result q :=
  (⟨0, Nat.mul_pos (by decide) hq⟩, fun _ _ => ⟨0, hq⟩)

end
end PerfectCompleteness.LocalCompletionFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DependentPredictionDifference

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

variable {O : Type*}

abbrev Sample (Ω A : O → Type*) := (o : O) × (Ω o × A o)

abbrev Observation (P A : O → Type*) := (o : O) × (P o × A o)

variable [Fintype O] {Ω P A : O → Type*}
  [∀ o, Fintype (Ω o)] [∀ o, Fintype (P o)] [∀ o, Fintype (A o)]

def observe (p : ∀ o, Ω o → P o) (x : Sample Ω A) : Observation P A :=
  ⟨x.1, (p x.1 x.2.1, x.2.2)⟩

end
end PerfectCompleteness.DependentPredictionDifference


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_FactoredFunctionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.FactoredFunctionsDependent

variable {𝕜 Ω I : Type*} [Field 𝕜] {J : I → Type*}

def dependentQuadraticSpan (lower : Ω → (i : I) → J i → 𝕜) :
    Submodule 𝕜 (Ω → 𝕜) :=
  Submodule.span 𝕜 {f | f = 1 ∨
    ∃ (i : I) (t u : J i), f = fun x => lower x i t * lower x i u}

end PerfectCompleteness.FactoredFunctionsDependent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_DescendantSpacesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DescendantSpaces

universe u w

inductive Path (branch : Nat → Nat) : Nat → Nat → Type
  | refl (n : Nat) : Path branch n n
  | step {n m : Nat} (i : Fin (branch n)) (tail : Path branch n m) :
      Path branch (n + 1) m

end PerfectCompleteness.DescendantSpaces



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalArrays

open TreeSourceSpaces

def Nodes (branch : Nat → Nat) : Nat → Type
  | 0 => Empty
  | n + 1 => Unit ⊕ (Fin (branch n) × Nodes branch n)

instance nodesFintype (branch : Nat → Nat) (n : Nat) : Fintype (Nodes branch n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ n ih =>
      letI : Fintype (Nodes branch n) := ih
      exact inferInstanceAs (Fintype (Unit ⊕ (Fin (branch n) × Nodes branch n)))

instance nodesDecidableEq (branch : Nat → Nat) (n : Nat) :
    DecidableEq (Nodes branch n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ n ih =>
      letI : DecidableEq (Nodes branch n) := ih
      exact inferInstanceAs (DecidableEq (Unit ⊕ (Fin (branch n) × Nodes branch n)))

namespace Nodes

variable {branch : Nat → Nat}

def height : {n : Nat} → Nodes branch n → Nat
  | 0, node => nomatch node
  | n + 1, .inl _ => n + 1
  | _ + 1, .inr (_, node) => height node

end Nodes

end PerfectCompleteness.HierarchicalArrays

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_EncodingLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.ProjectionTable.ofMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.Encoding

open UniqueGamesTheorem.Foundations.Complexity

@[simp] theorem tableWords_length {q : Nat} (table : ProjectionTable q) :
    (tableWords table).length = 2 * q := by
  simp [tableWords]

@[simp] theorem edgeWords_length {l r q : Nat} (edge : Edge l r q) :
    (edgeWords edge).length = 2 * q + 2 := by
  simp [edgeWords]

theorem edgesWords_length {l r q : Nat} (edges : List (Edge l r q)) :
    (edges.flatMap edgeWords).length = edges.length * (2 * q + 2) := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      simp only [List.flatMap_cons, List.length_append, edgeWords_length,
        List.length_cons, Nat.add_mul, Nat.one_mul, ih]
      omega

@[simp] theorem gameWords_length {q : Nat} (game : Instance q) :
    (gameWords game).length = 4 + game.edges.length * (2 * q + 2) := by
  simp only [gameWords, List.length_append, List.length_cons, List.length_nil,
    edgesWords_length]

end PerfectCompleteness.Encoding


namespace PerfectCompleteness.Encoding

theorem tableWords_sum_le {q : Nat} (table : ProjectionTable q) :
    (tableWords table).sum ≤ 2 * q * q := by
  have hsum (labels : List (Fin q)) :
      (labels.map Fin.val).sum ≤ labels.length * q := by
    induction labels with
    | nil => simp
    | cons a labels ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.add_mul, Nat.one_mul]
        calc
          _ ≤ q + labels.length * q :=
            Nat.add_le_add (Nat.le_of_lt a.isLt) ih
          _ = labels.length * q + q := Nat.add_comm _ _
  simpa [tableWords] using hsum table.images.toList

theorem edgeWords_sum_le {l r q : Nat} (edge : Edge l r q) :
    (edgeWords edge).sum ≤ l + r + 2 * q * q := by
  calc
    _ = edge.left.val + edge.right.val + (tableWords edge.projection).sum := by
      simp [edgeWords, Nat.add_assoc]
    _ ≤ l + r + 2 * q * q :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.le_of_lt edge.left.isLt) (Nat.le_of_lt edge.right.isLt))
        (tableWords_sum_le edge.projection)

theorem edgesWords_sum_le {l r q : Nat} (edges : List (Edge l r q)) :
    (edges.flatMap edgeWords).sum ≤ edges.length * (l + r + 2 * q * q) := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      calc
        _ = (edgeWords edge).sum + (edges.flatMap edgeWords).sum := by
          rw [List.flatMap_cons, List.sum_append]
        _ ≤ (l + r + 2 * q * q) + edges.length * (l + r + 2 * q * q) :=
          Nat.add_le_add (edgeWords_sum_le edge) ih
        _ = (edge :: edges).length * (l + r + 2 * q * q) := by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _

theorem gameWords_sum_le {q : Nat} (game : Instance q) :
    (gameWords game).sum ≤
      game.leftVertices + game.rightVertices + q + game.edges.length +
        game.edges.length * (game.leftVertices + game.rightVertices + 2 * q * q) := by
  calc
    _ = (game.leftVertices + game.rightVertices + q + game.edges.length) +
        (game.edges.flatMap edgeWords).sum := by
      simp [gameWords, Nat.add_assoc]
    _ ≤ _ := Nat.add_le_add_left (edgesWords_sum_le game.edges) _

end PerfectCompleteness.Encoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CompletionParameters

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness

noncomputable section

theorem residual_le_third {q n : Nat} {δ : ℝ} (hq : 0 < q)
    (hn : n ≤ q) (hδ : 0 < δ) (hbudget : 6 ≤ δ * q) :
    2 / (2 * q - n : Nat) ≤ δ / 3 := by
  have hden : q ≤ 2 * q - n := by omega
  have hden_real : (q : ℝ) ≤ (2 * q - n : Nat) := by exact_mod_cast hden
  have hpos : (0 : ℝ) < (2 * q - n : Nat) := by
    exact_mod_cast lt_of_lt_of_le hq hden
  rw [div_le_iff₀ hpos]
  have hmul := mul_le_mul_of_nonneg_left hden_real (le_of_lt hδ)
  nlinarith

end
end PerfectCompleteness.CompletionParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletionAlphabetLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CompletionAlphabet

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionParameters

def size (cap : Nat) (δ : ℚ) : Nat := max (cap + 1) ⌈(6 : ℚ) / δ⌉₊

theorem size_positive (cap : Nat) (δ : ℚ) : 0 < size cap δ := by
  have h : cap + 1 ≤ size cap δ := le_max_left _ _
  omega

theorem cap_le_size (cap : Nat) (δ : ℚ) : cap ≤ size cap δ :=
  (Nat.le_succ cap).trans (le_max_left _ _)

theorem size_budget (cap : Nat) (δ : ℚ) (hδ : 0 < δ) :
    (6 : ℝ) ≤ (δ : ℝ) * size cap δ := by
  have hceil : (6 : ℚ) / δ ≤ (⌈(6 : ℚ) / δ⌉₊ : ℚ) := Nat.le_ceil _
  have hsize : (⌈(6 : ℚ) / δ⌉₊ : ℚ) ≤ (size cap δ : ℚ) := by
    exact_mod_cast (le_max_right (cap + 1) ⌈(6 : ℚ) / δ⌉₊)
  have hprod : (6 : ℚ) ≤ δ * size cap δ := by
    have h := (div_le_iff₀ hδ).1 (hceil.trans hsize)
    simpa only [mul_comm] using h
  exact_mod_cast hprod

end PerfectCompleteness.CompletionAlphabet


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CleanConditioning

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def allEvent (event : (i : I) → Ω i → Bool) (x : (i : I) → Ω i) : Bool :=
  decide (∀ i, event i (x i) = true)

end Product


end
end PerfectCompleteness.CleanConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FiniteBlockMachineLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.KeyMetadataEncoding

open ClauseSupport

variable {n : Nat}

def bitWord (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem bitWord_eq_iff (a b : Bool) : bitWord a = bitWord b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bitWord_le (b : Bool) : bitWord b ≤ 1 := by
  cases b <;> decide

def entryID : SlotKey → Nat
  | .dropped => 0
  | .bit variableID => variableID
  | .full occurrence _ => occurrence

def entryWords (entry : Fin n × SlotKey) : List Nat :=
  entry.1.val :: match entry.2 with
    | .dropped => [0, 0, 0, 0, 0]
    | .bit variableID => [1, variableID, 0, 0, 0]
    | .full occurrence signs =>
        [2, occurrence, bitWord signs.1, bitWord signs.2.1, bitWord signs.2.2]

@[simp] theorem entryWords_length (entry : Fin n × SlotKey) :
    (entryWords entry).length = 6 := by
  rcases entry with ⟨position, key⟩
  cases key <;> rfl

theorem entryWords_injective (n : Nat) :
    Function.Injective (entryWords (n := n)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := Fin.ext (List.cons.inj h).1
  subst j
  apply congrArg (Prod.mk i)
  cases a <;> cases b <;> simp_all [entryWords, Prod.ext_iff]

def metadataWords (entries : List (Fin n × SlotKey)) : List Nat :=
  entries.flatMap entryWords

@[simp] theorem metadataWords_nil : metadataWords ([] : List (Fin n × SlotKey)) = [] := rfl

@[simp] theorem metadataWords_cons (entry : Fin n × SlotKey)
    (entries : List (Fin n × SlotKey)) :
    metadataWords (entry :: entries) = entryWords entry ++ metadataWords entries := rfl

@[simp] theorem metadataWords_length (entries : List (Fin n × SlotKey)) :
    (metadataWords entries).length = 6 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rw [metadataWords_cons, List.length_append, entryWords_length, ih,
        List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem metadataWords_injective (n : Nat) :
    Function.Injective (metadataWords (n := n)) := by
  intro entries
  induction entries with
  | nil =>
      intro other h
      have hlength := congrArg List.length h
      simp only [metadataWords_length, List.length_nil] at hlength
      have hz : other.length = 0 := by omega
      cases other with
      | nil => rfl
      | cons entry entries => simp at hz
  | cons entry entries ih =>
      intro other h
      cases other with
      | nil =>
          have hlength := congrArg List.length h
          simp only [metadataWords_length, List.length_cons, List.length_nil] at hlength
          omega
      | cons next rest =>
          have hblocks : entryWords entry ++ metadataWords entries =
              entryWords next ++ metadataWords rest := h
          obtain ⟨hhead, htail⟩ := List.append_inj hblocks
            ((entryWords_length entry).trans (entryWords_length next).symm)
          exact congrArg₂ List.cons (entryWords_injective n hhead) (ih htail)

theorem entryWords_le (entry : Fin n × SlotKey) (M : Nat)
    (hID : entryID entry.2 ≤ M) :
    ∀ word ∈ entryWords entry, word ≤ max n (max M 2) := by
  rcases entry with ⟨position, key⟩
  have hn : n ≤ max n (max M 2) := le_max_left _ _
  have hM : M ≤ max n (max M 2) := (le_max_left M 2).trans (le_max_right n _)
  have htwo : 2 ≤ max n (max M 2) := (le_max_right M 2).trans (le_max_right n _)
  have hposition := position.isLt
  intro word hw
  cases key with
  | dropped =>
      simp only [entryWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | bit variableID =>
      change variableID ≤ M at hID
      simp only [entryWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | full occurrence signs =>
      change occurrence ≤ M at hID
      have hs₀ := bitWord_le signs.1
      have hs₁ := bitWord_le signs.2.1
      have hs₂ := bitWord_le signs.2.2
      simp only [entryWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem metadataWords_le (entries : List (Fin n × SlotKey)) (M : Nat)
    (hIDs : ∀ entry ∈ entries, entryID entry.2 ≤ M) :
    ∀ word ∈ metadataWords entries, word ≤ max n (max M 2) := by
  intro word hw
  obtain ⟨entry, hentry, hword⟩ := List.mem_flatMap.mp hw
  exact entryWords_le entry M (hIDs entry hentry) word hword

end PerfectCompleteness.KeyMetadataEncoding


namespace PerfectCompleteness.CanonicalKeyEncoding

open ClauseSupport CanonicalKeys
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

def reducedValueEquiv : ReducedValue ≃ Option (Bool ⊕ SourceClause.Triple) where
  toFun
    | .dropped => none
    | .bit b => some (.inl b)
    | .full triple => some (.inr triple)
  invFun
    | none => .dropped
    | some (.inl b) => .bit b
    | some (.inr triple) => .full triple
  left_inv value := by cases value <;> rfl
  right_inv value := by
    cases value with
    | none => rfl
    | some value => cases value <;> rfl

local instance instFintypeReducedValue : Fintype ReducedValue := Fintype.ofEquiv _ reducedValueEquiv.symm

theorem reducedValue_card : Fintype.card ReducedValue = 11 := by
  rw [Fintype.card_congr reducedValueEquiv]
  simp [SourceClause.Triple]

abbrev Assignment (n : Nat) := Fin n → ReducedValue

def partitionWidth (n : Nat) : Nat := Fintype.card (Set (Assignment n))

theorem partitionWidth_eq (n : Nat) : partitionWidth n = 2 ^ (11 ^ n) := by
  simp only [partitionWidth, Fintype.card_set, Assignment, Fintype.card_fun,
    reducedValue_card, Fintype.card_fin]

def partEnum (n : Nat) : Set (Assignment n) ≃ Fin (partitionWidth n) :=
  Fintype.equivFin _

def partitionMask {n : Nat} (partition : Set (Set (Assignment n))) :
    Fin (partitionWidth n) → Bool :=
  fun i => decide ((partEnum n).symm i ∈ partition)

def partitionOfMask {n : Nat} (mask : Fin (partitionWidth n) → Bool) :
    Set (Set (Assignment n)) := {part | mask (partEnum n part) = true}

@[simp] theorem partitionOfMask_partitionMask {n : Nat}
    (partition : Set (Set (Assignment n))) :
    partitionOfMask (partitionMask partition) = partition := by
  ext part
  simp [partitionOfMask, partitionMask]

theorem partitionMask_injective (n : Nat) : Function.Injective (partitionMask (n := n)) := by
  intro a b h
  have hdecoded := congrArg partitionOfMask h
  simpa only [partitionOfMask_partitionMask] using hdecoded

def boolWord (b : Bool) : Nat := if b then 1 else 0

theorem boolWord_injective : Function.Injective boolWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolWord]

theorem boolWord_le_one (b : Bool) : boolWord b ≤ 1 := by
  cases b <;> decide

def partitionWords {n : Nat} (partition : Set (Set (Assignment n))) : List Nat :=
  List.ofFn (fun i => boolWord (partitionMask partition i))

@[simp] theorem partitionWords_length {n : Nat} (partition : Set (Set (Assignment n))) :
    (partitionWords partition).length = partitionWidth n := List.length_ofFn

theorem partitionWords_injective (n : Nat) :
    Function.Injective (partitionWords (n := n)) := by
  intro a b h
  apply partitionMask_injective n
  have hfun := List.ofFn_injective h
  funext i
  exact boolWord_injective (congrFun hfun i)

def sideWord : Side → Nat
  | .left => 0
  | .right => 1

theorem sideWord_injective : Function.Injective sideWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [sideWord]

def words {n : Nat} (key : Key n) : List Nat :=
  sideWord key.side ::
    (partitionWords key.partition ++ KeyMetadataEncoding.metadataWords key.retained)

theorem words_length {n : Nat} (key : Key n) :
    (words key).length = 1 + partitionWidth n + 6 * key.retained.length := by
  simp only [words, List.length_cons, List.length_append, partitionWords_length,
    KeyMetadataEncoding.metadataWords_length]
  omega

theorem words_injective (n : Nat) : Function.Injective (words (n := n)) := by
  intro a b h
  have hfields := List.cons.inj h
  have hlen : (partitionWords a.partition).length = (partitionWords b.partition).length := by
    simp only [partitionWords_length]
  have hside := sideWord_injective hfields.1
  have hpart := partitionWords_injective n (List.append_inj_left hfields.2 hlen)
  have hmeta := KeyMetadataEncoding.metadataWords_injective n
    (List.append_inj_right hfields.2 hlen)
  cases a
  cases b
  cases hside
  cases hpart
  cases hmeta
  rfl

end
end PerfectCompleteness.CanonicalKeyEncoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalLabelEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalLabelEncoding

open CanonicalKeys CanonicalKeyEncoding
open scoped Classical

noncomputable section

def labelIndex {n : Nat} (key : Key n) : KeyLabel key ↪ Fin (partitionWidth n) where
  toFun label := partEnum n label.val
  inj' := by
    intro a b h
    exact Subtype.ext ((partEnum n).injective h)

def labelEmbedding {n q : Nat} (key : Key n) (large : partitionWidth n ≤ q) :
    KeyLabel key ↪ Fin q :=
  (labelIndex key).trans (Fin.castLEEmb large)

@[simp] theorem labelEmbedding_val {n q : Nat} (key : Key n)
    (large : partitionWidth n ≤ q) (label : KeyLabel key) :
    (labelEmbedding key large label).val = (partEnum n label.val).val := rfl

def paddedMask {n q : Nat} (key : Key n) (a : Fin q) : Bool :=
  if h : a.val < partitionWidth n then partitionMask key.partition ⟨a.val, h⟩ else false

theorem label_card_le {n : Nat} (key : Key n) [Fintype (KeyLabel key)] :
    Fintype.card (KeyLabel key) ≤ partitionWidth n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (labelIndex key)
    (labelIndex key).injective

end
end PerfectCompleteness.CanonicalLabelEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LocalCompletionMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LocalCompletionSerialization

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open LocalCompletionFamily

noncomputable section

def projection {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) (seed : Fin (activeCount result)) : ProjectionTable q :=
  ProjectionTable.ofMap (table result seed) (by
    intro b
    simpa only [← Nat.card_eq_fintype_card] using correct.exact_two seed b)

@[simp] theorem projection_apply {q : Nat} {input : Input q} {result : Result q}
    (correct : Correct input result) (seed : Fin (activeCount result)) (a : Fin (2 * q)) :
    (projection correct seed).images[a] = table result seed a := by
  exact ProjectionTable.ofMap_apply (table result seed) _ a

end
end PerfectCompleteness.LocalCompletionSerialization

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CanonicalLocalCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalLocalCompletion

open scoped Classical
open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Games
open SourceClause CanonicalKeys CanonicalKeyEncoding CanonicalLabelEncoding
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

def alphabet (n : Nat) (δ : ℚ) : Nat := CompletionAlphabet.size (partitionWidth n) δ

theorem alphabet_positive (n : Nat) (δ : ℚ) : 0 < alphabet n δ :=
  CompletionAlphabet.size_positive (partitionWidth n) δ

theorem partitionWidth_le_alphabet (n : Nat) (δ : ℚ) : partitionWidth n ≤ alphabet n δ :=
  CompletionAlphabet.cap_le_size (partitionWidth n) δ

theorem partitionWidth_le_leftAlphabet (n : Nat) (δ : ℚ) :
    partitionWidth n ≤ 2 * alphabet n δ := by
  have h := partitionWidth_le_alphabet n δ
  omega

theorem alphabet_ge_two (n : Nat) (δ : ℚ) : 2 ≤ alphabet n δ := by
  have hpos : 0 < partitionWidth n := by
    rw [partitionWidth_eq]
    exact pow_pos (by decide) _
  have hcap : partitionWidth n + 1 ≤ alphabet n δ := le_max_left _ _
  omega

end
end PerfectCompleteness.CanonicalLocalCompletion

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformLatent

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CleanConditioning

noncomputable section


variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq J]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

abbrev Raw := Σ s : S, (j : J) → Ω s j

variable [∀ s j, DecidableEq (Ω s j)]

def zeroEvent (zero : (s : S) → (j : J) → Ω s j) (x : Raw Ω) : Bool :=
  decide (∀ j, x.2 j = zero x.1 j)


variable {D : Type*} [Fintype D]

def projectedZero (zero : (s : S) → (j : J) → Ω s j) : Sum D (Raw Ω) → Bool
  | Sum.inl _ => false
  | Sum.inr x => zeroEvent Ω zero x


end
end PerfectCompleteness.UniformLatent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutChildGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutChildGrouping

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end PerfectCompleteness.CutChildGrouping

end

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

abbrev OddList (s : Nat) (A : Type*) :=
  {L : Finset A // Odd L.card ∧ L.card ≤ s}

namespace OddList

theorem odd (L : OddList s A) : Odd L.val.card := L.property.1

theorem card_le (L : OddList s A) : L.val.card ≤ s := L.property.2

def singleton (positive : 0 < s) (a : A) : OddList s A :=
  ⟨{a}, by
    simp only [Finset.card_singleton]
    exact ⟨odd_one, Nat.succ_le_of_lt positive⟩⟩

@[simp] theorem singleton_val (positive : 0 < s) (a : A) :
    (singleton positive a).val = {a} := rfl

end OddList

section Parity

variable [Fintype B] [DecidableEq B]

def parityPushforward (π : A → B) (L : Finset A) : Finset B :=
  Finset.univ.filter fun b => Odd ((L.filter fun a => π a = b).card)

@[simp] theorem mem_parityPushforward (π : A → B) (L : Finset A) (b : B) :
    b ∈ parityPushforward π L ↔ Odd ((L.filter fun a => π a = b).card) := by
  simp only [parityPushforward, Finset.mem_filter, Finset.mem_univ, true_and]

theorem parityPushforward_preimage (π : A → B) (L : Finset A) (b : B)
    (member : b ∈ parityPushforward π L) : ∃ a ∈ L, π a = b := by
  have hodd := (mem_parityPushforward π L b).mp member
  have hpos : 0 < (L.filter fun a => π a = b).card := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at hodd
    exact Nat.not_odd_zero hodd
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩

theorem parityPushforward_subset_image (π : A → B) (L : Finset A) :
    parityPushforward π L ⊆ L.image π := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := parityPushforward_preimage π L b hb
  exact Finset.mem_image.mpr ⟨a, ha, hab⟩

theorem parityPushforward_card_le (π : A → B) (L : Finset A) :
    (parityPushforward π L).card ≤ L.card :=
  (Finset.card_le_card (parityPushforward_subset_image π L)).trans Finset.card_image_le

theorem sum_fiber_card (π : A → B) (L : Finset A) :
    (∑ b : B, (L.filter fun a => π a = b).card) = L.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter L Finset.univ π

end Parity

section Supports

variable [Fintype A]

def support (f : A → ZMod 2) : Finset A :=
  Finset.univ.filter fun a => f a = 1

end Supports

end PerfectCompleteness.OddLists

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddListExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddListExtraction

open scoped BigOperators Classical

abbrev F2 := ZMod 2

variable {X Y A B : Type*}

noncomputable def indicator (q : X → A) (a : A) : X → F2 :=
  fun x => if q x = a then 1 else 0

@[simp] theorem indicator_mul_self (q : X → A) (a : A) :
    indicator q a * indicator q a = indicator q a := by
  classical
  funext x
  by_cases h : q x = a <;> simp [indicator, h]

@[simp] theorem sum_indicator [Fintype A] (q : X → A) :
    ∑ a, indicator q a = (1 : X → F2) := by
  classical
  funext x
  simp [indicator, Finset.sum_apply]

end PerfectCompleteness.OddListExtraction

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

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

abbrev LeftLabels (t : Nat) := Fin t → Fin 7
abbrev RightLabels (t : Nat) := Fin t → Bool

end
end PerfectCompleteness.SourceOddLists



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceLocalOddLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceLocalOddLists

open scoped Classical
open TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end PerfectCompleteness.SourceLocalOddLists

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceQuestionReconstruction

open SourceClause SourceKeys

noncomputable section

variable {I E Q : Type*} {Leaf : I → Type*}
  (designated : (i : I) → Leaf i) (clean : I → Prop) [DecidablePred clean]
  [∀ i, DecidableEq (Leaf i)]

abbrev Visible := (i : I) → {s : Leaf i // ¬(clean i ∧ s = designated i)} → E

def reveal (x : (i : I) → Leaf i → E) : Visible (E := E) designated clean :=
  fun i s => x i s.1

def reconstruct (endpoint : I → E → Q)
    (visible : Visible (E := E) designated clean) (own : {i : I // clean i} → Q) :
    (i : I) → Leaf i → Q :=
  fun i s => if h : clean i ∧ s = designated i then own ⟨i, h.1⟩
    else endpoint i (visible i ⟨s, h⟩)

theorem reconstruct_eq (endpoint : I → E → Q) (x : (i : I) → Leaf i → E) :
    reconstruct designated clean endpoint (reveal designated clean x)
      (fun i => endpoint i.1 (x i.1 (designated i.1))) =
        fun i s => endpoint i (x i s) := by
  funext i s
  by_cases h : clean i ∧ s = designated i
  · simp [reconstruct, h]
  · simp [reconstruct, reveal, h]


variable {v m t : Nat}

abbrev SourceTuple (m t : Nat) := Fin t → Occurrence m

def leftTuple (e : SourceTuple m t) : Fin t → Endpoint v m :=
  fun k => .clause (e k).1

def reconstructLeft
    (visible : Visible (E := SourceTuple m t) designated clean)
    (own : {i : I // clean i} → Fin t → Fin m) :
    (i : I) → Leaf i → Fin t → Endpoint v m :=
  reconstruct designated clean (fun _ => leftTuple) visible
    (fun i k => .clause (own i k))

theorem reconstructLeft_eq (x : (i : I) → Leaf i → SourceTuple m t) :
    reconstructLeft designated clean (reveal designated clean x)
      (fun i k => (x i.1 (designated i.1) k).1) =
        fun i s => leftTuple (v := v) (x i s) := by
  exact reconstruct_eq designated clean (fun _ => leftTuple) x

end
end PerfectCompleteness.SourceQuestionReconstruction

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineUnaryAddAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt

end

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

section Order

omit [DecidableEq K]

open scoped BigOperators

def tupleOrder (n q : ℕ) : List (Fin q → Fin n) :=
  List.ofFn (finFunctionFinEquiv (m := n) (n := q)).symm

theorem tupleOrder_length (n q : ℕ) : (tupleOrder n q).length = n ^ q := by
  simp [tupleOrder]

end Order

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TupleEnumerationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TupleEnumerationMachine

open Turing UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators


variable {width : Nat} {Extra : Type} [DecidableEq Extra]

def setDigit (digits : Fin width → Nat) (depth value : Nat) : Fin width → Nat :=
  fun i => if i.val = depth then value else digits i

@[simp] theorem setDigit_self (digits : Fin width → Nat) (i : Fin width) (value : Nat) :
    setDigit digits i.val value i = value := by simp [setDigit]

def prependBlocks (blocks : Nat → List Bool) : Nat → List Bool
  | 0 => []
  | count + 1 => blocks count ++ prependBlocks blocks count

end PerfectCompleteness.TupleEnumerationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DependentDecoderSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DependentDecoderSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Q₁ Q₂ E : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype E]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {A : Q₁ → Type*} {B : Q₂ → Type*}
  [∀ q, Fintype (A q)] [∀ q, Fintype (B q)]

abbrev Seed (A : Q₁ → Type*) (B : Q₂ → Type*) :=
  ((q : Q₁) → A q) × ((q : Q₂) → B q)

end
end PerfectCompleteness.DependentDecoderSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSampler

open DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev OffPath (i : Fin (branch n)) := {j : Fin (branch n) // j ≠ i}

end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketSampler

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

abbrev F2 := ZMod 2

abbrev Direction (ℓ : Nat) := {v : Fin ℓ → F2 // v ≠ 0}

abbrev Tape (ℓ : Nat) (Ω : Type*) := Direction ℓ → Ω

variable {Ω H : Type*} [AddCommGroup H] [Module F2 H]

def rankOne {ℓ : Nat} (v : Fin ℓ → F2) (h : H) : Fin ℓ → H :=
  fun i => v i • h

def evaluate (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω) : Fin ℓ → H :=
  fun i => ∑ v : Direction ℓ, v.val i • eval (t v)

instance directionZero_isEmpty : IsEmpty (Direction 0) where
  false v := v.property (funext fun i => Fin.elim0 i)

@[simp] theorem evaluate_zero_width (eval : Ω → H) (t : Tape 0 Ω) :
    evaluate 0 eval t = 0 := by
  funext i
  exact Fin.elim0 i


open DescendantSpaces

universe u

end
end PerfectCompleteness.BucketSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderTableCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DecoderTableCoupling

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]

def definedEqual (a b : Option A) : Bool :=
  decide (∃ value, a = some value ∧ b = some value)

omit [Fintype A] in
@[simp] theorem definedEqual_none_left (a : Option A) : definedEqual none a = false := by
  simp [definedEqual]

omit [Fintype A] in
@[simp] theorem definedEqual_none_right (a : Option A) : definedEqual a none = false := by
  simp [definedEqual]

omit [Fintype A] in
@[simp] theorem definedEqual_self (a : Option A) : definedEqual a a = a.isSome := by
  cases a <;> simp [definedEqual]

omit [Fintype Q] [DecidableEq Q] [Fintype A] in
@[simp] theorem definedEqual_collision (f : Q → Option A) (q r : Q) :
    definedEqual (f q) (f r) = TwoResponseCollision.collision f (q, r) := rfl

end
end PerfectCompleteness.DecoderTableCoupling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.MarkedKernelProduct

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

def markEquiv {I : Type*} {Ω : I → Type*} :
    ((i : I) → Bool × Ω i) ≃ (I → Bool) × ((i : I) → Ω i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

end
end PerfectCompleteness.MarkedKernelProduct


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanCountingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CleanCounting

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CleanConditioning

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def cleanCount (clean : (i : I) → Ω i → Bool) (x : (i : I) → Ω i) : Nat :=
  (Finset.univ.filter fun i => clean i (x i) = true).card


end
end PerfectCompleteness.CleanCounting


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DesignatedLeavesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DesignatedLeaves

open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat}
  {height : Nat}
  (clean : Fin (branch height) → Prop)

abbrev Children := {i : Fin (branch height) // clean i}


end
end PerfectCompleteness.DesignatedLeaves



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SelectedSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CleanConditioning

noncomputable section

section Records

variable {E R T : Type*}

def childObservation (clean : E → R → T → Bool) (x : E × (R × T)) :
    Sum (E × (R × T)) R :=
  if clean x.1 x.2.1 x.2.2 then Sum.inr x.2.1 else Sum.inl x

end Records


end
end PerfectCompleteness.SelectedSources



namespace PerfectCompleteness.FiniteProductSplit

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

abbrev Others (i : I) := (j : {j : I // j ≠ i}) → Ω j.val

end
end PerfectCompleteness.FiniteProductSplit

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.UniformCleanSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CleanConditioning SelectedSources UniformLatent

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

abbrev ChildRaw (i : I) := Sum (D i) (UniformLatent.Raw (Ω i))

def childClean (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (i : I) (_ : E i) (_ : R i) : ChildRaw (D := D) Ω i → Bool :=
  projectedZero (Ω i) (zero i)

abbrev Record (i : I) := Sum (E i × (R i × ChildRaw (D := D) Ω i)) (R i)

def cleanRecord {i : I} : Record (D := D) Ω i → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

def rowEvent
    (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (record : (i : I) → Record (D := D) Ω i)
    (i : I) (x : E i × (R i × ChildRaw (D := D) Ω i)) : Bool := by
  classical
  exact decide (childObservation (childClean (D := D) Ω zero i) x = record i)

def recordEvent
    (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (record : (i : I) → Record (D := D) Ω i) :
    ((i : I) → E i × (R i × ChildRaw (D := D) Ω i)) → Bool :=
  allEvent (rowEvent Ω zero record)

end
end PerfectCompleteness.UniformCleanSources



namespace PerfectCompleteness.CleanSourceRecord

open scoped Classical
open SourceQuestionReconstruction

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Leaf : I → Type*} [∀ i, Fintype (Leaf i)] [∀ i, DecidableEq (Leaf i)]
  (designated : (i : I) → Leaf i) {m t : Nat}

abbrev Rest (i : I) := {leaf : Leaf i // leaf ≠ designated i} → SourceTuple m t

end
end PerfectCompleteness.CleanSourceRecord



namespace PerfectCompleteness.UniformCleanSoundness

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CleanConditioning SelectedSources UniformLatent UniformCleanSources

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  {R J D : I → Type*}
  [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

abbrev FullRecord := (i : I) → Record (D := D) Ω i

end
end PerfectCompleteness.UniformCleanSoundness



namespace PerfectCompleteness.ProjectedCleanRate

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniformCleanSources

noncomputable section

def projectionDensity (cube : Nat) : ℝ := 1 / (cube : ℝ) ^ 2

theorem projectionDensity_bounds {cube : Nat} (hcube : 0 < cube) :
    0 ≤ projectionDensity cube ∧ projectionDensity cube ≤ 1 := by
  have hc : (1 : ℝ) ≤ cube := by exact_mod_cast hcube
  have hsq : (1 : ℝ) ≤ (cube : ℝ) ^ 2 := by nlinarith
  constructor
  · exact one_div_nonneg.mpr (sq_nonneg _)
  · exact (div_le_one (by positivity)).2 hsq

end
end PerfectCompleteness.ProjectedCleanRate

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketUniformLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSampler

open DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

abbrev CallIndex (repeats : Nat → Nat) (n : Nat) := Fin (repeats (n + 1)) × Bool

end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatentSupportLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.NativeTaggedUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

abbrev Raw {S : Type*} (Native : S → Type*) := Σ s, Native s

end
end PerfectCompleteness.NativeTaggedUniform



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeCutSampler
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

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutSampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutGrouping

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

section Rearrangement

variable {V C T I E F O : Type*} {D A : I → Type*}

def regroupStep :
    ((V → ((C → (i : I) → D i) × E)) ×
      ((F × ((i : I) → (T → D i) × A i)) × O)) ≃
    (((V → E) × (F × O)) × ((i : I) → ((V × C ⊕ T) → D i) × A i)) where
  toFun x :=
    ((fun v => (x.1 v).2, (x.2.1.1, x.2.2)),
      fun i =>
        (fun q => match q with
          | .inl vc => (x.1 vc.1).1 vc.2 i
          | .inr t => (x.2.1.2 i).1 t,
         (x.2.1.2 i).2))
  invFun x :=
    ((fun v => (fun c i => (x.2 i).1 (.inl (v, c)), x.1.1 v)),
      ((x.1.2.1, fun i => (fun t => (x.2 i).1 (.inr t), (x.2 i).2)), x.1.2.2))
  left_inv x := rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      apply Prod.ext
      · funext q
        cases q <;> rfl
      · rfl

end Rearrangement

end
end PerfectCompleteness.WholeCutGrouping

end

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

namespace PerfectCompleteness.WholeCutExteriorTransport

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutExteriorTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutReplay

end

section

namespace PerfectCompleteness.WholeCutReplayGrouping

open DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeCutReplayGrouping

end

section

namespace PerfectCompleteness.WholeCutReplayTransport

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open scoped BigOperators Classical

noncomputable section

abbrev F2 := ZMod 2

end
end PerfectCompleteness.WholeCutReplayTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ManyGoodRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.ProductEvaluation

open MixedSupport CanonicalKeys

abbrev F2 := ZMod 2

variable {X C Z : Type*} {Row : C → Type*}

def displayedJoint (rows : (c : C) → Row c → X → F2) (other : X → Z) (x : X) :
    ((c : C) → Row c → F2) × Z :=
  ((fun c u => rows c u x), other x)

end PerfectCompleteness.ProductEvaluation

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LeftDecoder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LeftDecoder

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open ClauseSupport MixedSupport

abbrev F2 := ZMod 2

noncomputable section

section Affine

variable {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]

local instance dualFintype : Fintype (Module.Dual F2 V) :=
  Fintype.ofEquiv (Fin (Module.finrank F2 (Module.Dual F2 V)) → F2)
    (Module.finBasis F2 (Module.Dual F2 V)).equivFun.toEquiv.symm

end Affine


end

end PerfectCompleteness.LeftDecoder

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.GeometricCutSplit

open DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

def PrefixDepth (branch : Nat → Nat) (cutoff : Nat) : Nat → Type
  | 0 => Unit
  | depth + 1 => Fin (branch (cutoff + depth)) × PrefixDepth branch cutoff depth

abbrev Prefix (branch : Nat → Nat) (root cutoff : Nat) :=
  PrefixDepth branch cutoff (root - cutoff)

end PerfectCompleteness.GeometricCutSplit



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DecoderContraction

open scoped TensorProduct Classical
open TensorCosetEvaluation

noncomputable section

abbrev F2 := ZMod 2


end
end PerfectCompleteness.DecoderContraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputReference

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

end PerfectCompleteness.OwnInputReference



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RightDecoder

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

end PerfectCompleteness.RightDecoder



namespace PerfectCompleteness.RightDecoderDescendant

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

end PerfectCompleteness.RightDecoderDescendant

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderSourcePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DecoderSourcePullback

open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

abbrev F2 := ZMod 2


end
end PerfectCompleteness.DecoderSourcePullback

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_WholeArrayInteriorOwnInputLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayInteriorOwnInputLaw

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

end PerfectCompleteness.WholeArrayInteriorOwnInputLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeReplaySubtreeLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeReplaySubtree

open DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

abbrev F2 := ZMod 2

end
end PerfectCompleteness.WholeReplaySubtree

end

section

namespace PerfectCompleteness.WholeCutSubtree

noncomputable section

open scoped Classical
open DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

end
end PerfectCompleteness.WholeCutSubtree

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanLeftDecoderLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanRightDecoder

open scoped Classical
open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {N h : Nat}

variable {t v m : Nat}

abbrev OwnQuestions (clean : Fin (branch h) → Prop) :=
  {i : Fin (branch h) // clean i} → Fin t → Fin v

end
end PerfectCompleteness.CleanRightDecoder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderSeedLawLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderSeedLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.CleanDecoderSeedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayGroupingTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerReplayGroupingTransport

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler
open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.CutSamplerReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderRateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderRate

noncomputable section

open scoped BigOperators Classical
open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.CleanDecoderRate

end

section

namespace PerfectCompleteness.CleanDecoderPairLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.CleanDecoderPairLaw

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

namespace PerfectCompleteness.CutGroupedProjection

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler
open scoped BigOperators Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.CutGroupedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
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

abbrev F2 := ZMod 2

end
end PerfectCompleteness.OwnInputAffineSlice


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanPhysicalDecoderLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalDecoderLaw

noncomputable section

open scoped Classical
open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.CleanPhysicalDecoderLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerDirectionFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerDirectionFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {ℓ : Nat}

abbrev Rows (H : Type*) (ℓ : Nat) := Fin ℓ → H
end
end PerfectCompleteness.LowerDirectionFiber

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

namespace PerfectCompleteness.LowerCutRows

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.LowerCutRows

end

section

namespace PerfectCompleteness.LowerCutCallSplit

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.LowerCutCallSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairBackground
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutPairBackground

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

end PerfectCompleteness.LowerCutPairBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalDictionaryAppendMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryAppendMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def payload (bits : List Bool) : List Bool := bits.flatMap fun bit => [true, bit]

inductive Label
  | copyOut | copyBack | save | seed | emit | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyOut, .copyBack, .save, .seed, .emit,
  .restore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def steps (keyLength dictionaryLength : Nat) : Nat :=
  3 * keyLength + 2 * dictionaryLength + 6

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end PerfectCompleteness.CanonicalDictionaryAppendMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalDictionaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def appendMap : Fin 5 → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2

def searchMap : Fin 6 → Fin 8
  | 0 => 2
  | 1 => 0
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6

def appendTapes (tape : Fin 8 → K) : Fin 5 → K := fun i => tape (appendMap i)
def searchTapes (tape : Fin 8 → K) : Fin 6 → K := fun i => tape (searchMap i)

omit [DecidableEq K] in
theorem appendTapes_injective (tape : Fin 8 → K) (distinct : Function.Injective tape) :
    Function.Injective (appendTapes tape) :=
  distinct.comp (by decide : Function.Injective appendMap)

omit [DecidableEq K] in
theorem searchTapes_injective (tape : Fin 8 → K) (distinct : Function.Injective tape) :
    Function.Injective (searchTapes tape) :=
  distinct.comp (by decide : Function.Injective searchMap)

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Program

end PerfectCompleteness.CanonicalDictionaryMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalVertexNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalVertexNames

open CanonicalKeys
open Turing
open UniqueGamesTheorem.Foundations.Complexity

noncomputable section

variable {n : Nat}

def payloadBound (n bound : Nat) : Nat :=
  (1 + 2 ^ (11 ^ n) + 6 * n) * (max n (max bound 2) + 1) + 1

end
end PerfectCompleteness.CanonicalVertexNames

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalKeyShapeMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalOnlineNames

open CanonicalKeys

section Lists

variable {α : Type*} [BEq α] [LawfulBEq α]

theorem firstIndex_append_current (earlier suffix : List α) (key : α) :
    (earlier ++ [key]).idxOf key = (earlier ++ key :: suffix).idxOf key := by
  have present : key ∈ earlier ++ [key] := by simp
  have found := List.idxOf_append_of_mem (l₂ := suffix) present
  simpa only [List.append_assoc, List.singleton_append] using found.symm

end Lists

end PerfectCompleteness.CanonicalOnlineNames

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalDictionaryNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryNames

open CanonicalKeys Turing
open UniqueGamesTheorem.Foundations.Complexity

noncomputable section

variable {n : Nat}

def streamBound (n bound count : Nat) : Nat :=
  (2 * CanonicalVertexNames.payloadBound n bound + 2) * count

end
end PerfectCompleteness.CanonicalDictionaryNames

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ExactConditionalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ExactConditionalOutput

open scoped BigOperators Classical

noncomputable section

variable {S X : Type*} {E : S → Type*} [∀ s, Fintype (E s)]
  (count : ∀ s, E s → Nat)

def enumeration (s : S) : E s ≃ Fin (Fintype.card (E s)) := Fintype.equivFin _

def copies (s : S) : List (E s) :=
  (List.ofFn fun i : Fin (Fintype.card (E s)) =>
    List.replicate (count s ((enumeration s).symm i)) ((enumeration s).symm i)).flatten

theorem copies_length (s : S) : (copies count s).length = ∑ e, count s e := by
  simp only [copies, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.length_replicate, List.sum_ofFn]
  exact (enumeration s).symm.sum_comp (fun e : E s => count s e)

theorem copies_filter_length (s : S) (keep : E s → Bool) :
    ((copies count s).filter keep).length = ∑ e, if keep e then count s e else 0 := by
  simp only [copies, List.filter_flatten, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    _ = ∑ i : Fin (Fintype.card (E s)),
        if keep ((enumeration s).symm i) then count s ((enumeration s).symm i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : keep ((enumeration s).symm i) <;> simp [h]
    _ = _ := (enumeration s).symm.sum_comp
      (fun e : E s => if keep e then count s e else 0)

section Lists

variable {α : Type*} (shape : X → S) (entries : (x : X) → E (shape x) → α)

def localOutput (x : X) : List α := (copies count (shape x)).map (entries x)

def output (xs : List X) : List α := xs.flatMap (localOutput count shape entries)

theorem localOutput_length (D : Nat) (htotal : ∀ s, ∑ e, count s e = D) (x : X) :
    (localOutput count shape entries x).length = D := by
  rw [localOutput, List.length_map, copies_length, htotal]

theorem output_length (D : Nat) (htotal : ∀ s, ∑ e, count s e = D) (xs : List X) :
    (output count shape entries xs).length = D * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (localOutput count shape entries x ++ output count shape entries xs).length = _
      rw [List.length_append, localOutput_length count shape entries D htotal, ih,
        List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

end Lists

end
end PerfectCompleteness.ExactConditionalOutput

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedTag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedTag

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m v : Nat}

abbrev Flags := Fin (branch n) → Bool

end
end PerfectCompleteness.SourceProjectedTag

end

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

abbrev Signs := Fin 3 → Bool
abbrev Counters := Fin 3 → List Bool

end PerfectCompleteness.NormalizationReadMachine

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

abbrev Signs := NormalizationReadMachine.Signs

end PerfectCompleteness.SourceClauseReaderMachine


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceTupleData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceTupleData


open UniqueGamesTheorem.Foundations

inductive Tape (width : Nat) where
  | table
  | digit (position : Fin width)
  | work (slot : Fin 5)
  | variableName (position : Fin width) (slot : Fin 3)
  deriving DecidableEq, Fintype

end PerfectCompleteness.SourceTupleData

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_KeyMetadataMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.KeyMetadataMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeyShape ClauseSupport MixedSupport
open scoped BigOperators Classical

noncomputable section

variable {n : Nat}

def fieldValue (occurrence : Nat) (variableIDs : Fin 3 → Nat) : Fin 4 → Nat :=
  Fin.cases occurrence variableIDs

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def clean (ambient : σ) : State σ := (ambient, none)

inductive Label
  | suffix
  | copyOut
  | copyBack
  | «prefix»
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.suffix, .copyOut, .copyBack, .«prefix»]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def idIndex (field : Fin 4) : Fin 6 := ⟨field.val, lt_trans field.isLt (by decide)⟩

def idTape (tape : Fin 6 → K) (field : Fin 4) : K := tape (idIndex field)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun state => clean state.1)
    (match exit with | none => .halt | some label => .goto (fun _ => label))

theorem stepAux_finish (exit : Option Λ) (ambient : σ) (register : Option Bool)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) (ambient, register) base = ⟨exit, clean ambient, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def sourceLength (tape : Fin 6 → K) (base : K → List Bool) : Nat :=
  ∑ field : Fin 4, (base (idTape tape field)).length

omit [DecidableEq K] in
theorem selected_length_le (tape : Fin 6 → K) (base : K → List Bool) (field : Fin 4) :
    (base (idTape tape field)).length ≤ sourceLength tape base := by
  unfold sourceLength
  exact Finset.single_le_sum
    (f := fun selected : Fin 4 => (base (idTape tape selected)).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ field)

end
end PerfectCompleteness.KeyMetadataMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalKeyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalKeyMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys CanonicalKeyShape ClauseSupport MixedSupport
open scoped BigOperators Classical

noncomputable section

variable {n : Nat}

inductive Command (n : Nat)
  | terminal
  | metadata (position : Fin n)
  | header
  deriving DecidableEq, Fintype

def LocalLabel : Command n → Type
  | .terminal => Unit
  | .metadata _ => KeyMetadataMachine.Label
  | .header => Unit

instance localLabelFintype (command : Command n) : Fintype (LocalLabel command) := by
  cases command <;> unfold LocalLabel <;> infer_instance

instance localLabelDecidableEq (command : Command n) : DecidableEq (LocalLabel command) := by
  cases command <;> unfold LocalLabel <;> infer_instance

def main : (command : Command n) → LocalLabel command
  | .terminal => ()
  | .metadata _ => .suffix
  | .header => ()

def commands (n : Nat) : List (Command n) :=
  .terminal :: ((List.finRange n).reverse.map .metadata ++ [.header])

abbrev Label (n : Nat) := MachineFiniteSequence.Label LocalLabel (commands n)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def entry (labels : Label n → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel main (commands n) labels exit

def sourceLength (tape : Fin n → Fin 6 → K) (base : K → List Bool) : Nat :=
  ∑ i, KeyMetadataMachine.sourceLength (tape i) base

theorem resultOf_prepend {α : Type} (bits : α → List Bool)
    (cs : List α) (out : List Bool) :
    MachineFiniteSequence.resultOf (fun c acc => bits c ++ acc) cs out =
      cs.reverse.flatMap bits ++ out := by
  induction cs generalizing out with
  | nil => rfl
  | cons c cs ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc]

theorem steps_constant {α Data : Type} (result : α → Data → Data) (cost : α → Nat)
    (cs : List α) (data : Data) :
    MachineFiniteSequence.steps result (fun c _ => cost c) cs data = (cs.map cost).sum := by
  induction cs generalizing data with
  | nil => rfl
  | cons c cs ih => simp only [MachineFiniteSequence.steps, List.map_cons, List.sum_cons, ih]

theorem commands_cost (cost : Command n → Nat) :
    ((commands n).map cost).sum = cost .terminal + (∑ i, cost (.metadata i)) + cost .header := by
  simp only [commands, List.map_cons, List.map_append, List.map_map, List.map_reverse,
    List.sum_cons, List.sum_append, List.sum_reverse, List.map_nil, List.sum_nil, Nat.add_zero]
  rw [← Fin.sum_univ_def]
  simp only [Function.comp_def, Nat.add_assoc]

omit [DecidableEq K] in
theorem source_ne_output (tape : Fin n → Fin 6 → K)
    (distinct : ∀ i, Function.Injective (tape i)) (output : K)
    (sharedOutput : ∀ i, tape i 5 = output) (i : Fin n) (field : Fin 4) :
    KeyMetadataMachine.idTape (tape i) field ≠ output := by
  intro h
  have hi : KeyMetadataMachine.idIndex field = (5 : Fin 6) :=
    distinct i (h.trans (sharedOutput i).symm)
  have hv := congrArg Fin.val hi
  have hf := field.isLt
  change field.val = 5 at hv
  omega

end
end PerfectCompleteness.CanonicalKeyMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CanonicalEndpointMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CanonicalEndpointMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys CanonicalKeyShape ClauseSupport
open scoped Classical

noncomputable section

variable {n : Nat} {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end

end PerfectCompleteness.CanonicalEndpointMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineTransducerCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

open Turing

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev Alphabet (K : Type) (_ : K) := Bool
abbrev State (σ Q : Type) := (σ × Q) × Option Bool

def scanLoop (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push scratch (fun state => state.2.getD false)
        (.goto fun state => emitterLabel state.1.2 (state.2.getD false)))
      (.load (fun state => ((state.1.1, initial), none)) (.goto fun _ => restoreLabel)))

end UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CircuitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin

inductive Gate where
  | const (value : Bool)
  | not (input : Nat)
  | and (left right : Nat)
  | or (left right : Nat)
  deriving DecidableEq

def Gate.Bounded (g : Gate) (bound : Nat) : Prop :=
  match g with
  | .const _ => True
  | .not x => x < bound
  | .and x y | .or x y => x < bound ∧ y < bound

def Gate.eval (g : Gate) (wires : Nat → Bool) : Bool :=
  match g with
  | .const b => b
  | .not x => !(wires x)
  | .and x y => wires x && wires y
  | .or x y => wires x || wires y

theorem Gate.bounded_mono (g : Gate) {a b : Nat} (hab : a ≤ b)
    (h : g.Bounded a) : g.Bounded b := by
  cases g with
  | const _ => trivial
  | not _ => exact Nat.lt_of_lt_of_le h hab
  | and _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩
  | or _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩

def Ordered (start : Nat) (gates : List Gate) : Prop :=
  ∀ i (hi : i < gates.length), gates[i].Bounded (start + i)

@[simp] theorem ordered_nil (start : Nat) : Ordered start [] := by
  intro i hi
  simp at hi

def run (start : Nat) : List Gate → (Nat → Bool) → (Nat → Bool)
  | [], A => A
  | g :: gs, A => run (start + 1) gs (Function.update A start (g.eval A))

@[simp] theorem run_singleton (start : Nat) (g : Gate) (A : Nat → Bool) :
    run start [g] A = Function.update A start (g.eval A) := rfl

@[simp] theorem run_singleton_here (start : Nat) (g : Gate) (A : Nat → Bool) :
    run start [g] A start = g.eval A := by simp

structure Circuit where
  inputs : Nat
  gates : List Gate
  ordered : Ordered inputs gates
  output : Fin (inputs + gates.length)

abbrev Circuit.wires (C : Circuit) : Nat := C.inputs + C.gates.length

end UniqueGamesTheorem.Foundations.Complexity.CookLevin

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_DescriptorProjectionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DescriptorProjectionMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat}
  {n t q : Nat}
  {rows repeats : Nat → Nat}
  (hq : 0 < q)


variable {σ : Type}
  [Fintype σ]
  [DecidableEq σ]

def keys (σ : Type) [Fintype σ] : List σ := (Finset.univ : Finset σ).toList

omit [DecidableEq σ] in
theorem keys_complete (state : σ) : state ∈ keys σ := by
  simp [keys]

end
end PerfectCompleteness.DescriptorProjectionMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_CompletedEdgeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CompletedEdgeMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat}
  {n t q : Nat}
  {rows repeats : Nat → Nat}
  (hq : 0 < q)

def leftMap (i : Fin 8) : Fin 10 := ⟨i.val, lt_trans i.isLt (by decide)⟩

def rightMap (i : Fin 8) : Fin 10 := if i = 1 then 8 else leftMap i

theorem leftMap_injective : Function.Injective leftMap := by decide
theorem rightMap_injective : Function.Injective rightMap := by decide

theorem forward_ne_left : ∀ i, (9 : Fin 10) ≠ leftMap i := by decide
theorem forward_ne_right : ∀ i, (9 : Fin 10) ≠ rightMap i := by decide

theorem leftMap_work : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 →
    leftMap i ≠ 1 ∧ leftMap i ≠ 7 ∧ leftMap i ≠ 8 := by decide

theorem rightMap_work : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 →
    rightMap i ≠ 1 ∧ rightMap i ≠ 7 ∧ rightMap i ≠ 8 := by decide

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def leftTapes (work : Fin 10 → K) : Fin 8 → K := fun i => work (leftMap i)
def rightTapes (work : Fin 10 → K) : Fin 8 → K := fun i => work (rightMap i)

end
end PerfectCompleteness.CompletedEdgeMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_PositionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixModel

inductive Token where
  | const (value : Bool)
  | not | and | or
  | input (wire : Nat)
  deriving DecidableEq

namespace Token

def tag : Token → Fin 6
  | .const false => 0
  | .const true => 1
  | .not => 2
  | .and => 3
  | .or => 4
  | .input _ => 5

def words : Token → List Nat
  | .const false => [0]
  | .const true => [1]
  | .not => [2]
  | .and => [3]
  | .or => [4]
  | .input wire => [5, wire]

end Token

def tokenWords (tokens : List Token) : List Nat := tokens.flatMap Token.words

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixModel

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_PostfixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixMachine

open Turing PostfixModel Hastad


inductive Tape
  | input | current | remaining | roots | left | right | reversed | output | scratch
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .current, .remaining, .roots, .left,
  .right, .reversed, .output, .scratch]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PostfixMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ForestStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage

open Turing
open PostfixModel


inductive Tape
  | lower (tape : PostfixMachine.Tape)
  | tokens | records | rootTable
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_InitializationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine


open Turing
open PostfixModel

inductive Tape where
  | remaining | current | threshold | scratch | reversed
  | rawInput | witnessBound | capacity | closure
  deriving DecidableEq

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine

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

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | copyFirst | copySecond | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

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
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineProductGatherBoundsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | run (label : MachinePreservingLookup.Label)
  | cleanup
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_TermMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TermMachine

open Turing PostfixModel


inductive Tape
  | cursor | capacity | roots | count | reversed
  | position | address | value | scratch | copy | saveLeft | saveRight
  deriving DecidableEq


end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TermMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ProducerInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerInvariant

open PostfixModel

structure Snapshot where
  current : Nat
  roots : List Nat
  reversedRecords : List Bool
  deriving DecidableEq


end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ProducerInvariant

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_InitializationStageLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena


open Turing

inductive Extra
  | cursor | capacity | position | address | value | scratch | copy | saveLeft | saveRight
  | countdown | q | raw
  deriving DecidableEq

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OriginalWholeCutTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutTape

open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

section Rearrangement

variable {D T C S E L O B : Type*}

def regroupStep :
    ((D → ((T → S) × E)) × ((L × ((C → S) × B)) × O)) ≃
      (((D → E) × (L × O)) × (((D × T ⊕ C) → S) × B)) where
  toFun x :=
    ((fun d => (x.1 d).2, (x.2.1.1, x.2.2)),
      (fun call => match call with
        | .inl dt => (x.1 dt.1).1 dt.2
        | .inr c => x.2.1.2.1 c,
       x.2.1.2.2))
  invFun x :=
    ((fun d => (fun terminal => x.2.1 (.inl (d, terminal)), x.1.1 d)),
      ((x.1.2.1, (fun c => x.2.1 (.inr c), x.2.2)), x.1.2.2))
  left_inv x := rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext call
        cases call <;> rfl
      · rfl

def prependUnit (A : Type*) : A ≃ Unit × A where
  toFun x := ((), x)
  invFun := Prod.snd
  left_inv _ := rfl
  right_inv x := by rcases x with ⟨u, x⟩; cases u; rfl

end Rearrangement

end

end PerfectCompleteness.OriginalWholeCutTape

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_CompletedVisitOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CompletedVisitOrder

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat}
  {n t v m : Nat}
  (rows repeats : Nat → Nat)
  [NeZero m]
  (hn : 0 < n)
  (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))
  (δ : ℚ)

theorem mem_copies {S : Type*} {E : S → Type*}
    [Fintype S] [∀ s, Fintype (E s)] (count : ∀ s, E s → Nat)
    (s : S) (e : E s) (positive : 0 < count s e) :
    e ∈ ExactConditionalOutput.copies count s := by
  unfold ExactConditionalOutput.copies
  refine List.mem_flatten.mpr ⟨List.replicate (count s e) e, ?_, ?_⟩
  · refine List.mem_ofFn.mpr ⟨ExactConditionalOutput.enumeration s e, ?_⟩
    simp only [Equiv.symm_apply_apply]
  · exact List.mem_replicate.mpr ⟨Nat.ne_of_gt positive, rfl⟩

end
end PerfectCompleteness.CompletedVisitOrder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalProjectedMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalProjectedMeeting

noncomputable section

open scoped Classical
open DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

end
end PerfectCompleteness.CleanPhysicalProjectedMeeting

end

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

abbrev Alphabet (_ : K) := Bool

/-- Reset both the ambient finite state and the drain register before exiting. -/
def finish (initial : σ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun _ => (initial, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- A fixed finite chain skips Boolean unary words. A true head causes one
additional delimiter pop; a false head is already the complete zero word.
Only the one-bit head register is examined. -/
def skipBits (source : K) : Nat →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, next => .load (fun state => (state.1, none)) next
  | count + 1, next =>
      let rest := skipBits source count next
      .pop source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop source (fun state _ => (state.1, none)) rest)
          (.load (fun state => (state.1, none)) rest))

inductive Label
  | guard | skipTail | skipReverse | skipPredicate | select | copy
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skipTail, .skipReverse, .skipPredicate,
  .select, .copy]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev HeadTapes (K : Type) := Fin 6 → K

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

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

/-- All varying literals are finite: one Boolean or one bounded offset. -/
inductive Command (h : Nat) (σ : Type) (bound : Nat)
  | literal (word : List Bool)
  | bit (value : σ → Bool)
  | bounded (value : σ → Fin bound)
  | scaled (source : Fin h) (coefficient : Nat)
  | scaledIf (source : Fin h) (coefficient : Nat) (active : σ → Bool)

inductive Phase (bound : Nat)
  | entry | emit (symbol : Bool) | restore | offset (value : Fin bound)
  | scanIf (active : Bool) | emitIf (active symbol : Bool)
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (coefficient : Nat) (_ : Unit) (symbol : Bool) : List Bool :=
  if symbol then List.replicate coefficient true else []

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

abbrev Label (count bound : Nat) := Fin (count + 1) × Phase bound

def labelAt (count bound r : Nat) (phase : Phase bound) : Label count bound :=
  (⟨min r count, by omega⟩, phase)

def commandAt {count : Nat} (commands : Fin count → Command h σ bound) (r : Nat) :
    Command h σ bound :=
  if hr : r < count then commands ⟨r, hr⟩ else .literal []

def listCommands (commands : List (Command h σ bound)) :
    Fin commands.length → Command h σ bound := fun i => commands[i]

def affineCommands (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    List (Command h σ bound) :=
  terms.map (fun term => .scaled term.1 term.2) ++ [.bounded offset, .literal [false]]

@[simp] theorem affineCommands_length (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    (affineCommands terms offset).length = terms.length + 2 := by
  simp [affineCommands]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringOpinionsLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach

variable {V D A : Type*}

/-- Check all base constraints along the recorded walk. The reach certificates
select genuine vertices in the two full-radius neighborhood balls. -/
def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

/-- Reversal preserves the recorded walk and changes its direction flag. -/
def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

/-- An actual powered constraint graph, with a common raw alphabet at all
vertices. Its reversal law is witnessed by the orientation bit. -/
def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

end UniqueGamesTheorem.Foundations.PCP.PoweringTest

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

abbrev Field (S : Nat) := (GraphTables.Label × GraphTables.Label) ⊕ (Fin S ⊕ Fin S)

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

def fieldEquiv (S : Nat) : Field S ≃ Fin (4096 + (S + S)) :=
  (Equiv.sumCongr GraphTables.relationIndex
    (finSumFinEquiv : (Fin S ⊕ Fin S) ≃ Fin (S + S))).trans finSumFinEquiv

def inputEquiv (t S : Nat) : (Fin t × Field S) ≃ Fin (inputSize t S) :=
  (Equiv.prodCongr (Equiv.refl (Fin t)) (fieldEquiv S)).trans finProdFinEquiv

/-- The scan order is the fixed increasing finite-index order. -/
def firstMatch {S : Nat} (mask : Fin S → Bool) : Option (Fin S) :=
  (List.ofFn id).find? mask

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_CloudRoundingLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.edgeSatisfied_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetRetraction.rejectionCount_pullback _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.acceptsAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.reverseAt_graphRows _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_edgeSatisfied _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_rejectionCount _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_ofGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GenericGraphTables.semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.GraphTransport.reindex_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringReach.headFromEnd_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringReach.tailFromStart_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringWalks.lazyGraph_rot_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringWalks.lazyGraph_rot_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
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

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

end GraphRounding

end UniqueGamesTheorem.Foundations.PCP.CloudRounding

end

section

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

/-- Finite executable input data, with the two graph laws certified on lookup. -/
structure Table (vertices ports : Nat) where
  reverseIndex : Vector (Fin (vertices * ports)) (vertices * ports)
  relations : Vector GraphTables.RelationTable (vertices * ports)
  involutive : Function.Involutive
    (fun i : Fin (vertices * ports) => reverseIndex[i])
  transpose : ∀ (i : Fin (vertices * ports)) (a b : Label),
    GraphTables.relationAt relations[reverseIndex[i]] b a =
      GraphTables.relationAt relations[i] a b

variable {n d : Nat}

/-- One reverse-index lookup and the fixed mixed-radix decoding. -/
def rotation (table : Table n d) (e : Fin n × Fin d) : Fin n × Fin d :=
  (rowIndex n d).symm table.reverseIndex[rowIndex n d e]

/-- Lookup of the full stored binary predicate. -/
def accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) : Bool :=
  GraphTables.relationAt table.relations[rowIndex n d e] a b

@[simp] theorem rowIndex_rotation (table : Table n d) (e : Fin n × Fin d) :
    rowIndex n d (rotation table e) = table.reverseIndex[rowIndex n d e] := by
  exact (rowIndex n d).apply_symm_apply _

theorem rotation_involutive (table : Table n d) : Function.Involutive (rotation table) := by
  intro e
  simp only [rotation, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex n d).symm (table.involutive (rowIndex n d e))).trans
    ((rowIndex n d).symm_apply_apply e)

theorem accepts_rotation (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    accepts table (rotation table e) b a = accepts table e a b := by
  simpa only [accepts, rowIndex_rotation] using table.transpose (rowIndex n d e) a b

/-- The actual reversible regular port graph represented by the vectors. -/
def portGraph (table : Table n d) : PortGraph (Fin n) (Fin d) where
  rot :=
    { toFun := rotation table
      invFun := rotation table
      left_inv := rotation_involutive table
      right_inv := rotation_involutive table }
  rot_involutive := rotation_involutive table

@[simp] theorem portGraph_rot (table : Table n d) (e : Fin n × Fin d) :
    (portGraph table).rot e = rotation table e := rfl

/-- Constraint-graph semantics, with each vertex-port pair a distinct dart. -/
def baseGraph (table : Table n d) : ConstraintGraph (Fin n) (Fin n × Fin d) Label where
  reverse := (portGraph table).rot
  reverse_involutive := rotation_involutive table
  tail := Prod.fst
  accepts := accepts table
  reverse_accepts := accepts_rotation table

@[simp] theorem baseGraph_reverse (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).reverse e = rotation table e := rfl

@[simp] theorem baseGraph_tail (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).tail e = e.1 := rfl

@[simp] theorem baseGraph_head (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).head e = (rotation table e).1 := rfl

@[simp] theorem baseGraph_accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    (baseGraph table).accepts e a b = accepts table e a b := rfl

/-- Materialize a reversible port graph and its predicates into the fixed rows. -/
def ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rowIndex n d (G.rot ((rowIndex n d).symm i)))
  relations := Vector.ofFn (fun i => GraphTables.relationOf (predicate ((rowIndex n d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply]
    exact (congrArg (rowIndex n d) (G.rot_involutive ((rowIndex n d).symm i))).trans
      ((rowIndex n d).apply_symm_apply i)
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
      Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]
    exact htranspose ((rowIndex n d).symm i) a b

@[simp] theorem rotation_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) : rotation (ofPortGraph G predicate htranspose) e = G.rot e := by
  simp only [rotation, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

@[simp] theorem accepts_ofPortGraph (G : PortGraph (Fin n) (Fin d))
    (predicate : (Fin n × Fin d) → Label → Label → Bool)
    (htranspose : ∀ e a b, predicate (G.rot e) b a = predicate e a b)
    (e : Fin n × Fin d) (a b : Label) :
    accepts (ofPortGraph G predicate htranspose) e a b = predicate e a b := by
  simp only [accepts, ofPortGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply, GraphTables.relationAt_relationOf]

end UniqueGamesTheorem.Foundations.PCP.PortTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PoweringOpinionTables
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.graph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTables.lookup_ofGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.portGraph_rot_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.accepts_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.portGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.rotation_ofPortGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_next _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.square_rot_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ZigzagGraphs.zigzag_rot_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

theorem match_in_tail (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

def firstIndex (p : X → Prop) [DecidablePred p] :
    (xs : List X) → (∃ a ∈ xs, p a) → Fin xs.length
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨0, Nat.zero_lt_succ xs.length⟩ else
      (firstIndex p xs (match_in_tail p h ha)).succ

/-- The stored index selects the very same first address as `scanWitness`,
not just an address with the same endpoint. -/
theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h
    by_cases ha : p a
    · simp [firstIndex, scanWitness, ha]
    · simpa only [firstIndex, scanWitness, ha, dite_false, List.get_cons_succ'] using
        ih (match_in_tail p h ha)

/-- A local label slot is an index into the explicit bounded address list. -/
abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := by
  change (allAddresses d t).get (firstIndex
    (fun w => (wordToBall G t center w).val = u.val) (allAddresses d t) _) =
      (scanWitness _ _ _).val
  exact get_firstIndex _ _ _

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

/-- Materialize a padded label in the common address order. -/
def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

/-- Exact evaluation bridge for every local target, with no consistency
assumption on labels at distinct addresses that reach the same vertex. -/
theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

/-- One finite row for each constraint checked along a recorded walk. -/
structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

/-- The only target vertices inspected are the actual edge endpoints. -/
def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b

end UniqueGamesTheorem.Foundations.PCP.PoweringOpinionTables

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

namespace UniqueGamesTheorem.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

/-- Program-constant output alphabet size for degree `d` and walk length `n+1`. -/
def labelCount (d n : Nat) : Nat := 64 ^ addressCount d (n + 1)

/-- Number of directed recorded-walk occurrences, including orientation. -/
def dartCount (vertices d n : Nat) : Nat := 2 * vertices * d ^ (n + 1)

end UniqueGamesTheorem.Foundations.PCP.PoweringTables

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

namespace UniqueGamesTheorem.Foundations.PCP.PoweringRowData

open UniqueGamesTheorem.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

/-- An actual endpoint comparison; it has no reachability oracle input. -/
def endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center target : Fin vertices) (i : AddressIndex d t) : Bool :=
  decide ((wordToBall G t center ((allAddresses d t).get i)).val = target)

def slotCount (d n : Nat) : Nat := (allAddresses d (n + 1)).length

end UniqueGamesTheorem.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

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

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/

/-!
# Uniform restriction of Boolean tapes

Restricting a uniformly sampled Boolean function to a decidable subset gives
the uniform law on functions on that subset.  The subset and its complement
may be empty: their Boolean function spaces still contain the constant-false
function.  Extending by false gives a canonical full-domain oracle address.
-/

namespace UniqueGamesTheorem.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

/-- The values of a full Boolean tape on the legal coordinates. -/
def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

/-- Extend a tape on legal coordinates by false on every other coordinate. -/
def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

end UniqueGamesTheorem.Foundations.PCP.UniformRestriction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetGraphLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

abbrev Address (V E A : Type*) := (V × Cube A) ⊕ (E × Cube (A × A))

abbrev LocalEvent (A : Type*) := Fin 4 × AlphabetReduction.InputCoordinate A ×
  Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A)

abbrev Event (E A : Type*) := E × LocalEvent A

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev legal (G : ConstraintGraph V E A) (e : E) (p : A × A) : Prop :=
  G.accepts e p.1 p.2 = true

instance legalDecidable (G : ConstraintGraph V E A) (e : E) :
    DecidablePred (legal G e) :=
  fun p => inferInstanceAs (Decidable (G.accepts e p.1 p.2 = true))

def restrictTape (G : ConstraintGraph V E A) (e : E) (f : Cube (A × A)) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) := UniformRestriction.restrict (legal G e) f

def extendTape (G : ConstraintGraph V E A) (e : E)
    (f : Cube (AlphabetReduction.LegalPair (G.accepts e))) : Cube (A × A) :=
  UniformRestriction.extend (legal G e) f

def globalizeQuery (G : ConstraintGraph V E A) (e : E) :
    AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e)) → Address V E A
  | .inl (side, tape) => .inl ((if side then G.head e else G.tail e), tape)
  | .inr tape => .inr (e, extendTape G e tape)

def verifier (G : ConstraintGraph V E A) : QueryIncidence.Verifier (Event E A) (Address V E A) 6 where
  query := fun (e, kind, k, f, g, r₀, r₁, r₂) slot =>
    globalizeQuery G e (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
      (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
      (restrictTape G e r₁) (restrictTape G e r₂) slot)
  accepts := fun (_, kind, _, _, _, _, _, _) b => AssignmentTester.eventAccepts kind b

def vertexBlock (assignment : Address V E A → Bool) (v : V) : Cube A → Bool :=
  fun tape => assignment (.inl (v, tape))

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

def honestAssignment (G : ConstraintGraph V E A) (labeling : V → A) : Address V E A → Bool
  | .inl (v, tape) => tape (labeling v)
  | .inr (e, tape) => tape (labeling (G.tail e), labeling (G.head e))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem honest_vertexBlock (G : ConstraintGraph V E A) (labeling : V → A) (v : V) :
    vertexBlock (honestAssignment G labeling) v = CodeComposition.codeword (labeling v) := rfl

def graph [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A) :
    ConstraintGraph (QueryIncidence.Vertex (Event E A) (Address V E A))
      (QueryIncidence.Dart (Event E A) 6) (QueryIncidence.Label 6) := QueryIncidence.graph (verifier G) (by omega)

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraph

end

/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

/-- The number of local verifier events for an alphabet with `q` symbols. -/
def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

end UniqueGamesTheorem.Foundations.PCP.AlphabetGraphBounds

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

open UniqueGamesTheorem.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

/-- Left component first, with the right component varying fastest. -/
def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

/-- The complete left block precedes the complete right block. -/
def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

/-- Explicit binary rank/unrank; the inverse extracts digits by division and
remainder, as supplied by the executable `finFunctionFinEquiv`. -/
def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

/-- A reusable explicit increasing-index enumeration. -/
def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

def localEvents (q : Nat) : List (AlphabetGraph.LocalEvent (Fin q)) :=
  ordered (localEventEquiv q)

@[simp] theorem localEvents_length (q : Nat) : (localEvents q).length = localCount q :=
  ordered_length _

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

@[simp] theorem localCount_formula (q : Nat) :
    localCount q = 4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5 := rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_QueriesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Executable six-query generation on fixed full Boolean cubes. The event
type is exactly `AlphabetGraph.LocalEvent`, including all five full tapes.
Only the returned joint-table addresses are masked outside the input relation;
no legal-pair enumeration or change of sample multiplicities occurs. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries

open UniqueGamesTheorem.Foundations.Hastad

abbrev RawQuery (q : Nat) :=
  (Bool × Cube (Fin q)) ⊕ Cube (Fin q × Fin q)

abbrev LocalEvent (q : Nat) := AlphabetGraph.LocalEvent (Fin q)

/-- Canonical full-cube proof address: every illegal coordinate is false. -/
def mask {q : Nat} (P : Fin q → Fin q → Bool) (f : Cube (Fin q × Fin q)) :
    Cube (Fin q × Fin q) := fun p => if P p.1 p.2 then f p else false

def xorTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a ^^ g a

def andTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a && g a

/-- The coordinate value of the paired input codeword before masking. -/
def inputPairTape {q : Nat} (k : Bool × Cube (Fin q)) : Cube (Fin q × Fin q) :=
  fun p => if k.1 then k.2 p.2 else k.2 p.1

/-- Actual six queries, computed directly from fixed full tapes and P.
Padding slots repeat precisely the addresses used by `eventQueries`. -/
def query {q : Nat} (P : Fin q → Fin q → Bool) (event : LocalEvent q)
    (slot : Fin 6) : RawQuery q :=
  match event with
  | (kind, k, f, g, r₀, r₁, r₂) =>
    if kind = 0 then
      if slot = 0 then .inr (mask P f) else
      if slot = 1 then .inr (mask P g) else .inr (mask P (xorTape f g))
    else if kind = 1 then
      if slot = 0 then .inr (mask P r₀) else
      if slot = 1 then .inr (mask P (xorTape r₀ (andTape f g))) else
      if slot = 2 then .inr (mask P r₁) else
      if slot = 3 then .inr (mask P (xorTape r₁ f)) else
      if slot = 4 then .inr (mask P r₂) else .inr (mask P (xorTape r₂ g))
    else if kind = 2 then
      if slot = 0 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (fun _ => true)))
    else
      if slot = 0 then .inl k else
      if slot = 1 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (inputPairTape k)))

/-- Attach the actual endpoints and edge identifier to a local raw address. -/
def globalize {q : Nat} {V E : Type*} (tail head : V) (edge : E) :
    RawQuery q → AlphabetGraph.Address V E (Fin q)
  | .inl (side, tape) => .inl ((if side then head else tail), tape)
  | .inr tape => .inr (edge, tape)

@[simp] theorem mask_idempotent {q : Nat} (P : Fin q → Fin q → Bool)
    (f : Cube (Fin q × Fin q)) : mask P (mask P f) = mask P f := by
  funext p
  cases hp : P p.1 p.2 <;> simp [mask, hp]

/-- Proof-only comparison map: extend the original legal-coordinate addresses.
The executable `query` function above never calls this map. -/
def extendQuery {q : Nat} (P : Fin q → Fin q → Bool) :
    AlphabetReduction.InputCoordinate (Fin q) ⊕ Cube (AlphabetReduction.LegalPair P) →
      RawQuery q
  | .inl k => .inl k
  | .inr tape => .inr (UniformRestriction.extend (fun p : Fin q × Fin q => P p.1 p.2 = true) tape)

/-- Pointwise equality with the existing tester after restricting all five
full input tapes and canonically extending the resulting query. The statement
does not require any legal pair to exist. -/
theorem query_eq_extend_eventQueries {q : Nat} (P : Fin q → Fin q → Bool)
    (kind : Fin 4) (k : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) (slot : Fin 6) :
    query P (kind, k, f, g, r₀, r₁, r₂) slot =
      extendQuery P (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding P) kind k
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) f)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) g)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₀)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₁)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₂) slot) := by
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, AssignmentTester.eventQueries, hk₀, hk₁, hk₂, ite_true, if_true, ite_false, if_false]
  all_goals split_ifs <;> simp_all only [extendQuery]
  all_goals rfl

theorem globalize_extendQuery {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E)
    (x : AlphabetReduction.InputCoordinate (Fin q) ⊕
      Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    globalize (G.tail e) (G.head e) e (extendQuery (G.accepts e) x) =
      AlphabetGraph.globalizeQuery G e x := by
  cases x with
  | inl k => cases k; rfl
  | inr tape => rfl

/-- The executable raw queries are exactly the actual verifier queries after
attaching the endpoints and edge tag. This includes self-loops, duplicate
queries, empty legal relations, and every original five-tape event. -/
theorem globalize_query {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E) (event : LocalEvent q) (slot : Fin 6) :
    globalize (G.tail e) (G.head e) e (query (G.accepts e) event slot) =
      (AlphabetGraph.verifier G).query (e, event) slot := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rw [query_eq_extend_eventQueries]
  exact globalize_extendQuery G e _

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries

end

section

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

/-- Exact local address comparison. A loop identifies the two endpoint tables;
the joint edge table is always disjoint from every endpoint table. -/
def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

/-- Search the fixed six positions for the least occurrence of an address. -/
def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

/-- The old predicate is read in the same row-major order as a graph row. -/
def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations

end

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

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

abbrev Pattern (q : Nat) := Fin q → Bool

/-- The enumeration visits only the fixed-size truth table, never proof assignments. -/
def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

/-- Finite test data, with no soundness or complexity assumption. -/
structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.variables + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.variables) : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.variables (finProdFinEquiv (finProdFinEquiv (e, p), j))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.variables → Bool :=
  fun v => B (oldIndex V v)

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

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

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

theorem twelve_query_auxiliary_factor : 2 ^ 12 * (12 - 3) = 36864 := by decide

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

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .scratch, .vertices,
  .darts, .tail, .head, .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

inductive Label (headerCount rowCount : Nat)
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts | seedIndex
  | header (label : Emitter.Label headerCount 36864)
  | headerClearTail | headerClearHead
  | guard | startTail | readTail | startReverse | readReverse
  | headTableFirst | headTableSecond | headIndexFirst | headIndexSecond
  | headHeaderVertices | headHeaderDarts | headLookup (label : Lookup.Label)
  | readRelation
  | row (label : Emitter.Label rowCount 36864)
  | clearTail | clearHead | clearReverse | nextRow | reverseOutput
  deriving DecidableEq, Fintype

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

end Program

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

open Turing
open FinalCNFMachine.Program (Tape )

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

def redirectLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def redirectCfg (labels : Λ → Λ') (haltTarget : Option Λ') (cfg : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ :=
  ⟨redirectLabel labels haltTarget cfg.l, cfg.var, cfg.stk⟩

/-- Structural redirection changes only the destinations of goto and halt. -/
def redirectStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (redirectStmt labels haltTarget next)
  | .peek k f next => .peek k f (redirectStmt labels haltTarget next)
  | .pop k f next => .pop k f (redirectStmt labels haltTarget next)
  | .load f next => .load f (redirectStmt labels haltTarget next)
  | .branch test yes no => .branch test
      (redirectStmt labels haltTarget yes) (redirectStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

end Redirect

/-- The raw machine has thirteen tapes. These are precisely the twelve
non-output tapes, including the original input and retained archive. -/
def chosen : List Tape :=
  [.input, .accumulator, .scratch, .vertices, .darts, .tail, .head,
    .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

@[simp] theorem chosen_length : chosen.length = 12 := rfl

@[simp] theorem mem_chosen (tape : Tape) : tape ∈ chosen ↔ tape ≠ .output := by
  cases tape <;> simp [chosen]

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

/-- Explicit tape frame used during the header phase; all unlisted work tapes
are empty. The archive is separate from the unread input. -/
def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete relation addresses for the final Boolean verifier

Six-bit labels use the already checked executable little-endian enumeration.
A twelve-bit CNF pattern is split into its two endpoint labels, then addressed
in the graph table's row-major order. This fixed address map uses the actual
`VerifierToCNF.patternAt` enumeration, so no assumed correspondence between
two enumeration orders is needed. The graph interpretation is an explicit
relabeling of the validated table semantics.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineFixedDivMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) (d : Nat) := (σ × Fin d) × Option Bool

def residue (d : Nat) (positive : 0 < d) (n : Nat) : Fin d :=
  ⟨n % d, Nat.mod_lt n positive⟩

def nextResidue (d : Nat) (positive : 0 < d) (r : Fin d) : Fin d :=
  residue d positive (r.val + 1)

def scanLoop (d : Nat) (positive : 0 < d) (source quotient : K)
    (scanLabel : Λ) (emitterLabel : Fin d → Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.branch (fun state => decide ((nextResidue d positive state.1.2).val = 0))
        (.push quotient (fun _ => true)
          (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
            (.goto fun _ => scanLabel)))
        (.load (fun state => ((state.1.1, nextResidue d positive state.1.2), state.2))
          (.goto fun _ => scanLabel)))
      (.push source (fun _ => false) (.goto fun state => emitterLabel state.1.2)))

end UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ExpanderRowControlLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d
abbrev rowFactor (d : Nat) : Nat := cloudSize d * degree d

/-- The encoded vertex of `firstH` already stores both square ports.
The two graph-return registers and final-H register are overwritten by the
corresponding callbacks. Every field is bounded independently of table size. -/
structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

/-- Consume the finite cloud coordinate and input port, and perform the first
lookup in the fixed table. Initial register values need no inhabitance choice. -/
def start {d : Nat} (H : Table (cloudSize d) d)
    (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : Control d :=
  let ports := (rowIndex d d).symm port
  let first := lookup H (cloud, ports.1)
  let square := (rowIndex (degree d) (degree d)).symm first.1
  { firstH := first
    lastInput := ports.2
    firstG := square.1
    secondG := square.2
    lastH := first }

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

/-- The second graph remainder completes the final lookup in the fixed table.
The square return ports are ordered second, first, as in `stepLookup`. -/
def receiveSecond {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with
    secondG := returnedPort
    lastH := lookup H
      (rowIndex (degree d) (degree d) (returnedPort,s.firstG),s.lastInput) }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

def outputPort {d : Nat} (s : Control d) : Fin (degree d) :=
  rowIndex d d (s.lastH.2,s.firstH.2)

/-- The entire bounded contribution to the emitted row: output port plus
`q` times output cloud, with `q = d*d`. -/
def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def firstAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (firstOffset s).val

def secondAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  degree d * vertex + (secondOffset s).val

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

@[simp] theorem receiveSecond_port {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (r : Fin (degree d)) : (receiveSecond H s r).secondG = r := rfl

end UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

end

section

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open UniqueGamesTheorem.Foundations.Complexity (encodeWords )

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

end UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

inductive Label (d : Nat)
  | initialize_
  | firstEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | firstReverse
  | firstLookup (label : MachinePreservingLookupClean.Label)
  | firstScan
  | firstResidue (r : Fin (degree d))
  | clearQuery
  | secondEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | secondReverse
  | secondLookup (label : MachinePreservingLookupClean.Label)
  | secondScan
  | secondResidue (r : Fin (degree d))
  | outputEmit (label : PCP.AlphabetTable.Emitter.Label 3 (rowFactor d))
  | cleanup (i : Fin 6)
  | done
  deriving DecidableEq, Fintype

abbrev Ambient (ρ : Type) (d : Nat) := ρ × Control d
abbrev State (ρ : Type) (d : Nat) :=
  PCP.AlphabetTable.Emitter.State (Ambient ρ d × Fin (degree d))

/-- The residue and the emitter's unit field are just permuted; no tape is
read or written by this static change of finite state coordinates. -/
def divisionStates (ρ : Type) (d : Nat) :
    MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.1.2), ()), s.2)
  invFun s := (((s.1.1.1, ()), s.1.1.2), s.2)
  left_inv := by rintro ⟨⟨⟨a, u⟩, r⟩, b⟩; cases u; rfl
  right_inv := by rintro ⟨⟨⟨a, r⟩, u⟩, b⟩; cases u; rfl

def firstFinish {ρ : Type} {d : Nat} (s : Ambient ρ d × Unit)
    (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveFirst s.1.2 r), ())

def lookupTape : Fin 5 → Tape
  | ⟨0, _⟩ => .table
  | ⟨1, _⟩ => .queryIndex
  | ⟨2, _⟩ => .lookupWork
  | ⟨3, _⟩ => .lookupOutput
  | _ => .lookupRestore

def dirtyTape : Fin 6 → Tape
  | ⟨0, _⟩ => .queryIndex
  | ⟨1, _⟩ => .lookupOutput
  | ⟨2, _⟩ => .quotientFirst
  | ⟨3, _⟩ => .quotientSecond
  | ⟨4, _⟩ => .remainderFirst
  | _ => .remainderSecond

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

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
open PCP.ExpanderTables PCP.ExpanderRowControl

@[simp] theorem dirtyTape_zero : dirtyTape 0 = .queryIndex := rfl
@[simp] theorem dirtyTape_one : dirtyTape 1 = .lookupOutput := rfl
@[simp] theorem dirtyTape_two : dirtyTape 2 = .quotientFirst := rfl
@[simp] theorem dirtyTape_three : dirtyTape 3 = .quotientSecond := rfl
@[simp] theorem dirtyTape_four : dirtyTape 4 = .remainderFirst := rfl
@[simp] theorem dirtyTape_five : dirtyTape 5 = .remainderSecond := rfl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update base (ports .queryIndex) [])
            (ports .lookupOutput) [])
          (ports .quotientFirst) [])
        (ports .quotientSecond) [])
      (ports .remainderFirst) [])
    (ports .remainderSecond) []

@[simp] theorem cleanupTapes_dirty (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (i : Fin 6) :
    cleanupTapes ports base (ports (dirtyTape i)) = [] := by
  fin_cases i <;>
    simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .table) = base (ports .table) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_inputVertex (ports : Tape → K)
    (distinct : Function.Injective ports) (base : K → List Bool) :
    cleanupTapes ports base (ports .inputVertex) = base (ports .inputVertex) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_output (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .output) = base (ports .output) := by
  simp [cleanupTapes, distinct.eq_iff]

variable [Fintype ρ] {d : Nat}

def initializedTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (ports .quotientFirst) (false :: base (ports .quotientFirst)))
        (ports .quotientSecond) (false :: base (ports .quotientSecond)))
      (ports .remainderFirst) (false :: base (ports .remainderFirst)))
    (ports .remainderSecond) (false :: base (ports .remainderSecond))

def clearedQueryTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update base (ports .queryIndex) (base (ports .queryIndex)).tail)
    (ports .lookupOutput) (base (ports .lookupOutput)).tail

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineExpanderRowDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The two actual division phases of the expander-row program. Static state
conjugation connects the fixed-divisor machine to the common emitter state.
Only the concrete statement placement equations are premises; no phase trace
or whole-row execution is assumed. Each phase has exactly `n + 2` transitions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

@[simp] theorem divisionStates_apply (ρ : Type) (d : Nat)
    (s : MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d)) :
    divisionStates ρ d s = (((s.1.1.1, s.1.2), ()), s.2) := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

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
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev Position (d : Nat) := Fin (rowFactor d)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

inductive ExtraTape
  | remainingLevel | currentSize | unaryScratch | tableReverse
  deriving DecidableEq

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

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

/-- This one alphabet is already finite in the underlying machine record. -/
theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineProductFieldLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

/-- An actual finite coefficient list for every fixed natural polynomial.
No evaluation of an input is included in this static representation choice. -/
noncomputable def coefficients (p : Polynomial Nat) :
    {cs : List Nat // coefficientPolynomial cs = p} := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], rfl⟩
  · intro q a hq ha ih
    rcases ih with ⟨cs, hcs⟩
    cases cs with
    | nil =>
      refine ⟨[a], ?_⟩
      rw [← hcs]
      simp [coefficientPolynomial]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      rw [← hcs]
      simp only [coefficientPolynomial, Polynomial.C_add, add_assoc]
  · intro q hq ih
    rcases ih with ⟨cs, hcs⟩
    refine ⟨0 :: cs, ?_⟩
    simp only [coefficientPolynomial, Polynomial.C_0, add_zero, hcs]

noncomputable def highCoefficients (p : Polynomial Nat) : List Nat :=
  (coefficients p).val.reverse

noncomputable def width (p : Polynomial Nat) : Nat := (highCoefficients p).length

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

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

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

/-- A concrete logarithmic iteration count, including the zero input. -/
def rounds (n : Nat) : Nat := Nat.log2 n + 1

end UniqueGamesTheorem.Foundations.PCP.AmplificationIteration

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingOverlayTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

/-- Old ports precede expander ports. -/
def overlayPorts (d e : Nat) : (Fin d ⊕ Fin e) ≃ Fin (d + e) := finSumFinEquiv

@[simp] theorem overlayPorts_inl_val (d e : Nat) (i : Fin d) :
    (overlayPorts d e (Sum.inl i)).val = i.val := rfl

@[simp] theorem overlayPorts_inr_val (d e : Nat) (i : Fin e) :
    (overlayPorts d e (Sum.inr i)).val = d + i.val := rfl

/-- False/stay ports occupy rows `0,...,d-1`; true/move ports occupy
rows `d,...,2*d-1`, before the vertex offset is added. -/
def lazyPorts (d : Nat) : (Bool × Fin d) ≃ Fin (2 * d) :=
  (Equiv.prodCongr finTwoEquiv.symm (Equiv.refl (Fin d))).trans finProdFinEquiv

@[simp] theorem lazyPorts_false_val (d : Nat) (i : Fin d) :
    (lazyPorts d (false, i)).val = i.val := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

@[simp] theorem lazyPorts_true_val (d : Nat) (i : Fin d) :
    (lazyPorts d (true, i)).val = i.val + d := by
  simp [lazyPorts, finTwoEquiv, finProdFinEquiv]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables

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

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Port := ExpanderFamily.Port ⊕ Unit

end UniqueGamesTheorem.Foundations.PCP.Regularization

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_VertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CloudRounding.copied_satisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PortTables.baseGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VertexPadding

open scoped BigOperators

variable {V D A : Type*}

/-- Original darts use the original reversal; dummy darts stay fixed. -/
def reverseFunction (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (V ⊕ Fin extra) × D → (V ⊕ Fin extra) × D
  | (Sum.inl v, d) => (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2)
  | (Sum.inr w, d) => (Sum.inr w, d)

theorem reverseFunction_involutive (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    Function.Involutive (reverseFunction G extra) := by
  rintro ⟨v | w, d⟩
  · change (Sum.inl (G.reverse (G.reverse (v, d))).1,
      (G.reverse (G.reverse (v, d))).2) = (Sum.inl v, d)
    rw [G.reverse_involutive]
  · rfl

/-- Actual regular padding by an arbitrary finite number of dummy vertices. -/
def pad (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    ConstraintGraph (V ⊕ Fin extra) ((V ⊕ Fin extra) × D) A where
  reverse := {
    toFun := reverseFunction G extra
    invFun := reverseFunction G extra
    left_inv := reverseFunction_involutive G extra
    right_inv := reverseFunction_involutive G extra }
  reverse_involutive := reverseFunction_involutive G extra
  tail := Prod.fst
  accepts := fun e a b => match e.1 with
    | Sum.inl v => G.accepts (v, e.2) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v | w, d⟩ a b
    · change G.accepts (G.reverse (v, d)) b a = G.accepts (v, d) a b
      exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem pad_tail (G : ConstraintGraph V (V × D) A) (extra : ℕ) :
    (pad G extra).tail = Prod.fst := rfl

@[simp] theorem pad_reverse_inl (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (v : V) (d : D) :
    (pad G extra).reverse (Sum.inl v, d) =
      (Sum.inl (G.reverse (v, d)).1, (G.reverse (v, d)).2) := rfl

@[simp] theorem pad_reverse_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (w : Fin extra) (d : D) :
    (pad G extra).reverse (Sum.inr w, d) = (Sum.inr w, d) := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (extra : ℕ) (labeling : V ⊕ Fin extra → A)
    (v : V) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inl v, d) =
      G.edgeSatisfied (fun v => labeling (Sum.inl v)) (v, d) := by
  change G.accepts (v, d) (labeling (Sum.inl v))
      (labeling (Sum.inl (G.reverse (v, d)).1)) =
    G.accepts (v, d) (labeling (Sum.inl (G.tail (v, d))))
      (labeling (Sum.inl (G.tail (G.reverse (v, d)))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A) (extra : ℕ)
    (labeling : V ⊕ Fin extra → A) (w : Fin extra) (d : D) :
    (pad G extra).edgeSatisfied labeling (Sum.inr w, d) = true := rfl

def extendLabeling (extra : ℕ) (defaultA : A) (labeling : V → A) : V ⊕ Fin extra → A :=
  Sum.elim labeling (fun _ => defaultA)

@[simp] theorem extendLabeling_inl (extra : ℕ) (defaultA : A) (labeling : V → A)
    (v : V) : extendLabeling extra defaultA labeling (Sum.inl v) = labeling v := rfl

@[simp] theorem extendLabeling_inr (extra : ℕ) (defaultA : A) (labeling : V → A)
    (w : Fin extra) : extendLabeling extra defaultA labeling (Sum.inr w) = defaultA := rfl

section FamilySize

variable (V : Type*) [Fintype V]

def extraVertices : ℕ := ExpanderFamily.size (Fintype.card V) - Fintype.card V

abbrev Vertex := V ⊕ Fin (extraVertices V)

theorem card_vertex : Fintype.card (Vertex V) = ExpanderFamily.size (Fintype.card V) := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_sub_of_le (ExpanderFamily.le_size _)

/-- Exact coordinate bridge to the proved geometric family. -/
noncomputable def familyVertexEquiv :
    Vertex V ≃ ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card V)) :=
  Fintype.equivOfCardEq (by
    rw [card_vertex, ExpanderFamily.card_vertex]
    rfl)

variable {V}

def paddedG (G : ConstraintGraph V (V × D) A) : ConstraintGraph (Vertex V) (Vertex V × D) A :=
  pad G (extraVertices V)

@[simp] theorem paddedG_tail (G : ConstraintGraph V (V × D) A) :
    (paddedG G).tail = Prod.fst := rfl

end FamilySize

end UniqueGamesTheorem.Foundations.PCP.VertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_Preprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

end UniqueGamesTheorem.Foundations.PCP.Preprocessing

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

namespace UniqueGamesTheorem.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss
def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2

end UniqueGamesTheorem.Foundations.PCP.FinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FoldedEquationLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.cubeXor_right_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AssignmentTester.flipAt_twice _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type}

/-- Left and right stored tables have disjoint variable names. -/
abbrev Address (i₀ : I) (j₀ : J) := HalfCube i₀ ⊕ HalfCube j₀

/-- Cancellation of the two copies of `g j₀` leaves this explicit RHS. -/
def rhsCorrection (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (μ : Cube J) : Bool := f i₀ ^^ f (π j₀) ^^ μ j₀

/-- One sampled test becomes exactly one three-occurrence equation. -/
def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

/-- Conditioned storage uses only satisfying-assignment coordinates, so identical
restricted canonical inputs are the same variable, even for distinct raw queries. -/
def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)

end UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

end

section

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

namespace UniqueGamesTheorem.Foundations.Hastad

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

/-- Rename the three occurrences without merging or dropping any occurrence. -/
def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

namespace EmptyContext

variable {I : Type}

/-- A left half-table address or the one dummy address. -/
abbrev Address (i₀ : I) := HalfCube i₀ ⊕ Unit

/-- The dummy appears twice. Its assigned bit cancels in the equation. -/
def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

/-- The two opposite queries give an explicit balanced list of equations. -/
def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl

end EmptyContext
end UniqueGamesTheorem.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_ExplicitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Realizing the existing Håstad noise law with a finite uniform tape

A tape contains one element of `Fin D` per coordinate. The corresponding noise
bit is true exactly when that element has value zero. For `D > 0`, its law is
exactly `Foundations.Hastad.noiseWeight ((D : ℝ)⁻¹)`.

The construction also permits an empty coordinate type and `D = 1`.
-/

namespace UniqueGamesTheorem.Reduction.FiniteNoise

open scoped BigOperators

def realizedBit {D : Nat} (z : Fin D) : Bool := decide (z.val = 0)

def realizedNoise {A : Type*} {D : Nat} (z : A → Fin D) : A → Bool :=
  fun a => realizedBit (z a)

end UniqueGamesTheorem.Reduction.FiniteNoise

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_HonestTestLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTape

open scoped BigOperators
open UniqueGamesTheorem.Reduction.FiniteNoise

/-- Two full Boolean query tables and one finite noise entry per right index. -/
abbrev TestTape (I J : Type*) (D : ℕ) :=
  Cube I × ((J → Fin D) × Cube J)

end UniqueGamesTheorem.Foundations.Hastad.SourceTape

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

/-- Old vertices occupy the initial interval and dummy vertices the final one. -/
def vertexEquiv (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

@[simp] theorem vertexEquiv_inl (h : n ≤ m) (v : Fin n) :
    vertexEquiv h (Sum.inl v) = v.castLE h := rfl

@[simp] theorem vertexEquiv_inr_val (h : n ≤ m) (v : Fin (m - n)) :
    (vertexEquiv h (Sum.inr v)).val = n + v.val := rfl

@[simp] theorem vertexEquiv_symm_old (h : n ≤ m) (v : Fin n) :
    (vertexEquiv h).symm (v.castLE h) = Sum.inl v :=
  (vertexEquiv h).symm_apply_apply (Sum.inl v)

/-- The port number is retained by the coordinate conversion. -/
def dartEquiv (h : n ≤ m) :
    (Fin n ⊕ Fin (m - n)) × Fin d ≃ Fin m × Fin d :=
  Equiv.prodCongr (vertexEquiv h) (Equiv.refl _)

@[simp] theorem dartEquiv_apply (h : n ≤ m)
    (v : Fin n ⊕ Fin (m - n)) (p : Fin d) :
    dartEquiv h (v, p) = (vertexEquiv h v, p) := rfl

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

/-- Dummy coordinates, in increasing original vertex and local index order. -/
def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

/-- Explicit list search/get indexing, with an erased cardinality cast. -/
def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

/-- Internal cloud ports precede the one inherited-constraint port. -/
def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables

/-!
# Exact serialized family tables at actual regularization vertices

The geometric family maps request zero to a one-vertex table. Empty clouds in
regularization instead remain empty. The bridge therefore requires positive
cloud size, derived here from each actual original or dummy vertex.
-/

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

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

end

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

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialTables

open GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (UniqueGamesTheorem.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := UniqueGamesTheorem.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := UniqueGamesTheorem.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (UniqueGamesTheorem.Integration.BinaryCoordinates.pack
      (UniqueGamesTheorem.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [UniqueGamesTheorem.Integration.BinaryCoordinates.pack_unpack]

end UniqueGamesTheorem.Foundations.PCP.RawInitialTables

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialRows

open GraphTables RawInitialTables

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

end UniqueGamesTheorem.Foundations.PCP.RawInitialRows

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

/-- Initialized fixed data keep enormous constant powers symbolic in the kernel.
The stored equality proves the exact requested parameter; no value is assumed. -/
opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

theorem dartFactor_positive (q : Nat) : 0 < AlphabetGraphBounds.dartFactor q := by
  unfold AlphabetGraphBounds.dartFactor AlphabetGraphBounds.localEventFactor
  positivity

end UniqueGamesTheorem.Foundations.PCP.RoundTables

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

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineModel

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceContextLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

open Turing UniqueGamesTheorem.Foundations.Complexity

inductive Tape (u : Nat) (Extra : Type)
  | formula | index | work | scratch | copyScratch
  | current (coordinate : Fin u) | remaining (coordinate : Fin u)
  | field (coordinate : Fin u) (slot : Fin 6)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceHeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

open Turing UniqueGamesTheorem.Foundations.Complexity

structure Layout (K : Type) where
  bits : K
  count : K
  accumulator : K
  bits_count : bits ≠ count
  bits_accumulator : bits ≠ accumulator
  count_accumulator : count ≠ accumulator

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceOccurrences
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

/-- A concrete, reversible finite encoding. Constructors below specify the
actual arithmetic; no arbitrary `Fintype.equivFin` is used. -/
structure Encoding (α : Type) where
  size : ℕ
  code : α ≃ Fin size

namespace Encoding

def fin (n : ℕ) : Encoding (Fin n) := ⟨n, Equiv.refl _⟩
def bool : Encoding Bool := ⟨2, finTwoEquiv.symm⟩
def unit : Encoding Unit := ⟨1, finOneEquiv.symm⟩

/-- The second component is the low-order block coordinate. -/
def prod {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α × β) :=
  ⟨a.size * b.size, (Equiv.prodCongr a.code b.code).trans finProdFinEquiv⟩

/-- The right summand follows the whole left block. -/
def sum {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α ⊕ β) :=
  ⟨a.size + b.size, (Equiv.sumCongr a.code b.code).trans finSumFinEquiv⟩

/-- Function coordinate zero is the least significant radix digit. -/
def function {α β : Type} (a : Encoding α) (b : Encoding β) : Encoding (α → β) where
  size := b.size ^ a.size
  code := (show (α → β) ≃ (Fin a.size → Fin b.size) from
    { toFun := fun f i => b.code (f (a.code.symm i))
      invFun := fun f x => b.code.symm (f (a.code x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro f; funext i; simp }).trans finFunctionFinEquiv

def enumerate {α : Type} (a : Encoding α) : List α := List.ofFn a.code.symm

@[simp] theorem length_enumerate {α : Type} (a : Encoding α) :
    a.enumerate.length = a.size := by simp [enumerate]

end Encoding

/-- Distinct table vertices and the three side tags never share storage.
Unused ambient query positions are harmless explicit padding. -/
abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((c.prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v c i j).size =
      v.size * 2 ^ i.size + (c.size * 2 ^ j.size + 1) := rfl

/-- Extending by false gives a unique padded address to a restricted query. -/
def extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) : Cube J :=
  fun j => if h : valid j = true then f ⟨j, h⟩ else false

@[simp] theorem extendRestricted_valid {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) (j : {j : J // valid j = true}) :
    extendRestricted valid f j.val = f j := by simp [extendRestricted, j.property]

@[simp] theorem restrictQuery_extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) :
    restrictQuery valid (extendRestricted valid f) = f := by
  funext j
  exact extendRestricted_valid valid f j

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def localAddress (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    FoldedEquation.Address i₀ j₀ → Fin (globalEncoding vE cE iE jE).size
  | .inl f => (globalEncoding vE cE iE jE).code (.inl (v, f.val))
  | .inr g => (globalEncoding vE cE iE jE).code (.inr (.inl (c, extendRestricted valid g.val)))

def conditionedOccurrence
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    Equation (Fin (globalEncoding vE cE iE jE).size) :=
  mapEquation (localAddress vE cE iE jE v c valid i₀ j₀)
    (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)

end LocalEquations

/-- A terminating first-valid search on the explicitly ordered ambient list. -/
def findValid {J : Type} (valid : J → Bool) : List J → Option {j : J // valid j = true}
  | [] => none
  | j :: rest => if h : valid j = true then some ⟨j, h⟩ else findValid valid rest

def firstValid {J : Type} (e : Encoding J) (valid : J → Bool) :
    Option {j : J // valid j = true} := findValid valid e.enumerate

/-- Mapping the ordered enumeration preserves all sampled occurrences. -/
def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool

def leftAnchor (u : ℕ) : I u := fun _ => false

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceLoopInitLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

open Turing UniqueGamesTheorem.Foundations.Complexity
open SourceMachine

inductive HeaderTape
  | variableCount | clauseCount
  deriving DecidableEq

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceHeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity

noncomputable section

def leftValue (u n : Nat) : Nat := 2 ^ (2 ^ u) * n ^ u
def rightValue (u m : Nat) : Nat := 2 ^ (8 ^ u) * m ^ u
def dummyValue (u n m : Nat) : Nat := leftValue u n + rightValue u m

inductive Kind
  | left | right | occurrences
  deriving DecidableEq

end

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceHonestLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inl_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.addressEquiv_inr_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_address _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_cube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_event _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_localEvent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_pairCube _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.inputCoordinateEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_edgeAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Enumeration.vertexEquiv_vertexAddress_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Queries.mask_idempotent _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.averagingOperator_cayleyGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cayleyGraph_rot _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.coefficient_zeroFrequency _root_.OAI.UniqueGamesTheorem.Foundations.PCP.CayleySpectral.cubeXor_zeroFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHonest

open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise
open scoped BigOperators

/-- Padded query tables are evaluated at one coordinate per context. Left and
right tables have disjoint tags, and the unused dummy bit is fixed to false. -/
def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl (c, g)) => g (right c)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl (c, g))) = g (right c) := rfl

open SourceContexts
open SourceOccurrences

end UniqueGamesTheorem.Foundations.Hastad.SourceHonest

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceQueryOrderLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences


inductive BodyWork (Extra : Type)
  | leftBlock | dummy | bitCount | occurrenceCount
  | zero | rank | rightBase | leftBase
  | accA | accB | counter | arithScratch | coefficient
  | queryTemporary | queryScratch | accumulator
  | extra (value : Extra)
  deriving DecidableEq, Fintype

abbrev BodyExtra (Extra : Type) := SourceLoopInit.HeaderTape ⊕ BodyWork Extra

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



end OAI
end


