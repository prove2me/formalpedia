-- Prove2me | Definitions.Def_OAIQ252P016
-- name    : OAIQ252P016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:53:20.349077+00:00
-- url     : https://prove2.me/theorems/8e472ec9-45c2-45c6-807f-e394d5c6d05b
-- title:
--   Definitions bundle OAIQ252P016 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 370 declarations of OpenAI's Lean: 153 definitions, 3 inductive types or structures, 3 instances and 211 theorems. The definitions and types are `OAI.PerfectCompleteness.ExactTargetOdometer.enumerateInTimeOfBound`, `OAI.PerfectCompleteness.ExactTargetOdometer.targetInTimePolynomial`, `OAI.PerfectCompleteness.ExtraCutCall.EnlargedRecord`, `OAI.PerfectCompleteness.ExtraCutCall.observationLaw`, `OAI.PerfectCompleteness.ExtraCutCall.splitAssembled`, `OAI.PerfectCompleteness.ExtraCutCall.splitRecord`, `OAI.PerfectCompleteness.FixedParameters.Parameters`, `OAI.PerfectCompleteness.FixedParameters.branch`, `OAI.PerfectCompleteness.FixedParameters.calls`, `OAI.PerfectCompleteness.FixedPreliminaryGame.value`, `OAI.PerfectCompleteness.FixedTarget.alphabet`, `OAI.PerfectCompleteness.FixedTarget.construct`, `OAI.PerfectCompleteness.NormalizationEmitMachine.Label`, `OAI.PerfectCompleteness.NormalizationEmitMachine.Labels`, `OAI.PerfectCompleteness.NormalizationEmitMachine.commandSteps`, `OAI.PerfectCompleteness.NormalizationEmitMachine.cost`, `OAI.PerfectCompleteness.NormalizationEmitMachine.emit`, `OAI.PerfectCompleteness.NormalizationEmitMachine.instruction`, `OAI.PerfectCompleteness.NormalizationEmitMachine.localInstruction`, `OAI.PerfectCompleteness.NormalizationEmitMachine.main`, `OAI.PerfectCompleteness.NormalizationEmitMachine.result`, `OAI.PerfectCompleteness.NormalizationEmitMachine.sequenceEntry`, `OAI.PerfectCompleteness.NormalizationEmitMachine.sequenceInstruction`, `OAI.PerfectCompleteness.NormalizationEmitMachine.steps`, `OAI.PerfectCompleteness.NormalizationLoopMachine.Label`, `OAI.PerfectCompleteness.NormalizationLoopMachine.afterDrain`, `OAI.PerfectCompleteness.NormalizationLoopMachine.bodySteps`, `OAI.PerfectCompleteness.NormalizationLoopMachine.instruction`, `OAI.PerfectCompleteness.NormalizationLoopMachine.nameSum`, `OAI.PerfectCompleteness.NormalizationLoopMachine.steps`, `OAI.PerfectCompleteness.NormalizationMachine.Label`, `OAI.PerfectCompleteness.NormalizationMachine.cfg`, `OAI.PerfectCompleteness.NormalizationMachine.computableInPolyTime`, `OAI.PerfectCompleteness.NormalizationMachine.machine`, `OAI.PerfectCompleteness.NormalizationMachine.outputsInTime`, `OAI.PerfectCompleteness.NormalizationMachine.program`, `OAI.PerfectCompleteness.NormalizationMachine.steps`, `OAI.PerfectCompleteness.NormalizationStream.blocks`, `OAI.PerfectCompleteness.NormalizationWords.bits`, `OAI.PerfectCompleteness.NormalizationWords.body` and 116 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Foundations_ExtraCutCall`, `PerfectCompleteness_Foundations_NormalizationLemmas`, `PerfectCompleteness_Foundations_OriginalWholeCut`, `PerfectCompleteness_Foundations_OriginalWholeCutBridge`, `PerfectCompleteness_Foundations_PCPSource`, `PerfectCompleteness_Foundations_SourceKeyBoundsLemmas`, `PerfectCompleteness_Machines_ExactTargetOdometer`, `PerfectCompleteness_Machines_NormalizationEmitMachine`, `PerfectCompleteness_Machines_NormalizationLoopMachine`, `PerfectCompleteness_Machines_NormalizationMachine`, `PerfectCompleteness_Machines_SignedRuntimeBounds`, `PerfectCompleteness_Reduction_FixedCallBudgetLemmas`, `PerfectCompleteness_Reduction_FixedTarget`, `PerfectCompleteness_Reduction_NormalizedTarget`, `PerfectCompleteness_Reduction_PreliminaryOutputLemmas`, `PerfectCompleteness_Sampling_NumberedUniformCut`, `PerfectCompleteness_Sampling_OriginalUniformCutBase`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_MachineLazyCodec`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLazyTable`, `UniqueGames_Machines_MachineLazyTableRuntime`, `UniqueGames_Machines_MachineOverlayTable`, `UniqueGames_Machines_MachinePaddedOverlay`, `UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularTableBoundsLemmas`, `UniqueGames_Machines_MachineRegularTableTrace`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_PCP_PreprocessingPaddingWords`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P012`, `OAIQ252P013` and `OAIQ252P014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P018` and `OAIQ252P019`.
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

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndex_encodeRaw _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NormalizationLoopMachine.stepAux_finish _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightEquiv_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.NormalizationWords


open UniqueGamesTheorem.Foundations
open Complexity

@[simp] theorem recipe_length : recipe.length = 39 := by decide

def words (signs : Signs) (names : Names) (freshBase : Nat) : List Nat :=
  recipe.flatMap (literalWords signs names freshBase)

def bits (signs : Signs) (names : Names) (freshBase : Nat) : List Bool :=
  encodeWords (words signs names freshBase)

def clauseSigns {n : Nat} (clause : Target.Clause n) : Signs := fun i => clause[i].positive

def clauseNames {n : Nat} (clause : Target.Clause n) : Names := fun i => clause[i].variableIndex.val

theorem bits_eq_flatMap (signs : Signs) (names : Names) (freshBase : Nat) :
    bits signs names freshBase = recipe.flatMap (literalBits signs names freshBase) :=
  encodeWords_flatMap _ _

theorem gadget_words (formula : Target.Formula) (c : Fin formula.clauses.length) :
    (Normalization.gadgetClauses formula c).flatMap Complexity.clauseWords =
      words (clauseSigns (PCP.clauseAt formula c)) (clauseNames (PCP.clauseAt formula c))
        (formula.variables + 4 * c.val) := by
  simp [Normalization.gadgetClauses, Normalization.gadget, Normalization.mainClause,
    Normalization.equalityClauses, Normalization.normalizedTriple, Normalization.tripleClause,
    Normalization.copyVariable, Normalization.freshVariable, Normalization.oldVariable,
    Normalization.paddingVariable, Complexity.clauseWords, Complexity.literalWords,
    words, recipe, mainRecipe, equalityRecipe, literalWords, nameValue, sourceValue, offset,
    signValue, clauseSigns, clauseNames, Fin.getElem_fin]
  exact ⟨rfl, rfl, rfl⟩

theorem gadget_bits (formula : Target.Formula) (c : Fin formula.clauses.length) :
    encodeWords ((Normalization.gadgetClauses formula c).flatMap Complexity.clauseWords) =
      bits (clauseSigns (PCP.clauseAt formula c)) (clauseNames (PCP.clauseAt formula c))
        (formula.variables + 4 * c.val) := by
  rw [gadget_words]
  rfl

def body (formula : Target.Formula) : List Bool :=
  (PCP.allIndices formula).flatMap (fun c =>
    bits (clauseSigns (PCP.clauseAt formula c)) (clauseNames (PCP.clauseAt formula c))
      (formula.variables + 4 * c.val))

theorem encoded_body (formula : Target.Formula) :
    encodeWords ((Normalization.normalize formula).clauses.flatMap Complexity.clauseWords) =
      body formula := by
  change encodeWords (((PCP.allIndices formula).flatMap
    (Normalization.gadgetClauses formula)).flatMap Complexity.clauseWords) = _
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [gadget_bits, body]

theorem encoded_normalize (formula : Target.Formula) :
    formulaBits (Normalization.normalize formula) =
      encodeWord (formula.variables + 4 * formula.clauses.length) ++
        encodeWord (13 * formula.clauses.length) ++ body formula := by
  have count : (Normalization.normalize formula).clauses.length =
      13 * formula.clauses.length := Normalization.normalize_clause_count formula
  simp only [formulaBits, formulaWords, encodeWords_append, encodeWords, List.append_nil,
    Normalization.normalize_variables, List.append_assoc]
  erw [count, encoded_body]

end PerfectCompleteness.NormalizationWords



namespace PerfectCompleteness.NormalizationStream

open UniqueGamesTheorem.Foundations Complexity NormalizationWords

def blocks {n : Nat} (freshBase : Nat) : List (Target.Clause n) → List Bool
  | [] => []
  | clause :: clauses =>
      bits (clauseSigns clause) (clauseNames clause) freshBase ++ blocks (freshBase + 4) clauses

theorem blocks_eq_finRange {n : Nat} (clauses : List (Target.Clause n)) (freshBase : Nat) :
    blocks freshBase clauses = (List.finRange clauses.length).flatMap (fun i =>
      bits (clauseSigns clauses[i.val]) (clauseNames clauses[i.val]) (freshBase + 4 * i.val)) := by
  induction clauses generalizing freshBase with
  | nil => simp [blocks]
  | cons clause clauses ih =>
      simp only [blocks, List.length_cons, List.finRange_succ, List.flatMap_cons,
        List.flatMap_map, List.getElem_cons_zero, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
      apply congrArg (fun tail => bits (clauseSigns clause) (clauseNames clause) freshBase ++ tail)
      rw [ih]
      apply List.flatMap_congr
      intro i _
      have address : freshBase + 4 + 4 * i.val = freshBase + 4 * (i.val + 1) := by omega
      simp only [Fin.val_succ, List.getElem_cons_succ, address]

theorem body_eq_blocks (formula : Target.Formula) :
    NormalizationWords.body formula = blocks formula.variables formula.clauses := by
  rw [blocks_eq_finRange]
  rfl

theorem encoded_normalize (formula : Target.Formula) :
    formulaBits (Normalization.normalize formula) =
      encodeWord (formula.variables + 4 * formula.clauses.length) ++
        encodeWord (13 * formula.clauses.length) ++ blocks formula.variables formula.clauses := by
  rw [NormalizationWords.encoded_normalize, body_eq_blocks]

theorem blocks_length_le {n : Nat} (clauses : List (Target.Clause n)) (freshBase : Nat)
    (bound : Nat) (oldBound : n ≤ bound) (freshBound : freshBase + 4 * clauses.length ≤ bound) :
    (blocks freshBase clauses).length ≤ clauses.length * (39 * (bound + 3)) := by
  have literalBound (names : Names) (fresh : Nat) (signs : Signs)
      (hn : ∀ i, names i ≤ bound) (hf : fresh + 3 ≤ bound) (literal : LiteralRecipe) :
      (literalBits signs names fresh literal).length ≤ bound + 3 := by
    have nameBound : nameValue names fresh literal.name ≤ bound := by
      cases h : literal.name with
      | old i => simpa [nameValue, sourceValue, offset, h] using hn i
      | fresh i =>
          have hi := i.isLt
          simp only [nameValue, sourceValue, offset]
          omega
    cases h : signValue signs literal.sign <;>
      simp [literalBits, NormalizationWords.literalWords, h] <;> omega
  have gadgetBound (clause : Target.Clause n) (fresh : Nat) (hf : fresh + 3 ≤ bound) :
      (bits (clauseSigns clause) (clauseNames clause) fresh).length ≤ 39 * (bound + 3) := by
    rw [bits_eq_flatMap]
    have listBound (commands : List LiteralRecipe) :
        (commands.flatMap (literalBits (clauseSigns clause) (clauseNames clause) fresh)).length ≤
          commands.length * (bound + 3) := by
      induction commands with
      | nil => simp
      | cons command commands ih =>
          have hc := literalBound (clauseNames clause) fresh (clauseSigns clause)
            (fun i => Nat.le_trans (clause[i].variableIndex.isLt.le) oldBound) hf command
          simp only [List.flatMap_cons, List.length_append, List.length_cons,
            Nat.add_mul, Nat.one_mul]
          omega
    simpa only [recipe_length] using listBound recipe
  induction clauses generalizing freshBase with
  | nil => simp [blocks]
  | cons clause clauses ih =>
      have head := gadgetBound clause freshBase (by simp only [List.length_cons] at freshBound; omega)
      have tail := ih (freshBase + 4) (by simp only [List.length_cons] at freshBound; omega)
      simp only [blocks, List.length_append, List.length_cons]
      nlinarith

end PerfectCompleteness.NormalizationStream

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFLoopLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
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

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

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

/-- The actual padded row codec is the old row codec followed by the emitted suffix. -/
theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact dummy-block codec used by the complete lazy-table machine. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowBits_stay {n d : Nat} (v : Fin n) (p : Fin d) :
    MachineDummyRows.rowBits v.val (2 * d * v.val + p.val) =
      encodeWords (rowWords (stayRow d v p)) := by
  have h := MachineDummyRows.rowBits_eq_graph_row v (stayRow d v p).reverseIndex
  rw [stayRow_reverse_val] at h
  exact h

theorem rowsBits_stay {n d : Nat} (v : Fin n) :
    MachineDummyRows.rowsBits v.val (2 * d * v.val) d =
      encodeWords ((List.ofFn (stayRow d v)).flatMap rowWords) := by
  rw [rowsBits_ofFn, encodeWords_flatMap]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext p
  exact rowBits_stay v p

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyCodec

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyRows
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

/-- Every port executes its actual loader, mapper, emitter, and cleanup.
The trace is proved from the concrete program, with no per-row run premise. -/
theorem vertexSuffixTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A)
    (remaining : Nat) (i : Fin (d + 1)) (count : i.val + remaining = d) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b ((List.ofFn rows).drop i.val) output]
      (some ⟨some (labels (i, none)), streamClean d positive ambient,
        streamFrame tape base ((List.ofFn rows).drop i.val) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b ((List.ofFn rows).drop i.val))⟩ := by
  have hd (a k : Fin 10) (h : a ≠ k) : tape a ≠ tape k := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = d := by omega
      have hdrop : (List.ofFn rows).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, recordsOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < d := by omega
      let port : Fin d := ⟨i.val, hi⟩
      let next : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn rows).drop (i.val + 1)
      have split : (List.ofFn rows).drop i.val = rows port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn rows)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (rows port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), streamClean d positive ambient, initial⟩) =
          some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := streamRowTrace d positive c b tape distinct
        (fun stage => labels (i, some stage)) (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using (atLabels (i, some stage)))
        initial (rows port).tail.val (rows port).reverseIndex.val (rows port).relation
        (recordsInput rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 9 7 (by decide), recordsInput, List.append_assoc])
        (by
          intro k hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[streamRowSteps d c b
        (rows port).tail.val (rows port).reverseIndex.val (rows port).relation output]
        (some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
            (rows port).relation tape initial (recordsInput rest ++ base (tape 9))⟩ at body
      rw [show streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
        (rows port).relation tape initial (recordsInput rest ++ base (tape 9)) =
        streamFrame tape base rest
          (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) from
          streamFrame_afterRow d c b (rows port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = d := by dsimp [next]; omega
      have tail := ih next nextCount
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)
      change (advance (TM2.step program))^[vertexSteps d c b rest
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)]
        (some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamFrame tape base rest (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation)⟩) =
        some ⟨exit, streamClean d positive ambient,
          streamFrame (n := n) (m := m) tape base [] ((output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) ++ recordsOutput d c b rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, recordsOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b (List.ofFn rows) output]
      (some ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base [] (output ++ recordsOutput d c b (List.ofFn rows))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d positive c b tape distinct
    labels exit program atLabels base rows empty ambient d 0 (by simp) output

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyTable
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.initialExtra_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.leftMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rightMatches_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.rowBits_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTableLayout.vertexRows_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.edgeSatisfied_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_new _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords.vertexBits_pad_old _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def program (d : Nat) (positive : 0 < d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State d)
  | .split label => MachineCloudPadding.Placement.statement splitRoles Label.split
      (some .dartSeed) (MachineTableSplit.program label)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .darts .scratch .output 2 .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt .scratch .darts id false
      .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .vertices .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt .scratch .vertices id false
      .vertexRestore (some .fuelFirst)
  | .fuelFirst => Reduction.MachineTransfer.loopAt .vertices .scratch id false
      .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop .scratch .vertices .fuel false
      .fuelSecond (some .seedCounters)
  | .seedCounters => .push .vertex (fun _ => false)
      (.push .reverse (fun _ => false) (.goto fun _ => .guard))
  | .guard => MachineUnaryCounter.guard .fuel .copyVertexFirst .clearVertices
  | .copyVertexFirst => Reduction.MachineTransfer.loopAt .vertex .scratch id false
      .copyVertexFirst (some .copyVertexSecond)
  | .copyVertexSecond => MachineCopy.forkLoop .scratch .vertex .tail false
      .copyVertexSecond (some (.dummy (MachineDummyRows.start d)))
  | .dummy label => MachineCloudPadding.Placement.statement dummyRoles Label.dummy
      (some .clearDummyTail) (MachineDummyRows.program d label)
  | .clearDummyTail => MachineDrain.drain .tail .clearDummyTail (some .clearDummyRelation)
  | .clearDummyRelation => MachineDrain.drain .relation .clearDummyRelation (some (.oldRows (0, none)))
  | .oldRows label => MachineLazyRows.vertexInstruction d positive (2 * d) d oldRoles
      Label.oldRows (some .nextVertex) label
  | .nextVertex => pushWord .reverse (List.replicate d true)
      (.push .vertex (fun _ => true) (.goto fun _ => .guard))
  | .clearVertices => MachineDrain.drain .vertices .clearVertices (some .clearDarts)
  | .clearDarts => MachineDrain.drain .darts .clearDarts (some .clearFuel)
  | .clearFuel => MachineDrain.drain .fuel .clearFuel (some .clearVertex)
  | .clearVertex => MachineDrain.drain .vertex .clearVertex (some .clearReverse)
  | .clearReverse => MachineDrain.drain .reverse .clearReverse none

/-- Lift the actual dummy-block routine into the full program and account for
the exact preserved frame. The tail and relation are cleared in the next phase. -/
theorem dummyTrace (d : Nat) (positive : 0 < d) (base : Tape → List Bool) (v e : Nat)
    (ht : base .tail = encodeWord v) (he : base .reverse = encodeWord e)
    (hr : base .relation = []) (hb : base .rowBuffer = []) (hs : base .scratch = []) :
    (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v e (base .output) d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, base⟩) =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
          .relation MachineDummyRows.trueBits)
          .output (base .output ++ MachineDummyRows.rowsBits v e d)⟩ := by
  have initial : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.initialTapes v e (base .output)) base = base := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes, ht, he, hr, hb, hs]
  have final : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.fieldTapes v (e + d) (base .output ++ MachineDummyRows.rowsBits v e d))
      base = Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
        .relation MachineDummyRows.trueBits)
        .output (base .output ++ MachineDummyRows.rowsBits v e d) := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.fieldTapes, ht, hb, hs]
  have run := MachineCloudPadding.Placement.trace dummyRoles dummyView
    dummyRoles_left dummyRoles_right Label.dummy (some .clearDummyTail) base
    (MachineDummyRows.program d) (program d positive) (fun _ => rfl) _ _ _
    (MachineDummyRows.allTrace d v e (base .output) (clean d positive).1 none)
  simpa only [clean_pair, MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, initial, final] using run

theorem oldTrace {n m : Nat} (d : Nat) (positive : 0 < d)
    (base : Tape → List Bool) (rows : Fin d → GraphTables.DartRow n m) (rest : List Bool)
    (hi : base .source = MachineLazyRows.recordsInput (List.ofFn rows) ++ rest)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (oldRoles i) = []) :
    (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (base .output)]
      (some ⟨some (.oldRows (0, none)), clean d positive, base⟩) =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update base .source rest) .output
          (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows))⟩ := by
  let tailBase := Function.update base Tape.source rest
  have cleanBase : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → tailBase (oldRoles i) = [] := by
    intro i h7 h9
    have hn : oldRoles i ≠ Tape.source := by
      intro h
      have h' : oldRoles i = oldRoles 9 := h
      exact h9 (oldRoles_injective h')
    simpa only [tailBase, Function.update_of_ne hn] using empty i h7 h9
  have initial : MachineLazyRows.streamFrame oldRoles tailBase (List.ofFn rows) (base .output) = base := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, tailBase, oldRoles, hi]
  have final : MachineLazyRows.streamFrame (n := n) (m := m) oldRoles tailBase []
      (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) =
      Function.update (Function.update base .source rest) .output
        (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, MachineLazyRows.recordsInput, tailBase, oldRoles]
  have run := MachineLazyRows.vertexTrace d positive (2 * d) d oldRoles oldRoles_injective
    Label.oldRows (some .nextVertex) (program d positive) (fun _ => rfl)
    tailBase rows cleanBase () (base .output)
  simpa only [initial, final, clean] using run

theorem prefixTrace (d : Nat) (positive : 0 < d) (n m : Nat) (rows : List Bool) :
    (advance (TM2.step (program d positive)))^[prefixSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive,
        initialTapes (encodeWords [n, m] ++ rows)⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d (encodeWords [n, m] ++ rows) n m n 0 rows (encodeWords [n, 2 * m])⟩ := by
  let word := encodeWords [n, m] ++ rows
  let header := encodeWords [n, 2 * m]
  let b₁ := frame word rows [] (encodeWord n) (encodeWord m) [] [] []
  let b₂ := frame word rows (encodeWord (2 * m)) (encodeWord n) (encodeWord m) [] [] []
  let b₃ := frame word rows header (encodeWord n) (encodeWord m) [] [] []
  let b₄ := frame word rows header (encodeWord n) (encodeWord m) (encodeWord n) [] []
  have hstart : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.initialTapes word) (fun _ => []) = initialTapes word := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.initialTapes, MachineTableSplit.tapes, initialTapes, frame]
  have hend : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.resultTapes n m rows) (fun _ => []) = b₁ := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.resultTapes, MachineTableSplit.tapes, b₁, frame, word]
  have split := MachineCloudPadding.Placement.trace splitRoles splitView
    splitRoles_left splitRoles_right Label.split (some .dartSeed) (fun _ => [])
    MachineTableSplit.program (program d positive) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n m rows (clean d positive).1 none)
  have c₀ : (advance (TM2.step (program d positive)))^[MachineTableSplit.exactSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes word⟩) =
      some ⟨some .dartSeed, clean d positive, b₁⟩ := by
    simp only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label] at split
    rw [hstart, hend] at split
    simpa only [clean_pair] using split
  have hdart : Function.update b₁ Tape.output (encodeWord (2 * m + 0) ++ b₁ .output) = b₂ := by
    funext t; cases t <;> simp [b₁, b₂, frame]
  have dart := MachineUnaryAffineAt.seededAffineTrace Tape.darts .scratch .output
    (by decide) (by decide) (by decide) 2 0 .dartSeed .dartScan .dartRestore
    (some .vertexSeed) (program d positive) rfl rfl rfl b₁ m []
    (by simp [b₁, frame]) rfl (clean d positive).1 none
  have c₁ : (advance (TM2.step (program d positive)))^[2 * (m + 1) + 1]
      (some ⟨some .dartSeed, clean d positive, b₁⟩) =
      some ⟨some .vertexSeed, clean d positive, b₂⟩ := by
    simpa only [hdart, clean_pair] using dart
  have hv : Function.update b₂ Tape.output (encodeWord (1 * n + 0) ++ b₂ .output) = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, frame, header, encodeWords]
  have vertex := MachineUnaryAffineAt.seededAffineTrace Tape.vertices .scratch .output
    (by decide) (by decide) (by decide) 1 0 .vertexSeed .vertexScan .vertexRestore
    (some .fuelFirst) (program d positive) rfl rfl rfl b₂ n []
    (by simp [b₂, frame]) rfl (clean d positive).1 none
  have c₂ : (advance (TM2.step (program d positive)))^[2 * (n + 1) + 1]
      (some ⟨some .vertexSeed, clean d positive, b₂⟩) =
      some ⟨some .fuelFirst, clean d positive, b₃⟩ := by
    simpa only [hv, clean_pair] using vertex
  have hf : Function.update b₃ Tape.fuel (b₃ .vertices ++ b₃ .fuel) = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have fuel := MachineCopy.copyTrace Tape.vertices .fuel .scratch
    (by decide) (by decide) (by decide) false .fuelFirst .fuelSecond
    (some .seedCounters) (program d positive) rfl rfl b₃ rfl (clean d positive).1 none
  rw [hf] at fuel
  have c₃ : (advance (TM2.step (program d positive)))^[2 * (n + 2)]
      (some ⟨some .fuelFirst, clean d positive, b₃⟩) =
      some ⟨some .seedCounters, clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .vertices = encodeWord n from rfl, encodeWord_length,
      Nat.add_assoc] using fuel
  have c₄ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .seedCounters, clean d positive, b₄⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d word n m n 0 rows header⟩ := by
    have ht : Function.update (Function.update b₄ Tape.vertex [false]) Tape.reverse [false] =
        loopTapes d word n m n 0 rows header := by
      funext t; cases t <;> simp [b₄, loopTapes, frame, encodeWord]
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄
  have hc : MachineTableSplit.exactSteps n m rows + (2 * (m + 1) + 1) +
      (2 * (n + 1) + 1) + 2 * (n + 2) + 1 = prefixSteps n m rows := by
    dsimp [MachineTableSplit.exactSteps, prefixSteps]
    omega
  rw [hc] at all
  exact all

/-- One entire vertex body: preserve-copy its tail, append the real dummy block,
clear its temporary fields, transform all old rows, and increment both counters
by actual pushes. The caller supplies no execution premise. -/
theorem bodyTrace {n m : Nat} (d : Nat) (positive : 0 < d) (input : List Bool)
    (left v : Nat) (rows : Fin d → GraphTables.DartRow n m) (rest output : List Bool) :
    (advance (TM2.step (program d positive)))^[bodySteps d v rows output]
      (some ⟨some .copyVertexFirst, clean d positive,
        loopTapes d input n m left v (MachineLazyRows.recordsInput (List.ofFn rows) ++ rest) output⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
  let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let moving := MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)
  let b₀ := loopTapes d input n m left v source output
  let b₁ := Function.update b₀ Tape.tail (encodeWord v)
  let b₄ := frame input source (output ++ dummy) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  let b₂ := Function.update (Function.update b₄ Tape.tail (encodeWord v))
    Tape.relation MachineDummyRows.trueBits
  let b₃ := Function.update b₄ Tape.relation MachineDummyRows.trueBits
  let b₅ := frame input rest ((output ++ dummy) ++ moving) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  have hcopy : Function.update b₀ Tape.tail (b₀ .vertex ++ b₀ .tail) = b₁ := by
    simp [b₀, b₁, loopTapes, frame]
  have copy := MachineCopy.copyTrace Tape.vertex .tail .scratch
    (by decide) (by decide) (by decide) false .copyVertexFirst .copyVertexSecond
    (some (.dummy (MachineDummyRows.start d))) (program d positive) rfl rfl b₀ rfl
    (clean d positive).1 none
  rw [hcopy] at copy
  have c₀ : (advance (TM2.step (program d positive)))^[2 * (v + 2)]
      (some ⟨some .copyVertexFirst, clean d positive, b₀⟩) =
      some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩ := by
    simpa only [clean_pair, show b₀ .vertex = encodeWord v from rfl, encodeWord_length,
      Nat.add_assoc] using copy
  have hdummy : Function.update (Function.update (Function.update b₁ Tape.reverse
      (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
      Tape.output (b₁ .output ++ dummy) = b₂ := by
    funext t; cases t <;> simp [b₀, b₁, b₂, b₄, loopTapes, frame]
  have dummies := dummyTrace d positive b₁ v (2 * d * v)
    (by simp [b₁]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame])
  have c₁ : (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v
      (2 * d * v) output d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩) =
      some ⟨some .clearDummyTail, clean d positive, b₂⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update b₁ Tape.reverse
          (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
          Tape.output (b₁ .output ++ dummy)⟩ at dummies
    rw [hdummy] at dummies
    simpa only [show b₁ .output = output by simp [b₁, b₀, loopTapes, frame]] using dummies
  have ht : Function.update b₂ Tape.tail [] = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, b₄, frame]
  have drainTail := MachineDrain.drainTrace Tape.tail .clearDummyTail (some .clearDummyRelation)
    (program d positive) rfl b₂ (b₂ .tail) (clean d positive).1 none
  simp only [Function.update_eq_self, ht] at drainTail
  have c₂ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearDummyTail, clean d positive, b₂⟩) =
      some ⟨some .clearDummyRelation, clean d positive, b₃⟩ := by
    simpa only [clean_pair, show b₂ .tail = encodeWord v by simp [b₂], encodeWord_length,
      Nat.add_assoc] using drainTail
  have hr : Function.update b₃ Tape.relation [] = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have drainRelation := MachineDrain.drainTrace Tape.relation .clearDummyRelation
    (some (.oldRows (0, none))) (program d positive) rfl b₃ (b₃ .relation)
    (clean d positive).1 none
  simp only [Function.update_eq_self, hr] at drainRelation
  have c₃ : (advance (TM2.step (program d positive)))^[8193]
      (some ⟨some .clearDummyRelation, clean d positive, b₃⟩) =
      some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .relation = MachineDummyRows.trueBits by simp [b₃],
      MachineDummyRows.trueBits_length] using drainRelation
  have hmoving : Function.update (Function.update b₄ Tape.source rest) Tape.output
      (b₄ .output ++ moving) = b₅ := by
    funext t; cases t <;> simp [b₄, b₅, frame]
  have old := oldTrace d positive b₄ rows rest rfl
    (fun i h7 h9 => frame_old_empty _ _ _ _ _ _ _ _ i h7 h9)
  have c₄ : (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (output ++ dummy)]
      (some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩) =
      some ⟨some .nextVertex, clean d positive, b₅⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update b₄ Tape.source rest) Tape.output
          (b₄ .output ++ moving)⟩ at old
    rw [hmoving] at old
    exact old
  have c₅ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .nextVertex, clean d positive, b₅⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
    have hrev : List.replicate d true ++ encodeWord (2 * d * v + d) =
        encodeWord (2 * d * (v + 1)) := by
      have hw := MachineUnaryAffineAt.prepend_replicate_word d (2 * d * v + d) []
      simp only [List.append_nil] at hw
      rw [hw]
      exact congrArg encodeWord (show d + (2 * d * v + d) = 2 * d * (v + 1) by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have ht : Function.update (Function.update b₅ Tape.reverse
        ((List.replicate d true).reverse ++ b₅ .reverse)) Tape.vertex (true :: b₅ .vertex) =
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows) := by
      funext t
      cases t <;> simp [b₅, frame, loopTapes, vertexBlock, dummy, moving,
        hrev, List.append_assoc]
      simp [encodeWord, List.replicate_succ]
    simp only [Function.iterate_one, advance_some, TM2.step, program,
      stepAux_pushWord, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  exact all

theorem drainPhase (d : Nat) (positive : 0 < d) (tape : Tape) (label : Label d)
    (exit : Option (Label d))
    (atLabel : program d positive label = MachineDrain.drain tape label exit)
    (base : Tape → List Bool) :
    (advance (TM2.step (program d positive)))^[(base tape).length + 1]
      (some ⟨some label, clean d positive, base⟩) =
      some ⟨exit, clean d positive, Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self, clean_pair] using
    MachineDrain.drainTrace tape label exit (program d positive) atLabel base
      (base tape) (clean d positive).1 none

theorem finishTrace (d : Nat) (positive : 0 < d) (input output : List Bool) (n m v : Nat) :
    (advance (TM2.step (program d positive)))^[finishSteps d n m v]
      (some ⟨some .guard, clean d positive, loopTapes d input n m 0 v [] output⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
  let b₀ := loopTapes d input n m 0 v [] output
  let b₁ := Function.update b₀ Tape.vertices []
  let b₂ := Function.update b₁ Tape.darts []
  let b₃ := Function.update b₂ Tape.fuel []
  let b₄ := Function.update b₃ Tape.vertex []
  have hframe : MachineUnaryCounter.counterTapes Tape.fuel b₀ 0 [] = b₀ := by
    funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
  have guard := MachineUnaryCounter.guardTrace_zero Tape.fuel .guard .copyVertexFirst
    .clearVertices (program d positive) rfl b₀ [] (clean d positive).1 none
  have c₀ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .guard, clean d positive, b₀⟩) =
      some ⟨some .clearVertices, clean d positive, b₀⟩ := by
    simpa only [hframe, clean_pair] using guard
  have c₁ : (advance (TM2.step (program d positive)))^[n + 2]
      (some ⟨some .clearVertices, clean d positive, b₀⟩) =
      some ⟨some .clearDarts, clean d positive, b₁⟩ := by
    simpa only [show b₀ .vertices = encodeWord n from rfl, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertices .clearVertices (some .clearDarts) rfl b₀
  have c₂ : (advance (TM2.step (program d positive)))^[m + 2]
      (some ⟨some .clearDarts, clean d positive, b₁⟩) =
      some ⟨some .clearFuel, clean d positive, b₂⟩ := by
    have hv : b₁ .darts = encodeWord m := by simp [b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .darts .clearDarts (some .clearFuel) rfl b₁
  have c₃ : (advance (TM2.step (program d positive)))^[2]
      (some ⟨some .clearFuel, clean d positive, b₂⟩) =
      some ⟨some .clearVertex, clean d positive, b₃⟩ := by
    have hv : b₂ .fuel = encodeWord 0 := by simp [b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length] using
      drainPhase d positive .fuel .clearFuel (some .clearVertex) rfl b₂
  have c₄ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearVertex, clean d positive, b₃⟩) =
      some ⟨some .clearReverse, clean d positive, b₄⟩ := by
    have hv : b₃ .vertex = encodeWord v := by simp [b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertex .clearVertex (some .clearReverse) rfl b₃
  have hend : Function.update b₄ Tape.reverse [] = finalTapes input output := by
    funext t; cases t <;> simp [b₄, b₃, b₂, b₁, b₀, loopTapes, finalTapes, frame]
  have c₅ : (advance (TM2.step (program d positive)))^[2 * d * v + 2]
      (some ⟨some .clearReverse, clean d positive, b₄⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
    have hv : b₄ .reverse = encodeWord (2 * d * v) := by
      simp [b₄, b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc, hend] using
      drainPhase d positive .reverse .clearReverse none rfl b₄
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  have hc : 1 + (n + 2) + (m + 2) + 2 + (v + 2) + (2 * d * v + 2) =
      finishSteps d n m v := by dsimp [finishSteps]; omega
  rw [hc] at all
  exact all

theorem vertexBlock_codec {n d : Nat} (table : PortTables.Table n d) (v : Fin n) :
    vertexBlock d v.val (PreprocessingLazyWords.row table v) =
      encodeWords ((PreprocessingLazyWords.vertexRows table v).flatMap GraphTables.rowWords) := by
  rw [vertexBlock, MachineLazyCodec.rowsBits_stay, MachineLazyRows.recordsOutput_lazy,
    PreprocessingLazyWords.vertexRows, List.flatMap_append, encodeWords_append]

theorem outputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    outputBlocks table events = encodeWords
      ((events.flatMap (PreprocessingLazyWords.vertexRows table)).flatMap GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [outputBlocks, vertexBlock_codec]

theorem output_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits (PreprocessingOverlayTables.lazy table) =
      encodeWords [n, 2 * (n * d)] ++ outputBlocks table (List.finRange n) := by
  rw [outputBlocks_codec, PreprocessingLazyWords.tableBits_lazy, encodeWords_append]
  have hm : n * (2 * d) = 2 * (n * d) := by ac_rfl
  have hrows : (List.ofFn (PreprocessingLazyWords.vertexRows table)).flatten =
      (List.finRange n).flatMap (PreprocessingLazyWords.vertexRows table) := by
    rw [List.ofFn_eq_map]
    rfl
  exact congrArg₂ List.append (congrArg (fun k => encodeWords [n, k]) hm)
    (congrArg (fun rows => encodeWords (rows.flatMap GraphTables.rowWords)) hrows)

/-- Induction over the actual unary fuel and the actual stored vertex order. -/
theorem loopTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d)
    (input : List Bool) (count r : Nat) (hsum : r + count = n) (output : List Bool) :
    (advance (TM2.step (program d positive)))^[loopSteps table r count output]
      (some ⟨some .guard, clean d positive,
        loopTapes d input n (n * d) count r (inputBlocks table (remaining n r)) output⟩) =
      some ⟨none, clean d positive,
        finalTapes input (output ++ outputBlocks table (remaining n r))⟩ := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    simpa only [loopSteps, remaining_done, inputBlocks, outputBlocks, List.flatMap_nil,
      List.append_nil] using finishTrace d positive input output n (n * d) n
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    let rest := inputBlocks table (remaining n (r + 1))
    let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
    let b₀ := loopTapes d input n (n * d) (count + 1) r source output
    let b₁ := loopTapes d input n (n * d) count r source output
    have hguard (k : Nat) : MachineUnaryCounter.counterTapes Tape.fuel b₀ k [] =
        loopTapes d input n (n * d) k r source output := by
      funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
    have guard := MachineUnaryCounter.guardTrace_succ Tape.fuel .guard .copyVertexFirst
      .clearVertices (program d positive) rfl b₀ count [] (clean d positive).1 none
    have c₀ : (advance (TM2.step (program d positive)))^[1]
        (some ⟨some .guard, clean d positive, b₀⟩) =
        some ⟨some .copyVertexFirst, clean d positive, b₁⟩ := by
      simpa only [hguard, clean_pair] using guard
    have c₁ := bodyTrace d positive input count r rows rest output
    have c₂ := ih (r + 1) (by omega) (output ++ vertexBlock d r rows)
    have all := joinTrace (joinTrace c₀ c₁) c₂
    have hi : inputBlocks table (remaining n r) = source := by
      rw [remaining_cons n r hr]
      rfl
    have ho : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    simpa only [loopSteps, dite_eq_left hr, hi, ho, List.append_assoc] using all

/-- The full table execution, including all headers, all dummy and moving
rows, and complete work-tape cleanup, in the existing exact Boolean codec. -/
theorem tableTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    (advance (TM2.step (program d positive)))^[totalSteps table]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes (PortTables.tableBits table)⟩) =
      some ⟨none, clean d positive,
        finalTapes (PortTables.tableBits table)
          (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩ := by
  have prefixRun := prefixTrace d positive n (n * d) (inputBlocks table (List.finRange n))
  rw [← input_table_codec table] at prefixRun
  have loop := loopTrace table positive (PortTables.tableBits table) n 0 (by omega)
    (encodeWords [n, 2 * (n * d)])
  simp only [remaining_zero] at loop
  have all := joinTrace prefixRun loop
  rw [← output_table_codec table] at all
  exact all

theorem totalSteps_le {n d : Nat} (table : PortTables.Table n d) :
    totalSteps table ≤ (timePolynomial d).eval (PortTables.tableBits table).length := by
  let L := (PortTables.tableBits table).length
  let N := L + 1
  let C := 1000000 * (d + 1) ^ 3
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have hout : (encodeWords [n, 2 * (n * d)] ++
      outputBlocks table (remaining n 0)).length ≤ 20000 * (L + 1) ^ 2 := by
    rw [remaining_zero, ← output_table_codec]
    exact output_length_le table
  have hl := loopSteps_le table L n 0 (by omega) hn hm _ hout
  have hp : prefixSteps n (n * d) (inputBlocks table (List.finRange n)) ≤ 10 * L + 17 := by
    unfold prefixSteps
    rw [← input_table_codec table]
    change 2 * L + 5 * n + 3 * (n * d) + 17 ≤ _
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnN : n ≤ N := by dsimp [N]; omega
  have hN2 : 1 ≤ N ^ 2 := by nlinarith only [hN]
  have hN3 : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N hN2
    nlinarith only [h]
  have hc := Nat.mul_le_mul_right (1 + C * N ^ 2) hnN
  change loopSteps table 0 n (encodeWords [n, 2 * (n * d)]) ≤ n * (1 + C * N ^ 2) + 5 * L + 11 at hl
  rw [timePolynomial_eval]
  change totalSteps table ≤ (C + 100) * N ^ 3
  unfold totalSteps
  have hLN : L + 1 = N := rfl
  nlinarith only [hp, hl, hc, hN, hN3, hLN]

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label d
  main := .split .copyFirst
  σ := State d
  initialState := clean d positive
  m := program d positive

theorem initial_configuration (d : Nat) (positive : 0 < d) (input : List Bool) :
    initList (machine d positive) input =
      ⟨some (.split .copyFirst), clean d positive, initialTapes input⟩ := by
  have ht : (initList (machine d positive) input).stk = initialTapes input := by
    funext t
    cases t <;> simp [initList, machine, initialTapes, frame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- A full actual finite-machine execution with a fixed-degree polynomial
budget, the exact lazy-table output, preserved original input, and clean work. -/
def machineInTime {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    StateTransition.EvalsToInTime (machine d positive).step
      (initList (machine d positive) (PortTables.tableBits table))
      (some ⟨none, clean d positive, finalTapes (PortTables.tableBits table)
        (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩)
      ((timePolynomial d).eval (PortTables.tableBits table).length) where
  steps := totalSteps table
  evals_in_steps := by
    rw [initial_configuration]
    exact tableTrace table positive
  steps_le_m := totalSteps_le table

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

/-- The terminal witness is the checked full lazy-table execution. The wrapper
then drains the retained original input rather than assuming it disappeared. -/
def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

/-- The actual canonical-output finite machine computes precisely the shared
degree-d to degree-2d stage map in polynomial time. -/
noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

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

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

def clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : AmbientState) : State AmbientState d e :=
  MachineLazyRows.streamClean d hd (a, MachineFixedDivMod.residue e he 0)

theorem expanderState_clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : AmbientState) :
    expanderState AmbientState d e (MachinePortReindex.clean e he
      ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0)) =
      clean d e hd he a := rfl

/-- Fixed degree control, including two actual independent working streams. -/
def mainInstruction (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    MainLabel d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State AmbientState d e)
  | .copyHFirst => Reduction.MachineTransfer.loopAt expanderArchive scratch id false
      (.inr .copyHFirst) (next .copyHSecond)
  | .copyHSecond => MachineCopy.forkLoop scratch expanderArchive expanderStream false
      (.inr .copyHSecond) (next .countSeed)
  | .countSeed => MachineUnaryAffineAt.seed output 0 (.inr .countScan)
  | .countScan => MachineUnaryAffineAt.scan vertexCount scratch output (d + e)
      (.inr .countScan) (.inr .countRestore)
  | .countRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .countRestore) (next .headerSeed)
  | .headerSeed => MachineUnaryAffineAt.seed output 0 (.inr .headerScan)
  | .headerScan => MachineUnaryAffineAt.scan vertexCount scratch output 1
      (.inr .headerScan) (.inr .headerRestore)
  | .headerRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .headerRestore) (next .fuelSeed)
  | .fuelSeed => MachineUnaryAffineAt.seed fuel 0 (.inr .fuelScan)
  | .fuelScan => MachineUnaryAffineAt.scan vertexCount scratch fuel 1
      (.inr .fuelScan) (.inr .fuelRestore)
  | .fuelRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .fuelRestore) (next .vertexSeed)
  | .vertexSeed => .push vertex (fun _ => false) (.goto fun _ => .inr .guard)
  | .guard => MachineUnaryCounter.guard fuel (.inr (.old (0, none))) (.inr .drainFuel)
  | .old stage => MachineLazyRows.vertexInstruction d hd (d + e) 0 oldTapes
      (fun stage => .inr (.old stage)) (next .tailSeed) stage
  | .tailSeed => MachineUnaryAffineAt.seed tail 0 (.inr .tailScan)
  | .tailScan => MachineUnaryAffineAt.scan vertex scratch tail 1
      (.inr .tailScan) (.inr .tailRestore)
  | .tailRestore => Reduction.MachineTransfer.loopAt scratch vertex id false
      (.inr .tailRestore) (next (.expander (0, none)))
  | .expander stage => MachineStateEquiv.statement (expanderState AmbientState d e)
      (MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage)
  | .drainTail => MachineDrain.drain tail (.inr .drainTail) (next .increment)
  | .increment => .push vertex (fun _ => true) (.goto fun _ => .inr .guard)
  | .drainFuel => MachineDrain.drain fuel (.inr .drainFuel) (next .drainVertex)
  | .drainVertex => MachineDrain.drain vertex (.inr .drainVertex) (next .drainVertexCount)
  | .drainVertexCount => MachineDrain.drain vertexCount (.inr .drainVertexCount) (next .drainDartCount)
  | .drainDartCount => MachineDrain.drain dartCount (.inr .drainDartCount) none

/-- The checked splitter is placed directly in five homogeneous Boolean
stacks, with its actual halt replaced by the next preparation label. -/
def program (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    Label d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State AmbientState d e)
  | .inl l => Placement.statement Sum.inl Sum.inl (next .copyHFirst)
      (MachineTableSplit.program l)
  | .inr l => mainInstruction d e hd he l

theorem graphRows_blocks {n d : Nat} (G : PortTables.Table n d) :
    MachineTableSplit.rowsBits (PortTables.graphTable G) = (List.ofFn (oldBlock G)).flatten := by
  change encodeWords ((PortTables.flatRows G).toList.flatMap rowWords) = _
  rw [PreprocessingLazyWords.flatRows_list, encodeWords_flatten_flatMap, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (MachineLazyRows.recordsInput_eq_codec (oldRows G v)).symm

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

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

def program {σ : Type} (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) (State σ)
  | .splitCode l => Placement.statement splitTape Label.splitCode (some (.powerCode .init))
      (MachineTableSplit.program l)
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .dartSeed)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .power .scratch .output d .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .power .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .vertexRestore (some .copyFirst)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .power .scratch id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .scratch .power .fuel false .copySecond (some (.subtractCode .subtract))
  | .subtractCode l => Placement.statement subtractTape Label.subtractCode
      (some (.rowsCode (.inr .initialize_))) (MachineCloudPadding.program l)
  | .rowsCode l => Placement.statement rowTape Label.rowsCode (some .cleanVertex) (rowProgram d hd l)
  | .cleanVertex => MachineDrain.drain .vertex .cleanVertex (some .cleanEdge)
  | .cleanEdge => MachineDrain.drain .edge .cleanEdge (some .cleanPower)
  | .cleanPower => MachineDrain.drain .power .cleanPower (some .cleanRelation)
  | .cleanRelation => MachineDrain.drain .relation .cleanRelation (some .cleanFuel)
  | .cleanFuel => MachineDrain.drain .fuel .cleanFuel none

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

def overlaySource (d : Nat) (hd : 0 < d) : MachineOverlayTable.Label d overlayDegree →
    TM2.Stmt (fun _ : MachineOverlayTable.Tape => Bool) (MachineOverlayTable.Label d overlayDegree) (State d) :=
  MachineStateEquiv.program (overlayStates d) (MachineStateFrame.frameProgram
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive))

def program (H : BaseTable) (d : Nat) (hd : 0 < d) :
    Label d → TM2.Stmt Alphabet (Label d) (State d)
  | .inl l => Placement.statement paddingTape paddingLabel (some familyEntry) (MachineVertexPadding.program d hd l)
  | .inr (.inl l) => Placement.statement familyTape familyLabel (some overlayEntry)
      (familySource H d l)
  | .inr (.inr l) => Placement.statement overlayTape overlayLabel none (overlaySource d hd l)

def clean (H : BaseTable) (d : Nat) (hd : 0 < d) : State d :=
  (((MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()), false), none)

/-- The second phase executes the checked family program from the already
materialized level. Its runtime is polynomial in the original vertex count. -/
noncomputable def familyInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some familyEntry, clean H d hd, paddedTapes t⟩
      (some ⟨some overlayEntry, clean H d hd, familyTapes H t⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  let o := MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()
  have caller : MachineExpanderFamily.caller f = () := Subsingleton.elim _ _
  have castRun := MachineAlphabetTransport.successfulExecutionInTime
    MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)
    (MachineExpanderFamily.paddedFamilyInTime H n f [])
  have boolRun : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [MachineExpanderFamily.boolView, MachineExpanderFamily.configuration_toBool,
      caller] using castRun
  have framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) ((o, false), (none : Option Bool)) boolRun
  have transported := MachineStateEquiv.execution (familyStates d)
    (MachineStateFrame.frameProgram
      (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (familySource H d))
      ⟨some (.inr .initialize_), clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [familySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, familyStates,
      Equiv.coe_fn_mk, clean, f, o]
      using transported
  have run := placeExecution familyTape familyView familyView_left familyView_right
    familyLabel (some overlayEntry) (paddedTapes t) (familySource H d) (program H d hd)
    (fun _ => rfl) sourceRun
  have finishRaw := family_final_memory H (PortTables.tableBits t)
    (PortTables.tableBits (padded t)) (PreprocessingLevels.boundedLevel n)
  have hsize : ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n) =
      PreprocessingLevels.paddedSize n := PreprocessingLevels.table_vertexCount_eq_paddedSize n
  have count : memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n)
      (encodeWord (ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n))) [] =
      familyTapes H t :=
    congrArg (fun size => memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n) (encodeWord size) []) hsize
  have finish := finishRaw.trans count
  simpa only [Placement.configuration, Placement.label, paddedTapes,
    family_initial_memory, finish, familyEntry] using run

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

def rawProgram (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .inl .original
  output := .inr (.inr MachineOverlayTable.output)
  main := MachinePaddedOverlay.main
  initial := MachinePaddedOverlay.clean H d hd
  code := MachinePaddedOverlay.program H d hd

theorem cleanup_complete (H : BaseTable) (d : Nat) (hd : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H d hd).output := by
  simp [cleanupTapes, rawProgram]

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

abbrev State := (FamilyState × Bool) × Option Bool

def stateEquiv : MachinePaddedExpanderFamily.State Unit ≃ State :=
  (Equiv.prodAssoc FamilyState Bool (Option Bool)).symm

def seedState (H : SmallTable) : FamilyState :=
  MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()

def readyState (H : SmallTable) : State := ((seedState H, false), none)

def sourceProgram (H : SmallTable) : MachinePaddedExpanderFamily.Label →
    TM2.Stmt (fun _ : NativeTape => Bool) MachinePaddedExpanderFamily.Label State :=
  MachineStateEquiv.program stateEquiv (MachinePaddedExpanderFamily.program (ρ := Unit) H)

/-- Every size-dependent operation is performed by the checked native program.
The entry load only resets the finite control state. -/
def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label State
  | .start => .load (fun _ => readyState H) (.goto fun _ => .family MachinePaddedExpanderFamily.main)
  | .family l => Placement.statement familyTape Label.family (some .drainPower) (sourceProgram H l)
  | .drainPower => MachineDrain.drain powerTape .drainPower (some .drainSize)
  | .drainSize => MachineDrain.drain sizeTape .drainSize (some .drainLevel)
  | .drainLevel => MachineDrain.drain levelTape .drainLevel none

@[simp] theorem source_initial_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.initialState (seedState H) none) =
      readyState H := rfl

@[simp] theorem source_final_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.finalState H (seedState H)) =
      readyState H := by
  simp [stateEquiv, MachinePaddedExpanderFamily.finalState, readyState, seedState]

/-- The actual native family run, including geometric-level computation. -/
noncomputable def familyInTime (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩
      (some ⟨some .drainPower, readyState H,
        working (resultCore H k core)
          (encodeWord (PCP.PreprocessingLevels.paddedSize k))
          (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0)⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length) := by
  let raw := MachinePaddedExpanderFamily.paddedInTime H k (seedState H) none
  let renamed := MachineStateEquiv.execution stateEquiv
    (MachinePaddedExpanderFamily.program (ρ := Unit) H) raw
  let placed := liftExecutionInTime (TM2.step (sourceProgram H)) (TM2.step (program H))
    (Placement.configuration familyView Label.family (some .drainPower) (frame core))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      Label.family (some .drainPower) (frame core) (sourceProgram H) (program H)
      (fun _ => rfl)) renamed
  simpa only [MachineStateEquiv.configuration, Placement.configuration, Placement.label,
    source_initial_state, source_final_state, initial_placement k core hinput houtput,
    final_placement H k core hinput] using placed

/-- Every retained private symbol is physically popped. -/
theorem cleanupTrace (H : SmallTable) (m : Nat) (core : CoreTape → List Bool) :
    (advance (TM2.step (program H)))^[2*m+6]
      (some ⟨some .drainPower, readyState H,
        working core (encodeWord m) (encodeWord m) (encodeWord 0)⟩) =
      some ⟨none, readyState H, frame core⟩ := by
  have first := (MachineDrain.drainInTime powerTape .drainPower (some .drainSize)
    (program H) rfl (working core (encodeWord m) (encodeWord m) (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  have second := (MachineDrain.drainInTime sizeTape .drainSize (some .drainLevel)
    (program H) rfl (working core [] (encodeWord m) (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  have third := (MachineDrain.drainInTime levelTape .drainLevel none
    (program H) rfl (working core [] [] (encodeWord 0))
    (seedState H, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, working_power, working_size, working_level,
    encodeWord_length, update_working_power, update_working_size,
    update_working_level, working_empty] at first second third
  have all := appendTrace _ (appendTrace _ first second) third
  have count : 2*m+6 = (m+1+1)+(m+1+1)+(0+1+1) := by omega
  rw [count]
  exact all

def cleanupInTime (H : SmallTable) (m : Nat) (core : CoreTape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .drainPower, readyState H,
        working core (encodeWord m) (encodeWord m) (encodeWord 0)⟩
      (some ⟨none, readyState H, frame core⟩) (2*m+6) where
  steps := 2*m+6
  evals_in_steps := cleanupTrace H m core
  steps_le_m := le_rfl

def startInTime (H : SmallTable) (core : CoreTape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program H .start) state (frame core)) = _
    rfl
  steps_le_m := le_rfl

/-- Complete clean-frame execution, from the caller's actual unary request.
No callback, table-construction premise, or caller-supplied runtime is assumed. -/
noncomputable def familyCleanInTime (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (hinput : core 4 = encodeWord k)
    (houtput : core 7 = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨none, readyState H, frame (resultCore H k core)⟩)
      (timePolynomial.eval (encodeWord k).length) := by
  let first := startInTime H core state
  let second := familyInTime H k core hinput houtput
  let third := cleanupInTime H (PCP.PreprocessingLevels.paddedSize k) (resultCore H k core)
  let pair := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ pair third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  exact all.steps_le_m.trans
    (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using totalBudget_le k)

@[simp] theorem result_output (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    frame (resultCore H k core) (.inl 7) = rotor H k := by simp [frame, resultCore]

@[simp] theorem result_private_empty (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (t : NativeTape) :
    frame (resultCore H k core) (.inr t) = [] := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
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

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

/-- The full old-vertex block uses every internal port, then physically copies
the original relation and reverse index. The output is the actual table block. -/
theorem originalTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[originalSteps t padding tables e output.length]
      (some ⟨some (labels (originalEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e)
          (output ++ PreprocessingRegularWords.originalVertexBits t padding tables e)⟩ := by
  let x := oldCloud t padding e
  let bits := (List.ofFn (rowBits t padding tables t.rows[e].tail x)).flatten
  have ports := portTrace q positive (fun l => labels (.originalPort l))
    (some (labels (.original (.row (.lookup .seed))))) program
    (fun l => code (.originalPort l)) t padding tables t.rows[e].tail x output ambient
  have inherited := originalCoreTrace q positive (fun l => labels (.original l)) exit program
    (fun l => code (.original l)) t e t.rows[e].tail.val
    (paddedCloudRank t padding t.rows[e].tail x).val (cloudSize t t.rows[e].tail)
    (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))) (output ++ bits) ambient
  rw [originalRowSteps_eq] at inherited
  change (advance (TM2.step program))^[originalRowSteps q t e (output ++ bits).length]
    (some ⟨some (labels (.original (.row (.lookup .seed)))), coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x (output ++ bits)⟩) =
    some ⟨exit, coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x
        ((output ++ bits) ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ at inherited
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e) := by
    have h := vertexBits_split t padding tables t.rows[e].tail x
    change PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inl e) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_original_words] at h
    exact h
  rw [hbits]
  simpa only [originalSteps, portEntry, dite_eq_left positive, originalEntry,
    List.length_append, List.append_assoc, x, bits] using total

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Regularization.graph_tail
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

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev FamilyState := MachineRegularFamily.State
abbrev State := (CoreState × MetaState) × FamilyState

def readyState (H : BaseTable) : State :=
  ((MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
    (((), false), none)), MachineRegularFamily.readyState H)

def familyTape : MachineRegularFamily.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inr e)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl i => some (.inl i)
  | .inr (.inl _) => none
  | .inr (.inr e) => some (.inr e)

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := by cases k <;> rfl

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h
    | inr e => cases h; rfl

def metadataStates : (MetaState × (CoreState × FamilyState)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × (CoreState × MetaState)) ≃ State := Equiv.prodComm _ _
def vertexStates : (CoreState × (MetaState × FamilyState)) ≃ State :=
  (Equiv.prodAssoc _ _ _).symm

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.family .start))
      metadataStates (MachineRegularMetadata.program l)
  | .family l => Lift.statement familyTape Label.family
      (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
      familyStates (MachineRegularFamily.program H l)
  | .vertex l => Lift.statement Sum.inl Label.vertex (clearEntry 0)
      vertexStates (vertexSource l)
  | .clear i => Lift.statement id (fun _ : Unit => .clear i) (clearEntry (i.val + 1))
      metadataStates (clearSource (clearTape i) ())

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

def familyData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { metadataData t e output with
    rotor := MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) }

def emittedData (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Data :=
  { familyData H t e output with output := output ++ emittedBits H t e }

/-- Genuine metadata trace transported with all other finite registers and
private family tapes preserved. -/
theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularMetadata.totalTime t e]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H (some (.family .start)) (metadataData t e output)) := by
  have raw := MachineRegularMetadata.originalTrace t e (initialData t e output)
    rfl rfl rfl rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.family .start)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) (frame (initialData t e output))
    MachineRegularMetadata.program (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem familyPlacement (data : Data) :
    MachineCloudPadding.Placement.tapes familyView (MachineRegularFamily.frame (coreFrame data))
      (frame data) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k (coreFrame data)))
      (frame data) = frame { data with rotor := MachineRegularFamily.rotor H k } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [MachineCloudPadding.Placement.tapes, familyView, MachineRegularFamily.frame,
        MachineRegularFamily.resultCore, coreFrame, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t t.rows[e].tail)
    (coreFrame (metadataData t e output)) rfl rfl (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) : Nat :=
  (familyExecution H t e output).steps

/-- Family work is performed on its physical tapes and produces the rotor
from the previously computed unary cloud size. -/
theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t e output]
      (some (cfg H (some (.family .start)) (metadataData t e output))) =
      some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output)) := by
  have raw := (familyExecution H t e output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
    familyStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      ((((), false), none) : MetaState)) (frame (metadataData t e output))
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familyData, familySteps, cfg, readyState,
    familyStates, Equiv.prodComm_apply, Prod.swap_prod_mk] using placed

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length + 1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val + 1), readyState H, Function.update base (clearTape i) []⟩ := by
  have raw := MachineDrain.drainTrace (clearTape i) () none (clearSource (clearTape i)) rfl
    base (base (clearTape i)) ((), false) none
  simp only [Function.update_eq_self] at raw
  have placed := Lift.trace id some (fun _ => rfl)
    (fun j k h => (Option.some.inj h).symm)
    (fun _ : Unit => Label.clear i) (clearEntry (i.val + 1)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) base (clearSource (clearTape i)) (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    identityPlacement, metadataStates, Equiv.coe_fn_mk, readyState] using placed

theorem clearPrefixTrace (H : BaseTable) (base : Tape → List Bool)
    (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[clearSteps base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, clearMemory base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k, h⟩ (clearMemory base k)
    have atEntry : clearEntry k = some (.clear ⟨k, h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace first second

theorem clearTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[clearSteps base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, clearMemory base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using clearPrefixTrace H base 7 le_rfl

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    coreFrame (familyData H t e output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        t.rows[e].tail (MachineRegularVertexBlock.oldCloud t (padding t) e) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t t.rows[e].tail)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t t.rows[e].tail
      (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  funext i
  fin_cases i <;>
    simp [coreFrame, familyData, metadataData, MachineRegularMetadata.originalData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
      MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData,
      MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      MachineRegularVertexBlock.oldCloud, paddedOld,
      MachineRegularMetadata.originalMember]
  all_goals first | exact rotor | rfl

theorem emittedData_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : emittedData H t e output =
      familyData H t e (output ++ emittedBits H t e) := rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output output' : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView (coreFrame (familyData H t e output'))
      (frame (familyData H t e output)) = frame (familyData H t e output') := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

/-- Every internal port and the inherited original row are emitted by their
actual checked row machines, using the rotor just materialized on tape 7. -/
theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[vertexSteps H t e output]
      (some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output))) =
      some (cfg H (clearEntry 0) (emittedData H t e output)) := by
  have raw := MachineRegularVertexBlock.originalTraceAt internalDegree degree_positive id none
    vertexSource (fun _ => rfl) t (padding t) (familyCloudTable H t) e output ()
  have finished := coreFrame_eq H t e (output ++ emittedBits H t e)
  simp only [emittedBits] at finished
  rw [← coreFrame_eq H t e output, ← finished] at raw
  have placed := Lift.trace Sum.inl vertexView vertexView_left vertexView_right
    Label.vertex (clearEntry 0) vertexStates
    (((((), false), none) : MetaState), MachineRegularFamily.readyState H)
    (frame (familyData H t e output)) vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    emittedData_eq, cfg, readyState, vertexStates, Equiv.prodAssoc_symm_apply,
    vertexSteps, emittedBits, id_eq] using placed

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularMetadata.totalTime t e + familySteps H t e output + vertexSteps H t e output +
    clearSteps (frame (emittedData H t e output)) 7

/-- Complete execution of one original-vertex iteration, including physical
cleanup of all seven retained metadata fields. The global index is preserved. -/
theorem originalTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t e output]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H none (initialData t e (output ++ emittedBits H t e))) := by
  have metadata := metadataTrace H t e output
  have family := familyTrace H t e output
  have vertex := vertexTrace H t e output
  have cleanup := clearTrace H (frame (emittedData H t e output))
  have final : clearMemory (frame (emittedData H t e output)) 7 =
      frame (initialData t e (output ++ emittedBits H t e)) := by
    rw [clearFrame]
    rfl
  rw [final] at cleanup
  exact joinTrace (joinTrace (joinTrace metadata family) vertex) cleanup

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBodyBounds
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

theorem cleanupSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    clearSteps (frame (emittedData H t e output)) 7 ≤
      (cleanupPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  have bounds := wide_le t output
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have ho := prefix_le_input t v.val
  have hp := cloudTotal_le_input t v
  have hl := level_le_input t v
  have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
    (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  rw [← hrotor] at hR
  rw [clearSteps_frame]
  simp only [emittedData, familyData, metadataData, MachineRegularMetadata.originalData,
    MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
    MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData, initialData,
    encodeWord_length, cleanupPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  change _ ≤ 6*((ExpanderFamily.growth+1)*bodySize t output) +
    (rotorPolynomial internalDegree).eval (bodySize t output)+13
  change cloudSize t v + MachineCloudPadding.padding (cloudSize t v) ≤ _ at hp
  dsimp only [v, bodySize, inputLength] at *
  omega

theorem totalSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    totalSteps H t e output ≤ timePolynomial.eval (bodySize t output) := by
  have hsize : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hm := (MachineRegularMetadata.totalTime_le t e).trans
    (natPolynomial_eval_mono MachineRegularMetadata.timePolynomial hsize)
  have hf := (familyExecution H t e output).steps_le_m
  have hfb := MachineRegularExecutionBounds.family_budget_le t t.rows[e].tail
  simp only [MachineRegularFamily.timePolynomial, encodeWord_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hf
  have hf' := (hf.trans hfb).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial hsize)
  have hv := vertexSteps_le H t e output
  have hc := cleanupSteps_le H t e output
  simp only [totalSteps, familySteps, timePolynomial, Polynomial.eval_add]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerCleanup
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

abbrev State := MachineRegularOriginalBody.State × Option Bool

variable {Λ : Type}

/-- Coefficient one, no seed: the destination already contains its offset. -/
def instruction (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ State
  | .scan => MachineUnaryAffineAt.scan padding scratch prefixTape 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch padding id false
      (labels .restore) (cleanupEntry labels exit)
  | .drain l => MachineDrainMany.instruction cleanupTapes
      (fun l => labels (.drain l)) exit l

theorem additionTraceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (d + 1)]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨cleanupEntry labels exit, (ambient, none), afterAddition base d o⟩ := by
  have frame (word : List Bool) :
      MachineUnaryAffineAt.tapes padding scratch prefixTape base (encodeWord d) [] word =
        Function.update base prefixTape word := by
    rw [← paddingWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have initial : MachineUnaryAffineAt.tapes padding scratch prefixTape base
      (encodeWord d) [] (encodeWord o) = base := by
    rw [frame, ← prefixWord, Function.update_eq_self]
  have run := MachineUnaryAffineAt.affineTrace padding scratch prefixTape
    (by decide) (by decide) (by decide) 1 (labels .scan) (labels .restore)
    (cleanupEntry labels exit) program (code .scan) (code .restore)
    base d o [] [] ambient register
  simpa only [List.append_nil, Nat.one_mul, initial, frame, entry, afterAddition] using run

/-- Complete physical addition followed by the six exact drain loops.
No phase run or precomputed sum word is supplied as a hypothesis. -/
theorem traceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[steps base d]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes base d o⟩ := by
  have first := additionTraceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  have second := MachineDrainMany.trace cleanupTapes (fun l => labels (.drain l)) exit
    program (fun l => code (.drain l)) (afterAddition base d o) ambient none
  simp only [MachineDrainMany.finalRegister_none, drainSteps_eq] at second
  unfold steps
  rw [Nat.add_comm, Function.iterate_add_apply, first]
  exact second

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

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev FamilyState := MachineRegularOriginalBody.FamilyState

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def familyTape (k : MachineRegularFamily.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.familyTape k)

def familyView : Tape → Option MachineRegularFamily.Tape
  | .inl k => MachineRegularOriginalBody.familyView k
  | .inr _ => none

theorem familyView_left (k : MachineRegularFamily.Tape) :
    familyView (familyTape k) = some k := MachineRegularOriginalBody.familyView_left k

theorem familyView_right (j : Tape) (k : MachineRegularFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.familyView_right j k h)
  | inr j => cases h

def metadataStates : (MetaState × ((CoreState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.2.1.1, p.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.2, ((p.1.1.1, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def familyStates : (FamilyState × ((CoreState × MetaState) × Option Bool)) ≃ State where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def vertexStates : (CoreState × ((MetaState × FamilyState) × Option Bool)) ≃ State where
  toFun p := (((p.1, p.2.1.1), p.2.1.2), p.2.2)
  invFun p := (p.1.1.1, ((p.1.1.2, p.1.2), p.2))
  left_inv _ := rfl
  right_inv _ := rfl

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.copyCount .seed))
      metadataStates (MachineRegularMetadata.program l)
  | .copyCount .seed => MachineUnaryAffineAt.seed (core 3) 0 (.copyCount .scan)
  | .copyCount .scan => MachineUnaryAffineAt.scan (core 4) scratch (core 3) 1
      (.copyCount .scan) (.copyCount .restore)
  | .copyCount .restore => Reduction.MachineTransfer.loopAt scratch (core 4) id false
      (.copyCount .restore) (some (.copyFuel .seed))
  | .copyFuel .seed => MachineUnaryAffineAt.seed dummyFuel 0 (.copyFuel .scan)
  | .copyFuel .scan => MachineUnaryAffineAt.scan paddingTape scratch dummyFuel 1
      (.copyFuel .scan) (.copyFuel .restore)
  | .copyFuel .restore => Reduction.MachineTransfer.loopAt scratch paddingTape id false
      (.copyFuel .restore) (some .guard)
  | .guard => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .family .start))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .family l => Lift.statement familyTape Label.family (some .loop)
      familyStates (MachineRegularFamily.program H l)
  | .loop => .peek dummyFuel (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop dummyFuel (fun state _ => (state.1, none))
          (.goto fun _ => .vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)))
        (.load (fun state => (state.1, none))
          (.goto fun _ => .cleanup MachineRegularOwnerCleanup.entry)))
  | .vertex l => Lift.statement core Label.vertex (some .bump)
      vertexStates (MachineRegularOriginalBody.vertexSource l)
  | .bump => .push (core 1) (fun _ => true)
      (.push (core 3) (fun _ => true) (.goto fun _ => .loop))
  | .cleanup l => MachineRegularOwnerCleanup.instruction Label.cleanup none l

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBody
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

/-- Actual cloud metadata, with every outer register and tape preserved. -/
theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineCloudPadding.totalTime t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H (some (.copyCount .seed)) (metadataData t v output)) := by
  have raw := MachineRegularMetadata.cloudTrace t v (initialData t v output)
    rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.copyCount .seed)) metadataStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), MachineRegularFamily.readyState H), none)
    (frame (initialData t v output)) MachineRegularMetadata.program (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    MachineRegularOriginalBody.readyState, metadataStates, Equiv.coe_fn_mk, entry] using placed

/-- The local rank starts at the actual cloud size, copied from its physical tape. -/
theorem copyCountTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[2 * (cloudSize t v + 1) + 1]
      (some (cfg H (some (.copyCount .seed)) (metadataData t v output))) =
      some (cfg H (some (.copyFuel .seed)) (seededData t v output)) := by
  have run := MachineUnaryAffineAt.seededAffineTrace (core 4) scratch (core 3)
    (by decide) (by decide) (by decide) 1 0
    (.copyCount .seed) (.copyCount .scan) (.copyCount .restore) (some (.copyFuel .seed))
    (program H) rfl rfl rfl (frame (metadataData t v output)) (cloudSize t v) []
    (by simp only [List.append_nil]; rfl) rfl
    (MachineRegularOriginalBody.readyState H) none
  have hempty : frame (metadataData t v output) (core 3) = [] := rfl
  rw [hempty, List.append_nil] at run
  simpa only [Nat.one_mul, Nat.add_zero, List.append_nil, cfg, readyState,
    frame, working_update_local, seededData] using run

/-- Padding fuel is another preserved unary copy; it is never a control parameter. -/
theorem copyFuelTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[2 * (padding t v + 1) + 1]
      (some (cfg H (some (.copyFuel .seed)) (seededData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ := by
  have run := MachineUnaryAffineAt.seededAffineTrace paddingTape scratch dummyFuel
    (by decide) (by decide) (by decide) 1 0
    (.copyFuel .seed) (.copyFuel .scan) (.copyFuel .restore) (some .guard)
    (program H) rfl rfl rfl (frame (seededData t v output)) (padding t v) []
    (by simp only [List.append_nil]; rfl) rfl
    (MachineRegularOriginalBody.readyState H) none
  have hempty : frame (seededData t v output) dummyFuel = [] := rfl
  rw [hempty, List.append_nil] at run
  simpa only [Nat.one_mul, Nat.add_zero, List.append_nil, cfg, readyState,
    frame, working_update_fuel] using run

theorem guardZeroStep (H : BaseTable) (data : Data) :
    TM2.step (program H) ⟨some .guard, readyState H, working data (encodeWord 0) []⟩ =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working data (encodeWord 0) []⟩ := by
  rfl

theorem guardPositiveStep (H : BaseTable) (data : Data) (d : Nat) (hd : 0 < d) :
    TM2.step (program H) ⟨some .guard, readyState H, working data (encodeWord d) []⟩ =
      some ⟨some (.family .start), readyState H, working data (encodeWord d) []⟩ := by
  cases d with
  | zero => omega
  | succ d =>
      simp [TM2.step, program, TM2.stepAux, working, dummyFuel, encodeWord,
        List.replicate_succ, readyState]

def vertexData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output : List Bool) : Data :=
  { seededData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + n)
    localRank := encodeWord (cloudSize t v + n)
    rotor := MachineRegularFamily.rotor H (cloudSize t v) }

def loopData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) : Data :=
  vertexData H t v n (output ++ blocksPrefix (dummyBits H t v) n)

def loopFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) : Tape → List Bool :=
  working (loopData H t v output n) (encodeWord (padding t v - n)) []

def cleanupCost (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  if padding t v = 0 then
    MachineRegularOwnerCleanup.steps (working (seededData t v output) (encodeWord 0) []) (padding t v)
  else MachineRegularOwnerCleanup.steps (loopFrame H t v output (padding t v)) (padding t v)

noncomputable def ownerTime (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  preSteps t v + 1 + (if padding t v = 0 then 0 else
    MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length +
      loopSteps H t v output (padding t v) le_rfl + 1) + cleanupCost H t v output

theorem familyPlacement (data : Data) (fuel saved : List Bool) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularOriginalBody.coreFrame data))
      (working data fuel saved) = working data fuel saved := by
  funext j
  cases j with
  | inl j => exact congrFun (MachineRegularOriginalBody.familyPlacement data) j
  | inr i => rfl

theorem familyResultPlacement (H : BaseTable) (k : Nat) (data : Data) (fuel saved : List Bool) :
    MachineCloudPadding.Placement.tapes familyView
      (MachineRegularFamily.frame (MachineRegularFamily.resultCore H k
        (MachineRegularOriginalBody.coreFrame data)))
      (working data fuel saved) =
      working { data with rotor := MachineRegularFamily.rotor H k } fuel saved := by
  funext j
  cases j with
  | inl j => exact congrFun (MachineRegularOriginalBody.familyResultPlacement H k data) j
  | inr i => rfl

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t v)
    (MachineRegularOriginalBody.coreFrame (seededData t v output)) rfl rfl
    (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat :=
  (familyExecution H t v output).steps

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t v output]
      (some ⟨some (.family .start), readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output 0⟩ := by
  have raw := (familyExecution H t v output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some .loop) familyStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), ((((), false), none) : MetaState)), none)
    (working (seededData t v output) (encodeWord (padding t v)) [])
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familySteps, readyState,
    MachineRegularOriginalBody.readyState, familyStates, Equiv.coe_fn_mk,
    loopFrame, loopData, vertexData, blocksPrefix_zero, List.append_nil, Nat.sub_zero,
    Nat.add_zero, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData] using placed

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output : List Bool) :
    MachineRegularOriginalBody.coreFrame (vertexData H t v j.val output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        v (paddedNew t (padding t) v j) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t v) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t v)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v
      (PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v j)
  funext i
  fin_cases i <;>
    simp [MachineRegularOriginalBody.coreFrame, vertexData, seededData, metadataData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      paddedNew,
      PreprocessingPaddingOffsets.paddingOrder_val, Nat.add_assoc]
  all_goals first | exact rotor | rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output output' fuel : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView
      (MachineRegularOriginalBody.coreFrame (vertexData H t v n output'))
      (working (vertexData H t v n output) fuel []) =
      working (vertexData H t v n output') fuel [] := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr i => rfl

/-- A complete actual dummy vertex block, with the owner's fuel left untouched. -/
theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output fuel : List Bool) :
    (advance (TM2.step (program H)))^[
        MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j output.length]
      (some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working (vertexData H t v j.val output) fuel []⟩) =
      some ⟨some .bump, readyState H,
        working (vertexData H t v j.val (output ++ dummyBits H t v j)) fuel []⟩ := by
  have raw := MachineRegularVertexBlock.dummyTraceAt internalDegree
    MachineRegularOriginalBody.degree_positive id none MachineRegularOriginalBody.vertexSource
    (fun _ => rfl) t (padding t) (familyCloudTable H t) v j output ()
  have finished := coreFrame_eq H t v j (output ++ dummyBits H t v j)
  simp only [dummyBits] at finished
  rw [← coreFrame_eq H t v j output, ← finished] at raw
  have placed := Lift.trace core vertexView vertexView_left vertexView_right
    Label.vertex (some .bump) vertexStates
    ((((((), false), none) : MetaState), MachineRegularFamily.readyState H), none)
    (working (vertexData H t v j.val output) fuel [])
    MachineRegularOriginalBody.vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    readyState, MachineRegularOriginalBody.readyState, vertexStates, Equiv.coe_fn_mk,
    dummyBits, id_eq] using placed

theorem loopPositiveStep (H : BaseTable) (data : Data) (d : Nat) :
    TM2.step (program H) ⟨some .loop, readyState H, working data (encodeWord (d + 1)) []⟩ =
      some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working data (encodeWord d) []⟩ := by
  change some (TM2.stepAux (program H .loop) _ _) = _
  simp only [program, TM2.stepAux, working_fuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, Option.getD_some, Bool.cond_true,
    List.tail_cons, working_update_fuel]
  rfl

theorem loopZeroStep (H : BaseTable) (data : Data) :
    TM2.step (program H) ⟨some .loop, readyState H, working data (encodeWord 0) []⟩ =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working data (encodeWord 0) []⟩ := by rfl

theorem bumpStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (n : Nat) (output fuel : List Bool) :
    TM2.step (program H) ⟨some .bump, readyState H, working (vertexData H t v n output) fuel []⟩ =
      some ⟨some .loop, readyState H, working (vertexData H t v (n + 1) output) fuel []⟩ := by
  change some (TM2.stepAux (program H .bump) _ _) = _
  simp only [program, TM2.stepAux,
    Function.update_of_ne (by decide : core 3 ≠ core 1),
    working_update_global, working_update_local]
  congr 2

theorem loopPrefixTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    (advance (TM2.step (program H)))^[loopSteps H t v output n hn]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : n < padding t v := by omega
      have first := ih (by omega)
      have hremaining : padding t v - n = (padding t v - (n + 1)) + 1 := by omega
      have guard := loopPositiveStep H (loopData H t v output n) (padding t v - (n + 1))
      rw [← hremaining] at guard
      have guardRun : (advance (TM2.step (program H)))^[1]
          (some ⟨some .loop, readyState H, loopFrame H t v output n⟩) =
          some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)), readyState H,
            working (loopData H t v output n) (encodeWord (padding t v - (n + 1))) []⟩ := oneStep guard
      have vertex := vertexTrace H t v ⟨n, h⟩
        (output ++ blocksPrefix (dummyBits H t v) n) (encodeWord (padding t v - (n + 1)))
      have bump := bumpStep H t v n
        ((output ++ blocksPrefix (dummyBits H t v) n) ++ dummyBits H t v ⟨n, h⟩)
        (encodeWord (padding t v - (n + 1)))
      have bumpRun := oneStep bump
      have all := joinTrace (joinTrace (joinTrace first guardRun) vertex) bumpRun
      simpa only [loopSteps, loopFrame, loopData, blocksPrefix_succ _ n h,
        List.append_assoc, Nat.add_assoc] using all

theorem preparationTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[preSteps t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
  joinTrace (joinTrace (metadataTrace H t v output) (copyCountTrace H t v output))
    (copyFuelTrace H t v output)

theorem cleanupLoopFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerCleanup.finalTapes (loopFrame H t v output (padding t v))
      (padding t v) (PreprocessingPaddingOffsets.offset (padding t) v.val) =
        frame (finalData H t v output) := by
  rw [loopFrame, cleanupFrame]
  apply congrArg frame
  simp only [loopData, vertexData, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData, finalData, blocksPrefix_all, dummyBits, ownerBits,
    Nat.add_comm (padding t v) (PreprocessingPaddingOffsets.offset (padding t) v.val)]

theorem cleanupZeroTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (hp : padding t v = 0) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerCleanup.steps
        (working (seededData t v output) (encodeWord 0) []) (padding t v)]
      (some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        working (seededData t v output) (encodeWord 0) []⟩) =
      some (cfg H none (finalData H t v output)) := by
  have run := MachineRegularOwnerCleanup.traceAt Label.cleanup none (program H) (fun _ => rfl)
    (working (seededData t v output) (encodeWord 0) []) (padding t v)
    (PreprocessingPaddingOffsets.offset (padding t) v.val) rfl rfl rfl
    (MachineRegularOriginalBody.readyState H) none
  rw [cleanupZeroFrame H t v output hp] at run
  exact run

theorem cleanupLoopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerCleanup.steps
        (loopFrame H t v output (padding t v)) (padding t v)]
      (some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩) =
      some (cfg H none (finalData H t v output)) := by
  have run := MachineRegularOwnerCleanup.traceAt Label.cleanup none (program H) (fun _ => rfl)
    (loopFrame H t v output (padding t v)) (padding t v)
    (PreprocessingPaddingOffsets.offset (padding t) v.val) rfl rfl rfl
    (MachineRegularOriginalBody.readyState H) none
  rw [cleanupLoopFrame] at run
  exact run

theorem loopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[loopSteps H t v output (padding t v) le_rfl + 1]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
  have first := loopPrefixTrace H t v output (padding t v) le_rfl
  have last : (advance (TM2.step (program H)))^[1]
      (some ⟨some .loop, readyState H, loopFrame H t v output (padding t v)⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
    simpa only [loopFrame, Nat.sub_self] using
      oneStep (loopZeroStep H (loopData H t v output (padding t v)))
  exact joinTrace first last

/-- Actual complete owner execution, including the genuinely empty padding case.
The bound is assembled from proven component bounds; its family term is not
used as an exact number of transitions. -/
noncomputable def ownerInTime (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t v output))
      (some (cfg H none (finalData H t v output))) (ownerTime H t v output) := by
  have prepared := preparationTrace H t v output
  by_cases hp : padding t v = 0
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
          working (seededData t v output) (encodeWord 0) []⟩ := by
      simpa only [hp] using oneStep (guardZeroStep H (seededData t v output))
    have all := joinTrace (joinTrace prepared gate) (cleanupZeroTrace H t v output hp)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    simp only [ownerTime, cleanupCost, ite_eq_left hp, Nat.add_zero, le_refl]
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.family .start), readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
      oneStep (guardPositiveStep H (seededData t v output) (padding t v) (Nat.pos_of_ne_zero hp))
    have all := joinTrace
      (joinTrace (joinTrace (joinTrace prepared gate) (familyTrace H t v output))
        (loopTrace H t v output)) (cleanupLoopTrace H t v output)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    have hb : familySteps H t v output ≤
        MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length :=
      (familyExecution H t v output).steps_le_m
    simp only [ownerTime, cleanupCost, ite_eq_right hp]
    omega

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat := (ownerInTime H t v output).steps

theorem ownerTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t v output]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H none (finalData H t v output)) := (ownerInTime H t v output).evals_in_steps

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : totalSteps H t v output ≤ ownerTime H t v output :=
  (ownerInTime H t v output).steps_le_m

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBodyBounds
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
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

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

theorem cleanupCost_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.cleanupCost H t v output ≤
      cleanupPolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := (cloudSize_le_input t v).trans bounds.1
  have htotal := (cloudTotal_le_input t v).trans bounds.2.1
  have hl := (level_le_input t v).trans bounds.1
  have hp : MachineCloudPadding.padding (cloudSize t v) = padding t v := rfl
  by_cases hd : padding t v = 0
  · rw [MachineRegularOwnerBody.cleanupCost, ite_eq_left hd, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, List.length_nil, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · have hpositive : 0 < padding t v := by omega
    have hkpos := PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v ⟨0, hpositive⟩
    have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v hkpos
    change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
    have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
      (natPolynomial_eval_mono (rotorPolynomial internalDegree)
        (Nat.le_add_right (inputLength t) output.length))
    rw [← hrotor] at hR
    change (MachineRegularFamily.rotor H (cloudSize t v)).length ≤
      (rotorPolynomial internalDegree).eval (bodySize t output) at hR
    rw [MachineRegularOwnerBody.cleanupCost, ite_eq_right hd,
      MachineRegularOwnerBody.loopFrame, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.loopData, MachineRegularOwnerBody.vertexData,
      MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, Nat.sub_self, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

/-- The whole owner budget follows from the real recurrence and its separately
proved stage bounds. The zero-padding branch performs no family or vertex work. -/
theorem ownerTime_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.ownerTime H t v output ≤ timePolynomial.eval (bodySize t output) := by
  have hp := preSteps_le t v output
  have hc := cleanupCost_le H t v output
  have hl := allLoopSteps_le H t v output
  have hf := (MachineRegularExecutionBounds.family_budget_le t v).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial
      (Nat.le_add_right (inputLength t) output.length))
  have hfamily : MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length ≤
      MachineRegularExecutionBounds.familyPolynomial.eval (bodySize t output) := by
    simpa only [bodySize, MachineRegularFamily.timePolynomial, encodeWord_length, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using hf
  simp only [MachineRegularOwnerBody.ownerTime, timePolynomial, Polynomial.eval_add,
    Polynomial.eval_ofNat]
  split_ifs <;> omega

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.totalSteps H t v output ≤ timePolynomial.eval (bodySize t output) :=
  (MachineRegularOwnerBody.totalSteps_le H t v output).trans (ownerTime_le H t v output)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTable
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

abbrev Tape := Body ⊕ (Header.Tape ⊕ Fin 4)
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineRegularOriginalBody.State × Option Bool

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq
    (sumDecidableEq (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq
          (sumDecidableEq
            (sumDecidableEq (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (sumDecidableEq
      (sumDecidableEq (inferInstanceAs (DecidableEq MachineCloudPrefix.Tape))
        (inferInstanceAs (DecidableEq Header.Extra)))
      (inferInstanceAs (DecidableEq (Fin 4))))

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕
      ((MachineCloudPrefix.Tape ⊕ Header.Extra) ⊕ Fin 4))
  infer_instance

def coreTape (i : Fin 27) : Tape := .inl (.inl i)
def oldFuel : Tape := .inr (.inr 0)
def ownerFuel : Tape := .inr (.inr 1)
def dummyFuel : Tape := .inr (.inr 2)
def scratch : Tape := .inr (.inr 3)

def headerTape (k : Header.Tape) : Tape :=
  if k = Header.tableTape then coreTape 0
  else if k = Header.mTape then coreTape 6
  else if k = Header.outputTape then coreTape 8
  else .inr (.inl k)

def headerView : Tape → Option Header.Tape
  | .inl (.inl i) => match i.val with
    | 0 => some Header.tableTape
    | 6 => some Header.mTape
    | 8 => some Header.outputTape
    | _ => none
  | .inl (.inr _) => none
  | .inr (.inl k) =>
      if k = Header.tableTape ∨ k = Header.mTape ∨ k = Header.outputTape then none else some k
  | .inr (.inr _) => none

theorem headerView_left (k : Header.Tape) : headerView (headerTape k) = some k := by
  by_cases ht : k = Header.tableTape
  · subst k; rfl
  by_cases hm : k = Header.mTape
  · subst k; rfl
  by_cases ho : k = Header.outputTape
  · subst k; rfl
  simp [headerTape, headerView, ht, hm, ho]

theorem headerView_right (j : Tape) (k : Header.Tape)
    (h : headerView j = some k) : headerTape k = j := by
  cases j with
  | inl j =>
    cases j with
    | inl i =>
      fin_cases i <;> simp_all [headerView] <;> subst k <;> rfl
    | inr e => cases h
  | inr j =>
    cases j with
    | inl i =>
      by_cases hi : i = Header.tableTape ∨ i = Header.mTape ∨ i = Header.outputTape
      · simp [headerView, hi] at h
      · have hik : i = k := by simpa [headerView, hi] using h
        subst k
        simp only [not_or] at hi
        simp [headerTape, hi.1, hi.2.1, hi.2.2]
    | inr i => cases h

def bodyView : Tape → Option Body
  | .inl k => some k
  | .inr _ => none

theorem bodyView_left (k : Body) : bodyView (.inl k) = some k := rfl
theorem bodyView_right (j : Tape) (k : Body)
    (h : bodyView j = some k) : Sum.inl k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j => cases h

def ownerTape : MachineRegularOwnerBody.Tape → Tape
  | .inl k => .inl k
  | .inr i => if i.val = 0 then dummyFuel else scratch

def ownerView : Tape → Option MachineRegularOwnerBody.Tape
  | .inl k => some (.inl k)
  | .inr (.inl _) => none
  | .inr (.inr i) => match i.val with
    | 2 => some (.inr 0)
    | 3 => some (.inr 1)
    | _ => none

theorem ownerView_left (k : MachineRegularOwnerBody.Tape) :
    ownerView (ownerTape k) = some k := by
  cases k with
  | inl k => rfl
  | inr i => fin_cases i <;> rfl

theorem ownerView_right (j : Tape) (k : MachineRegularOwnerBody.Tape)
    (h : ownerView j = some k) : ownerTape k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j =>
    cases j with
    | inl j => cases h
    | inr i => fin_cases i <;> simp_all [ownerView] <;> subst k <;> rfl

def headerStates :
    (Header.State Unit × (MachineRegularOriginalBody.CoreState ×
      (MachineRegularOriginalBody.FamilyState × Option Bool))) ≃ State where
  toFun p := (((p.2.1, p.1), p.2.2.1), p.2.2.2)
  invFun p := (p.1.1.2, (p.1.1.1, (p.1.2, p.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def readyState (H : BaseTable) : State := (MachineRegularOriginalBody.readyState H, none)

def copySource : CopyPhase → Tape
  | .old => coreTape 6
  | .owner => headerTape Header.nTape
def copyTarget : CopyPhase → Tape
  | .old => oldFuel
  | .owner => ownerFuel

def copyExit : CopyPhase → Label
  | .old => .oldGuard
  | .owner => .ownerGuard

def clearTape : Fin 7 → Tape :=
  ![coreTape 1, coreTape 2, coreTape 5, coreTape 6,
    headerTape Header.nTape, headerTape Header.verticesTape, headerTape Header.dartsTape]

/-- All graph-dependent loop counts remain on tapes. The code contains only
the fixed expander base and the finite subprogram labels. -/
def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .header l => Lift.statement headerTape Label.header (some .oldSeed) headerStates
      (Header.program PreprocessingRegularTables.internalDegree l)
  | .oldSeed => .push (coreTape 1) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.old)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratch id false
      (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratch (copySource phase) (copyTarget phase) false
      (.copySecond phase) (some (copyExit phase))
  | .oldGuard => Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry) (some Label.ownerSeed)
  | .oldBody l => Lift.statement Sum.inl Label.oldBody (some .oldIncrement) (Equiv.refl _)
      (MachineRegularOriginalBody.program H l)
  | .oldIncrement => Fuel.increment (coreTape 1) Label.oldGuard
  | .ownerSeed => .push (coreTape 2) (fun _ => false)
      (.push (coreTape 5) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.owner))
  | .ownerGuard => Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry) (clearEntry 0)
  | .ownerBody l => MachineCloudPadding.Placement.statement ownerTape Label.ownerBody
      (some .ownerIncrement) (MachineRegularOwnerBody.program H l)
  | .ownerIncrement => Fuel.increment (coreTape 2) Label.ownerGuard
  | .clear i => MachineDrain.drain (clearTape i) (.clear i) (clearEntry (i.val + 1))

def machine (H : BaseTable) : FinTM2 where
  K := Tape
  k₀ := coreTape 0
  k₁ := coreTape 8
  Γ _ := Bool
  Λ := Label
  main := .header .init
  σ := State
  initialState := readyState H
  m := program H

/-- These are mathematical descriptions of the physical stacks at loop
boundaries. They are never loaded into the machine's finite control. -/
def frame (data : Data) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr (.inl k) => header k
  | .inr (.inr i) => counters i

def cfg (H : BaseTable) (label : Option Label) (data : Data)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data header counters⟩

@[simp] theorem frame_core (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (i : Fin 27) :
    frame data header counters (coreTape i) = MachineRegularMetadata.frame data (.inl i) := rfl

theorem bodyPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes bodyView (MachineRegularOriginalBody.frame data)
      (frame extra header counters) = frame data header counters := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

def headerAux (n N R : List Bool) : Header.Tape → List Bool := fun k =>
  if k = Header.nTape then n
  else if k = Header.verticesTape then N
  else if k = Header.dartsTape then R
  else []

@[simp] theorem headerAux_empty : headerAux [] [] [] = (fun _ => []) := by
  funext k
  simp [headerAux]

theorem headerPlacement (data : Data) (t n m N R output : List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes headerView
      (Header.frame t n [] [] [] m [] [] [] N R [] output)
      (frame data (fun _ => []) counters) =
      frame { data with table := t, darts := m, output := output } (headerAux n N R) counters := by
  funext j
  cases j with
  | inl j =>
    cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j =>
    cases j with
    | inl k =>
      cases k with
      | inl k =>
        cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => rfl

def inputData (t : GraphTables.Table) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := []
  owner := []
  localRank := []
  count := []
  offset := []
  darts := []
  rotor := []
  output := output
  padding := []
  level := []

def headerData (t : GraphTables.Table) (output : List Bool) : Data :=
  { inputData t output with darts := encodeWord t.darts }

def headerStacks (t : GraphTables.Table) : Header.Tape → List Bool :=
  headerAux (encodeWord t.vertices) (encodeWord (Header.vertexTotal t))
    (encodeWord (Header.dartTotal PreprocessingRegularTables.internalDegree t))

theorem headerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t output]
      (some (cfg H (some (.header .init)) (inputData t output) (fun _ => []) counters)) =
      some (cfg H (some .oldSeed)
        (headerData t (output ++ Header.headerBits PreprocessingRegularTables.internalDegree t))
        (headerStacks t) counters) := by
  have raw := Header.trace PreprocessingRegularTables.internalDegree t output () none
  have placed := Lift.trace headerTape headerView headerView_left headerView_right
    Label.header (some .oldSeed) headerStates
    (MachineRegularInternalRow.coreInitialState PreprocessingRegularTables.internalDegree
      MachineRegularOriginalBody.degree_positive (), (MachineRegularFamily.readyState H, none))
    (frame (inputData t output) (fun _ => []) counters)
    (Header.program PreprocessingRegularTables.internalDegree) (program H) (fun _ => rfl)
    _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, headerPlacement,
    headerAux_empty, cfg, readyState, MachineRegularOriginalBody.readyState, headerStates,
    Equiv.coe_fn_mk, headerData, inputData, headerStacks] using placed

def oldData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with globalIndex := encodeWord index }

theorem originalData_eq (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalBody.initialData t e output = oldData t e.val output := rfl

/-- The actual old-vertex body is transported with all outer counters and
header words untouched. No body-execution hypothesis occurs in this lemma. -/
theorem oldBodyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOriginalBody.totalSteps H t e output]
      (some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry))
        (oldData t e.val output) header counters)) =
      some (cfg H (some .oldIncrement)
        (oldData t e.val (output ++ MachineRegularOriginalBody.emittedBits H t e)) header counters) := by
  have raw := MachineRegularOriginalBody.originalTrace H t e output
  have placed := Lift.trace Sum.inl bodyView bodyView_left bodyView_right Label.oldBody
    (some .oldIncrement) (Equiv.refl _) none
    (frame (oldData t e.val output) header counters)
    (MachineRegularOriginalBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, bodyPlacement,
    MachineRegularOriginalBody.cfg, originalData_eq, cfg, readyState, Equiv.refl_apply] using placed

@[simp] theorem frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) oldFuel = old := rfl

@[simp] theorem frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) ownerFuel = owners := rfl

@[simp] theorem update_frame_oldFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) oldFuel replacement =
      frame data header (counterStacks replacement owners dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_ownerFuel (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work replacement : List Bool) :
    Function.update (frame data header (counterStacks old owners dummy work)) ownerFuel replacement =
      frame data header (counterStacks old replacement dummy work) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

@[simp] theorem update_frame_global (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 1) replacement =
      frame { data with globalIndex := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

@[simp] theorem update_frame_owner (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 2) replacement =
      frame { data with owner := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem oldGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header
        (counterStacks (encodeWord (remaining + 1)) [] [] []))) =
      some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry)) data header
        (counterStacks (encodeWord remaining) [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_oldFuel]
  rfl

theorem oldGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header (counterStacks (encodeWord 0) [] [] []))) =
      some (cfg H (some Label.ownerSeed) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_oldFuel]
  rfl

theorem oldIncrementStep (H : BaseTable) (t : GraphTables.Table) (index : Nat)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldIncrement) (oldData t index output) header counters)) =
      some (cfg H (some .oldGuard) (oldData t (index + 1) output) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 1) Label.oldGuard)
    (readyState H) (frame (oldData t index output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.oldGuard, readyState H,
    Function.update (frame (oldData t index output) header counters) (coreTape 1)
      (true :: encodeWord index)⟩ : TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  simp only [cfg, oldData, encodeWord, List.replicate_succ, List.cons_append]

noncomputable def oldElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => oldElapsed H t output k +
      if h : k < t.darts then
        1 + MachineRegularOriginalBody.totalSteps H t ⟨k,h⟩ (output ++ oldPrefix H t k) + 1
      else 0

/-- Each actual fuel/body/increment segment appends exactly the next original
vertex block. This induction is over a specification index, not a register. -/
theorem oldPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.darts →
    (advance (TM2.step (program H)))^[oldElapsed H t output k]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t k (output ++ oldPrefix H t k)) header
        (counterStacks (encodeWord (t.darts-k)) [] [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [oldElapsed, oldPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.darts := by omega
    have hremaining : t.darts-k = (t.darts-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := oldGuardStep H (oldData t k (output ++ oldPrefix H t k)) header
      (t.darts-(k+1))
    rw [← hremaining] at guard
    have body := oldBodyTrace H t ⟨k,hlt⟩ (output ++ oldPrefix H t k) header
      (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have increment := oldIncrementStep H t k
      ((output ++ oldPrefix H t k) ++ MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩)
      header (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have combined := joinTrace_p0 (joinTrace_p0 (joinTrace_p0 previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOriginalBody.emittedBits H t) k hlt
    change oldPrefix H t (k+1) = oldPrefix H t k ++
      MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩ at bits
    simpa only [oldElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem oldLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[oldElapsed H t output t.darts + 1]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := oldPrefixTrace H t output header t.darts (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_p0 prefixRun (oldGuardExit H _ header)

@[simp] theorem frame_scratch (data : Data) (header : Header.Tape → List Bool)
    (old owners dummy work : List Bool) :
    frame data header (counterStacks old owners dummy work) scratch = work := rfl

@[simp] theorem frame_darts (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) : frame data header counters (coreTape 6) = data.darts := rfl

@[simp] theorem frame_header_n (data : Data) (n N R : List Bool)
    (counters : Fin 4 → List Bool) :
    frame data (headerAux n N R) counters (headerTape Header.nTape) = n := rfl

theorem oldSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldSeed) (headerData t output) header counters)) =
      some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header counters) := by
  change some (TM2.stepAux (.push (coreTape 1) (fun _ => false)
    (.goto fun _ => Label.copyFirst CopyPhase.old)) (readyState H) (frame (headerData t output) header counters)) = _
  change some (⟨some (Label.copyFirst CopyPhase.old), readyState H,
    Function.update (frame (headerData t output) header counters) (coreTape 1) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  rfl

theorem copyOldTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[2*(t.darts+2)]
      (some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] [])) := by
  have h := MachineCopy.copyTrace (coreTape 6) oldFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .old) (.copySecond .old)
    (some .oldGuard) (program H) rfl rfl
    (frame (oldData t 0 output) header (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [frame_darts, oldData, headerData, inputData, encodeWord_length,
    frame_oldFuel, List.append_nil, update_frame_oldFuel, cfg, readyState, Nat.add_assoc] using h

theorem oldStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.darts+2)+(oldElapsed H t output t.darts+1)]
      (some (cfg H (some .oldSeed) (headerData t output) header (counterStacks [] [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) :=
  joinTrace_p0 (joinTrace_p0 (oldSeedStep H t output header _) (copyOldTrace H t output header))
    (oldLoopTrace H t output header)

@[simp] theorem update_frame_offset (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 5) replacement =
      frame { data with offset := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

def ownerData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index)
    owner := encodeWord index
    offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index) }

theorem ownerSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) header counters)) =
      some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) header counters) := by
  change some (TM2.stepAux
    (.push (coreTape 2) (fun _ => false) (.push (coreTape 5) (fun _ => false)
      (.goto fun _ => Label.copyFirst CopyPhase.owner))) (readyState H)
      (frame (oldData t t.darts output) header counters)) = _
  simp only [TM2.stepAux, frame_core]
  change some (⟨some (Label.copyFirst CopyPhase.owner), readyState H,
    Function.update (Function.update (frame (oldData t t.darts output) header counters)
      (coreTape 2) [false]) (coreTape 5) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner, update_frame_offset]
  simp only [cfg, ownerData, oldData, PreprocessingPaddingOffsets.offset_zero, Nat.add_zero,
    encodeWord, List.replicate_zero, List.nil_append]

theorem copyOwnerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[2*(t.vertices+2)]
      (some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] (encodeWord t.vertices) [] [])) := by
  have h := MachineCopy.copyTrace (headerTape Header.nTape) ownerFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .owner) (.copySecond .owner)
    (some .ownerGuard) (program H) rfl rfl
    (frame (ownerData t 0 output) (headerStacks t) (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [headerStacks, frame_header_n, encodeWord_length, frame_ownerFuel,
    List.append_nil, update_frame_ownerFuel, cfg, readyState, Nat.add_assoc] using h

theorem ownerPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (old owners : List Bool) :
    MachineCloudPadding.Placement.tapes ownerView (MachineRegularOwnerBody.frame data)
      (frame extra header (counterStacks old owners [] [])) =
      frame data header (counterStacks old owners [] []) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

theorem ownerInitialData_eq (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.initialData t v output = ownerData t v.val output := rfl

theorem ownerBodyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (owners : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerBody.totalSteps H t v output]
      (some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry))
        (ownerData t v.val output) header (counterStacks [] owners [] []))) =
      some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header (counterStacks [] owners [] [])) := by
  have raw := MachineRegularOwnerBody.ownerTrace H t v output
  have placed := MachineCloudPadding.Placement.trace ownerTape ownerView ownerView_left ownerView_right
    Label.ownerBody (some .ownerIncrement)
    (frame (ownerData t v.val output) header (counterStacks [] owners [] []))
    (MachineRegularOwnerBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    ownerPlacement, MachineRegularOwnerBody.cfg, MachineRegularOwnerBody.readyState,
    ownerInitialData_eq, cfg, readyState] using placed

theorem ownerGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header
        (counterStacks [] (encodeWord (remaining+1)) [] []))) =
      some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry)) data header
        (counterStacks [] (encodeWord remaining) [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_ownerFuel]
  rfl

theorem ownerGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header (counterStacks [] (encodeWord 0) [] []))) =
      some (cfg H (clearEntry 0) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_ownerFuel]
  rfl

theorem ownerIncrementStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header counters)) =
      some (cfg H (some .ownerGuard)
        (ownerData t (v.val+1) (output ++ MachineRegularOwnerBody.ownerBits H t v)) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 2) Label.ownerGuard) (readyState H)
    (frame (MachineRegularOwnerBody.finalData H t v output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.ownerGuard, readyState H,
    Function.update (frame (MachineRegularOwnerBody.finalData H t v output) header counters)
      (coreTape 2) (true :: encodeWord v.val)⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner]
  have offset := PreprocessingRegularBounds.offset_succ (PreprocessingRegularTables.padding t) v.val v.isLt
  simp only [cfg, ownerData, headerData, inputData, MachineRegularOwnerBody.finalData,
    MachineRegularOwnerBody.initialData, offset, encodeWord, List.replicate_succ,
    List.cons_append, Nat.add_assoc]

noncomputable def ownerElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => ownerElapsed H t output k +
      if h : k < t.vertices then
        1 + MachineRegularOwnerBody.totalSteps H t ⟨k,h⟩ (output ++ ownerPrefix H t k) + 1
      else 0

theorem ownerPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.vertices →
    (advance (TM2.step (program H)))^[ownerElapsed H t output k]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t k (output ++ ownerPrefix H t k)) header
        (counterStacks [] (encodeWord (t.vertices-k)) [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [ownerElapsed, ownerPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.vertices := by omega
    have hremaining : t.vertices-k = (t.vertices-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := ownerGuardStep H (ownerData t k (output ++ ownerPrefix H t k)) header
      (t.vertices-(k+1))
    rw [← hremaining] at guard
    have body := ownerBodyTrace H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (encodeWord (t.vertices-(k+1)))
    have increment := ownerIncrementStep H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (counterStacks [] (encodeWord (t.vertices-(k+1))) [] [])
    have combined := joinTrace_p0 (joinTrace_p0 (joinTrace_p0 previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOwnerBody.ownerBits H t) k hlt
    change ownerPrefix H t (k+1) = ownerPrefix H t k ++
      MachineRegularOwnerBody.ownerBits H t ⟨k,hlt⟩ at bits
    simpa only [ownerElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem ownerLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[ownerElapsed H t output t.vertices+1]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := ownerPrefixTrace H t output header t.vertices (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_p0 prefixRun (ownerGuardExit H _ header)

theorem ownerStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.vertices+2)+(ownerElapsed H t output t.vertices+1)]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) (headerStacks t)
        (counterStacks [] [] [] [])) :=
  joinTrace_p0 (joinTrace_p0 (ownerSeedStep H t output (headerStacks t) _) (copyOwnerTrace H t output))
    (ownerLoopTrace H t output (headerStacks t))

def cleaned (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k+1 => if h : k < 7 then Function.update (cleaned base k) (clearTape ⟨k,h⟩) []
      else cleaned base k

def cleanupTime (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => cleanupTime base k + if h : k < 7 then
      ((cleaned base k) (clearTape ⟨k,h⟩)).length+1 else 0

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length+1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val+1), readyState H, Function.update base (clearTape i) []⟩ := by
  have h := MachineDrain.drainTrace (clearTape i) (.clear i) (clearEntry (i.val+1))
    (program H) rfl base (base (clearTape i)) (MachineRegularOriginalBody.readyState H) none
  simpa only [Function.update_eq_self, readyState] using h

theorem cleanupPrefixTrace (H : BaseTable) (base : Tape → List Bool) (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[cleanupTime base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, cleaned base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k,h⟩ (cleaned base k)
    have atEntry : clearEntry k = some (.clear ⟨k,h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [cleanupTime, cleaned, dite_eq_left h] using joinTrace_p0 first second

theorem cleanupTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, cleaned base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using cleanupPrefixTrace H base 7 le_rfl

def finalStacks (t : GraphTables.Table) (output : List Bool) : Tape → List Bool :=
  frame (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] [])

theorem cleaned_finalStacks (t : GraphTables.Table) (output : List Bool) :
    cleaned (finalStacks t output) 7 =
      frame (inputData t output) (fun _ => []) (counterStacks [] [] [] []) := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j with
    | inl k => cases k with
      | inl k => cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => fin_cases i <;> rfl

theorem cleaned_length_le (base : Tape → List Bool) (k : Nat) :
    ∀ j, (cleaned base k j).length ≤ (base j).length := by
  induction k with
  | zero => intro j; exact Nat.le_refl _
  | succ k ih =>
    intro j
    simp only [cleaned]
    split
    · rename_i hk
      by_cases hj : j = clearTape ⟨k,hk⟩
      · simp [hj]
      · simpa only [Function.update_of_ne hj] using ih j
    · exact ih j

theorem cleanupTime_le (base : Tape → List Bool) (cap : Nat)
    (bounded : ∀ i : Fin 7, (base (clearTape i)).length ≤ cap) (k : Nat) :
    cleanupTime base k ≤ k*(cap+1) := by
  induction k with
  | zero => simp [cleanupTime]
  | succ k ih =>
    simp only [cleanupTime]
    split
    · rename_i hk
      have hword := (cleaned_length_le base k (clearTape ⟨k,hk⟩)).trans (bounded ⟨k,hk⟩)
      calc
        cleanupTime base k + ((cleaned base k (clearTape ⟨k,hk⟩)).length+1) ≤
            k*(cap+1)+(cap+1) := by omega
        _ = (k+1)*(cap+1) := by simp only [Nat.add_mul, one_mul]
    · exact ih.trans (Nat.mul_le_mul_right _ (by omega))

theorem cleanupTime_final_le (t : GraphTables.Table) (output : List Bool) :
    cleanupTime (finalStacks t output) 7 ≤
      (7*(ExpanderFamily.growth*(PreprocessingRegularTables.internalDegree+4)+4)) *
        (PreprocessingMachineBounds.inputLength t+1) := by
  let L := PreprocessingMachineBounds.inputLength t
  let g := ExpanderFamily.growth
  let q := PreprocessingRegularTables.internalDegree
  let C := g*(q+4)+4
  have hm : t.darts ≤ L := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ L := GraphTables.vertices_le_tableBits_length t
  have hs : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ g*L :=
    PreprocessingMachineBounds.prefix_le_input t t.vertices
  have hN : Header.vertexTotal t ≤ g*L := PreprocessingMachineBounds.regularVertices_le_input t
  have hone : 1 ≤ C := by dsimp [C]; omega
  have hg : g ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgp : g+1 ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgq : g*(q+1) ≤ C := by
    have h := Nat.mul_le_mul_left g (show q+1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hmC : t.darts ≤ C*L := hm.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hnC : t.vertices ≤ C*L := hn.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hsC : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L :=
    hs.trans (Nat.mul_le_mul_right L hg)
  have hNC : Header.vertexTotal t ≤ C*L := hN.trans (Nat.mul_le_mul_right L hg)
  have hxC : t.darts +
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L := by
    calc
      _ ≤ L+g*L := Nat.add_le_add hm hs
      _ = (g+1)*L := by simp only [Nat.add_mul, one_mul, Nat.add_comm]
      _ ≤ C*L := Nat.mul_le_mul_right L hgp
  have hRC : Header.dartTotal q t ≤ C*L := by
    calc
      _ ≤ (g*L)*(q+1) := Nat.mul_le_mul_right _ hN
      _ = (g*(q+1))*L := by ac_rfl
      _ ≤ C*L := Nat.mul_le_mul_right L hgq
  have bounds : ∀ i : Fin 7, (finalStacks t output (clearTape i)).length ≤ C*L+1 := by
    intro i
    fin_cases i
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hxC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hsC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hmC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hNC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hRC 1
  have actual := cleanupTime_le (finalStacks t output) (C*L+1) bounds 7
  have hC : 2 ≤ C := by dsimp [C]; omega
  change cleanupTime (finalStacks t output) 7 ≤ (7*C)*(L+1)
  nlinarith

noncomputable def totalTime (H : BaseTable) (t : GraphTables.Table) : Nat :=
  Header.totalTime PreprocessingRegularTables.internalDegree t [] +
    (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
    (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1)) +
    cleanupTime (finalStacks t (finalOutput H t)) 7

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinTrace_p1 (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinTrace_p1 (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinTrace_p1 (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

@[simp] theorem update_frame_output (data : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) (replacement : List Bool) :
    Function.update (frame data header counters) (coreTape 8) replacement =
      frame { data with output := replacement } header counters := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j <;> rfl

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => (fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]); rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

/-- Complete execution from the actual serialized input. All header reads,
metadata, geometric rotors, rows, counters and cleanup are run by this one
finite machine. No body trace or target-table computation is supplied as a premise. -/
theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    rw [← input_stacks_eq]
    erw [update_frame_output]
    rfl
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTableBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds


theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top



namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)


def rawProgram (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.Program Tape Label State where
  input := coreTape 0
  output := coreTape 8
  main := .header .init
  initial := readyState H
  code := MachineRegularTable.Top.program H

theorem sourceMachine_eq (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.sourceMachine (rawProgram H) =
      MachineRegularTable.Top.machine H := rfl

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ : Finset Tape).toList.filter (fun k => decide (k ≠ coreTape 8))

theorem cleanup_complete (H : PreprocessingRegularTables.BaseTable) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H).output := by
  simp [cleanupTapes, rawProgram]

noncomputable def terminalRun (H : PreprocessingRegularTables.BaseTable)
    (t : GraphTables.Table) :
    MachineCanonicalOutput.TerminalRun (rawProgram H) (GraphTables.tableBits t)
      (PortTables.inputBits (PreprocessingStageMaps.regular H t))
      (MachineRegularTable.Top.timePolynomial.eval (GraphTables.tableBits t).length) where
  state := readyState H
  tapes := Function.update
    (initList (MachineRegularTable.Top.machine H) (GraphTables.tableBits t)).stk
    (coreTape 8) (PortTables.inputBits (PreprocessingStageMaps.regular H t))
  execution := by
    simpa only [sourceMachine_eq, FinTM2.Cfg, FinTM2.step, MachineRegularTable.Top.machine,
      PreprocessingMachineBounds.inputLength, PreprocessingStageMaps.regular,
      PortTables.inputBits] using!
      MachineRegularTable.Top.machineInTime H t
  output_eq := by
    dsimp only [rawProgram]
    erw [Function.update_self]

/-- The literal canonical output configuration computes the shared regular
preprocessing map, with the actual complete raw execution as its witness. -/
noncomputable def computableInPolyTime (H : PreprocessingRegularTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingRegularTables.internalDegree + 1))
      (PreprocessingStageMaps.regular H) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTableRuntime

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PCPSource
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
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

def clauseFamily (F : Formula) :
    Fin (normalizedFormula F).clauses.length → NormalizedClause (normalizedFormula F).variables :=
  fun c =>
    { clause := clauseAt (normalizedFormula F) c
      distinct := fun i j same => normalizedFormula_distinct F _
        (List.getElem_mem c.isLt) i j same }

instance clauseCount_neZero (F : Formula) : NeZero (normalizedFormula F).clauses.length :=
  ⟨Nat.ne_of_gt (List.length_pos_iff.mpr (normalizedFormula_nonempty F))⟩

end
end PerfectCompleteness.PCPSource

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationEmitMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.NormalizationLoopMachine.stepAux_finish _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany.sequence_result _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany.sequence_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationEmitMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution
open NormalizationWords

variable {K Λ A : Type} [DecidableEq K]

def emit (output : K) (literal : LiteralRecipe) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  pushWord output (List.replicate (offset literal.name) true ++ [false])
    (emitSign output literal.sign exit)

def localInstruction (tape : Fin 6 → K) (literal : LiteralRecipe)
    (labels : LocalLabel → Λ) (exit : Option Λ) :
    LocalLabel → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyOut => loopAt (tape (sourceIndex literal.name)) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape (sourceIndex literal.name))
      (tape 5) false (labels .copyBack) (some (labels .emit))
  | .emit => emit (tape 5) literal exit

theorem stepAux_emit (output : K) (literal : LiteralRecipe) (exit : Option Λ)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat) :
    TM2.stepAux (emit output literal exit) (clean ambient signs)
      (Function.update base output
        (List.replicate (sourceValue names freshBase literal.name) true ++ base output)) =
      ⟨exit, clean ambient signs, Function.update base output
        ((literalBits signs names freshBase literal).reverse ++ base output)⟩ := by
  have nameOrder : nameValue names freshBase literal.name =
      offset literal.name + sourceValue names freshBase literal.name := by
    exact Nat.add_comm _ _
  have swapped : List.replicate (offset literal.name) true ++
      (List.replicate (sourceValue names freshBase literal.name) true ++ base output) =
      List.replicate (sourceValue names freshBase literal.name) true ++
        (List.replicate (offset literal.name) true ++ base output) := by
    calc
      _ = List.replicate
          (offset literal.name + sourceValue names freshBase literal.name) true ++ base output := by
            rw [List.replicate_add, List.append_assoc]
      _ = List.replicate
          (sourceValue names freshBase literal.name + offset literal.name) true ++ base output := by
            rw [Nat.add_comm (offset literal.name) (sourceValue names freshBase literal.name)]
      _ = _ := by rw [List.replicate_add, List.append_assoc]
  unfold emit
  rw [stepAux_pushWord]
  cases hs : signValue signs literal.sign <;> cases exit <;>
    simp [emitSign, clean, TM2.stepAux, exitAt, hs, literalBits,
      NormalizationWords.literalWords, encodeWords, encodeWord, nameOrder,
      List.reverse_append, List.reverse_replicate, List.replicate_add, List.append_assoc,
      -List.replicate_append_replicate] <;>
    rw [swapped]

theorem literalTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (literal : LiteralRecipe) (labels : LocalLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = localInstruction tape literal labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (sourceWord : base (tape (sourceIndex literal.name)) =
      List.replicate (sourceValue names freshBase literal.name) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[2 * (sourceValue names freshBase literal.name + 1) + 1]
      (some ⟨some (labels .copyOut), clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((literalBits signs names freshBase literal).reverse ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have copied := MachineCopy.copyTrace (tape (sourceIndex literal.name)) (tape 5) (tape 4)
    (hd _ _ (sourceIndex_ne_output _)) (hd _ _ (sourceIndex_ne_scratch _))
    (hd 5 4 (by decide)) false (labels .copyOut) (labels .copyBack)
    (some (labels .emit)) program (atLabels .copyOut) (atLabels .copyBack)
    base scratchEmpty (ambient, signs) none
  rw [sourceWord, List.length_replicate] at copied
  have emitted : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emit), clean ambient signs,
        Function.update base (tape 5)
          (List.replicate (sourceValue names freshBase literal.name) true ++ base (tape 5))⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((literalBits signs names freshBase literal).reverse ++ base (tape 5))⟩ := by
    change some (TM2.stepAux (program (labels .emit)) _ _) = _
    rw [atLabels .emit]
    exact congrArg some (stepAux_emit (tape 5) literal exit base ambient signs names freshBase)
  exact joinTrace copied emitted

def result (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) (output : List Bool) : List Bool :=
  (literalBits signs names freshBase literal).reverse ++ output

def cost (names : Names) (freshBase : Nat) (literal : LiteralRecipe) (_ : List Bool) : Nat :=
  2 * (sourceValue names freshBase literal.name + 1) + 1

def commandSteps (names : Names) (freshBase : Nat) (commands : List LiteralRecipe) : Nat :=
  (commands.map (fun literal => 2 * (sourceValue names freshBase literal.name + 1) + 1)).sum

theorem resultOf_eq (signs : Signs) (names : Names) (freshBase : Nat)
    (commands : List LiteralRecipe) (output : List Bool) :
    MachineFiniteSequence.resultOf (result signs names freshBase) commands output =
      (commands.flatMap (literalBits signs names freshBase)).reverse ++ output := by
  induction commands generalizing output with
  | nil => rfl
  | cons literal commands ih =>
      simp only [MachineFiniteSequence.resultOf, ih, result, List.flatMap_cons,
        List.reverse_append, List.append_assoc]

theorem sequenceSteps_eq (signs : Signs) (names : Names) (freshBase : Nat)
    (commands : List LiteralRecipe) (output : List Bool) :
    MachineFiniteSequence.steps (result signs names freshBase) (cost names freshBase)
      commands output = commandSteps names freshBase commands := by
  induction commands generalizing output with
  | nil => rfl
  | cons literal commands ih =>
      simp only [MachineFiniteSequence.steps, ih, commandSteps, List.map_cons,
        List.sum_cons, cost]

theorem commandSteps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (commands : List LiteralRecipe) :
    commandSteps names freshBase commands ≤ commands.length * (2 * maximum + 3) := by
  induction commands with
  | nil => simp [commandSteps]
  | cons literal commands ih =>
      have current := sourceValue_le names freshBase maximum freshBound nameBounds literal.name
      simp only [commandSteps, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

abbrev Labels (commands : List LiteralRecipe) :=
  MachineFiniteSequence.Label (fun _ : LiteralRecipe => LocalLabel) commands

def sequenceInstruction (tape : Fin 6 → K) (commands : List LiteralRecipe)
    (labels : Labels commands → Λ) (exit : Option Λ) :
    Labels commands → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  MachineFiniteSequence.instruction (fun _ => LocalLabel) (fun _ => LocalLabel.copyOut)
    (localInstruction tape) commands labels exit

def sequenceEntry (commands : List LiteralRecipe) (labels : Labels commands → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (fun _ => LocalLabel) (fun _ => LocalLabel.copyOut)
    commands labels exit

theorem sequenceTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (commands : List LiteralRecipe) (labels : Labels commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction tape commands labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (sourceWords : ∀ name, base (tape (sourceIndex name)) =
      List.replicate (sourceValue names freshBase name) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[commandSteps names freshBase commands]
      (some ⟨sequenceEntry commands labels exit, clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((commands.flatMap (literalBits signs names freshBase)).reverse ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have native := MachineFiniteSequence.trace (fun _ : LiteralRecipe => LocalLabel)
    (fun _ => LocalLabel.copyOut) (localInstruction tape)
    (result signs names freshBase) (cost names freshBase) program
    (fun _ => True) (fun _ => clean ambient signs)
    (fun output => Function.update base (tape 5) output) commands
    (fun _ _ _ _ => True.intro)
    (fun literal _ localLabels localExit localEquations output _ => by
      have actual := literalTrace tape distinct literal localLabels localExit program
        localEquations (Function.update base (tape 5) output) ambient signs names freshBase
        (by simp [hd (sourceIndex literal.name) 5 (sourceIndex_ne_output literal.name), sourceWords])
        (by simp [hd 4 5 (by decide), scratchEmpty])
      simpa only [cost, result, Function.update_self, Function.update_idem] using actual)
    labels exit atLabels (base (tape 5)) True.intro
  simpa only [sequenceSteps_eq, resultOf_eq, Function.update_eq_self,
    sequenceEntry] using native

abbrev Label := Labels recipe

def main : Label := .inl .copyOut

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  sequenceInstruction tape recipe labels exit

def steps (names : Names) (freshBase : Nat) : Nat := commandSteps names freshBase recipe

theorem steps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum) :
    steps names freshBase ≤ 39 * (2 * maximum + 3) := by
  simpa only [steps, recipe_length] using
    commandSteps_le names freshBase maximum freshBound nameBounds recipe

theorem gadgetTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (freshWord : base (tape 0) = List.replicate freshBase true)
    (oldWords : ∀ i, base (tape (sourceIndex (.old i))) = List.replicate (names i) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps names freshBase]
      (some ⟨some (labels main), clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((bits signs names freshBase).reverse ++ base (tape 5))⟩ := by
  have sources : ∀ name, base (tape (sourceIndex name)) =
      List.replicate (sourceValue names freshBase name) true := by
    intro name
    cases name with
    | old i => exact oldWords i
    | fresh i => exact freshWord
  have trace := sequenceTrace tape distinct recipe labels exit program atLabels
    base ambient signs names freshBase sources scratchEmpty
  have entry : sequenceEntry recipe labels exit = some (labels main) := rfl
  rw [← bits_eq_flatMap] at trace
  simpa only [steps, entry] using trace

end PerfectCompleteness.NormalizationEmitMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationLoopMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryFormula.compactLiteral_positive _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationLoopMachine


open Turing
open UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineSubstitution
open NormalizationWords

def nameSum {n : Nat} (clause : Target.Clause n) : Nat :=
  clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val

def bodySteps {n : Nat} (freshBase : Nat) (clause : Target.Clause n) : Nat :=
  1 + (nameSum clause + 6) + NormalizationEmitMachine.steps (clauseNames clause) freshBase +
    (clause[0].variableIndex.val + 1) + (clause[1].variableIndex.val + 1) +
    (clause[2].variableIndex.val + 1) + 1

def steps {n : Nat} (freshBase : Nat) : List (Target.Clause n) → Nat
  | [] => 1
  | clause :: clauses => bodySteps freshBase clause + steps (freshBase + 4) clauses

theorem bodySteps_le {n : Nat} (freshBase maximum : Nat) (clause : Target.Clause n)
    (nameBound : n ≤ maximum) (freshBound : freshBase ≤ maximum) :
    bodySteps freshBase clause ≤ 84 * maximum + 128 := by
  have oldBounds (i : Fin 3) : clauseNames clause i ≤ maximum :=
    (Nat.le_of_lt clause[i].variableIndex.isLt).trans nameBound
  have emitted := NormalizationEmitMachine.steps_le (clauseNames clause)
    freshBase maximum freshBound oldBounds
  have h0 := oldBounds 0
  have h1 := oldBounds 1
  have h2 := oldBounds 2
  simp only [clauseNames] at h0 h1 h2
  unfold bodySteps nameSum
  omega

theorem steps_le {n : Nat} (freshBase maximum : Nat) (clauses : List (Target.Clause n))
    (nameBound : n ≤ maximum) (freshBound : freshBase + 4 * clauses.length ≤ maximum) :
    steps freshBase clauses ≤ clauses.length * (84 * maximum + 128) + 1 := by
  induction clauses generalizing freshBase with
  | nil => simp [steps]
  | cons clause clauses ih =>
      have head := bodySteps_le freshBase maximum clause nameBound (by
        simp only [List.length_cons] at freshBound
        omega)
      have tail := ih (freshBase + 4) (by
        simp only [List.length_cons] at freshBound
        omega)
      simp only [steps, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

section Program

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | guard
  | read (label : NormalizationReadMachine.Label)
  | emit (label : NormalizationEmitMachine.Label)
  | drain (slot : Fin 3)
  | tally
  deriving DecidableEq, Fintype

def afterDrain (labels : Label → Λ) (slot : Fin 3) : Λ :=
  if slot = 0 then labels (.drain 1) else if slot = 1 then labels (.drain 2) else labels .tally

def instruction (tape : Fin 9 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard =>
      .pop (tape 2) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isNone)
          (finish done)
          (.branch (fun state => state.2.getD false)
            (finish (some (labels (.read (.field 0))))) (finish rejected)))
  | .read l => NormalizationReadMachine.instruction (readerTapes tape)
      (fun l => labels (.read l)) (some (labels (.emit NormalizationEmitMachine.main))) rejected l
  | .emit l => NormalizationEmitMachine.instruction (emitterTapes tape)
      (fun l => labels (.emit l)) (some (labels (.drain 0))) l
  | .drain slot => MachineDrain.drain (tape (oldIndex slot)) (labels (.drain slot))
      (some (afterDrain labels slot))
  | .tally => pushWord (tape 1) (List.replicate 4 true)
      (pushWord (tape 3) (List.replicate 13 true) (finish (some (labels .guard))))

variable (tape : Fin 9 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem guardStep (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), reset ambient,
        loopTapes tape base input freshBase (remaining + 1) clauseCounter output⟩ =
      some ⟨some (labels (.read (.field 0))), reset ambient,
        loopTapes tape base input freshBase remaining clauseCounter output⟩ := by
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, reset, clean, NormalizationEmitMachine.clean,
    loopTapes_remaining tape distinct, List.replicate_succ, update_remaining tape distinct]

theorem emptyStep (input : List Bool) (freshBase : Nat) (clauseCounter output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), reset ambient,
        loopTapes tape base input freshBase 0 clauseCounter output⟩ =
      some ⟨done, reset ambient, loopTapes tape base input freshBase 0 clauseCounter output⟩ := by
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, reset, clean, NormalizationEmitMachine.clean,
    loopTapes_remaining tape distinct]

theorem tallyStep (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) (signs : Signs) :
    TM2.step program
      ⟨some (labels .tally), clean ambient signs,
        loopTapes tape base input freshBase remaining clauseCounter output⟩ =
      some ⟨some (labels .guard), reset ambient,
        loopTapes tape base input (freshBase + 4) remaining
          (List.replicate 13 true ++ clauseCounter) output⟩ := by
  have freshEq : List.replicate 4 true ++ List.replicate freshBase true =
      List.replicate (freshBase + 4) true := by
    rw [← List.replicate_add, Nat.add_comm]
  change some (TM2.stepAux (program (labels .tally)) _ _) = _
  rw [atLabels .tally]
  simp only [instruction, stepAux_pushWord, List.reverse_replicate,
    loopTapes_fresh tape distinct, freshEq, update_fresh tape distinct,
    loopTapes_count tape distinct, update_count tape distinct,
    stepAux_finish, clean, NormalizationEmitMachine.clean]

theorem bodyTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (freshBase remaining : Nat) (clauseCounter output : List Bool)
    (empty : ∀ i : Fin 9, 4 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[bodySteps freshBase clause]
      (some ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
          freshBase (remaining + 1) clauseCounter output⟩) =
      some ⟨some (labels .guard), reset ambient,
        loopTapes tape base suffix (freshBase + 4) remaining
          (List.replicate 13 true ++ clauseCounter)
          ((bits (clauseSigns clause) (clauseNames clause) freshBase).reverse ++ output)⟩ := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 9) (lo : 4 ≤ i.val := by decide) (hi : i.val ≤ 7 := by decide) :
      base (tape i) = [] := empty i lo hi
  let s₀ := loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
    freshBase remaining clauseCounter output
  let s₁ := NormalizationReadMachine.tapes (readerTapes tape) s₀ suffix
    (NormalizationReadMachine.clauseCounters clause)
  let word := bits (clauseSigns clause) (clauseNames clause) freshBase
  let s₂ := Function.update s₁ (tape 8) (word.reverse ++ output)
  let s₃ := Function.update s₂ (tape 4) []
  let s₄ := Function.update s₃ (tape 5) []
  let s₅ := Function.update s₄ (tape 6) []
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
          freshBase (remaining + 1) clauseCounter output⟩) =
      some ⟨some (labels (.read (.field 0))), reset ambient, s₀⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      guardStep tape distinct labels done rejected program atLabels base ambient
        (encodeWords (clauseWords clause) ++ suffix) freshBase remaining clauseCounter output
  have s₀input : s₀ (tape 0) = encodeWords (clauseWords clause) ++ suffix := by
    simp [s₀, loopTapes, hd]
  have s₀old (i : Fin 9) (hi : i = 4 ∨ i = 5 ∨ i = 6) : s₀ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl <;> simp [s₀, loopTapes, hd, he]
  have initialReader : NormalizationReadMachine.tapes (readerTapes tape) s₀
      (encodeWords (clauseWords clause) ++ suffix) (fun _ => []) = s₀ := by
    have unchanged (i : Fin 9) (hi : i = 4 ∨ i = 5 ∨ i = 6) :
        Function.update s₀ (tape i) [] = s₀ := by
      funext k
      by_cases hk : k = tape i
      · subst k
        simp [s₀old i hi]
      · simp [hk]
    change Function.update (Function.update (Function.update (Function.update s₀
      (tape 0) _) (tape 4) []) (tape 5) []) (tape 6) [] = s₀
    rw [← s₀input, Function.update_eq_self, unchanged 4 (by simp),
      unchanged 5 (by simp), unchanged 6 (by simp)]
  have read := NormalizationReadMachine.clauseTrace (readerTapes tape)
    (readerTapes_injective tape distinct) (fun l => labels (.read l))
    (some (labels (.emit NormalizationEmitMachine.main))) rejected program
    (fun l => atLabels (.read l)) s₀ ambient clause suffix (fun _ => false) none
  rw [initialReader] at read
  have s₁fresh : s₁ (tape 1) = List.replicate freshBase true := by
    simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex, s₀, loopTapes, hd]
  have s₁old (i : Fin 3) :
      s₁ (emitterTapes tape (NormalizationEmitMachine.sourceIndex (.old i))) =
        List.replicate (clauseNames clause i) true := by
    fin_cases i <;>
      simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex,
        emitterTapes, emitterIndex, NormalizationEmitMachine.sourceIndex,
        NormalizationReadMachine.clauseCounters, clauseNames, hd]
  have s₁scratch : s₁ (tape 7) = [] := by
    simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex, s₀, loopTapes, hd, he 7]
  have s₁output : s₁ (tape 8) = output := by
    simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex, s₀, loopTapes, hd]
  have emit := NormalizationEmitMachine.gadgetTrace (emitterTapes tape)
    (emitterTapes_injective tape distinct) (fun l => labels (.emit l))
    (some (labels (.drain 0))) program (fun l => atLabels (.emit l)) s₁ ambient
    (clauseSigns clause) (clauseNames clause) freshBase s₁fresh s₁old s₁scratch
  rw [show emitterTapes tape 5 = tape 8 from rfl, s₁output] at emit
  have s₂old : s₂ (tape 4) = List.replicate clause[0].variableIndex.val true := by
    simpa [s₂, hd 4 8 (by decide), emitterTapes, emitterIndex,
      NormalizationEmitMachine.sourceIndex, clauseNames] using s₁old 0
  have drain₀ : (advance (TM2.step program))^[clause[0].variableIndex.val + 1]
      (some ⟨some (labels (.drain 0)), clean ambient (clauseSigns clause), s₂⟩) =
      some ⟨some (labels (.drain 1)), clean ambient (clauseSigns clause), s₃⟩ := by
    have h := MachineDrain.drainTrace (tape 4) (labels (.drain 0)) (some (labels (.drain 1)))
      program (atLabels (.drain 0)) s₂ (List.replicate clause[0].variableIndex.val true)
      (ambient, clauseSigns clause) none
    have initial : Function.update s₂ (tape 4)
        (List.replicate clause[0].variableIndex.val true) = s₂ := by
      rw [← s₂old]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_replicate, clean, NormalizationEmitMachine.clean, s₃] using h
  have s₃old : s₃ (tape 5) = List.replicate clause[1].variableIndex.val true := by
    simpa [s₃, s₂, hd 5 4 (by decide), hd 5 8 (by decide), emitterTapes, emitterIndex,
      NormalizationEmitMachine.sourceIndex, clauseNames] using s₁old 1
  have drain₁ : (advance (TM2.step program))^[clause[1].variableIndex.val + 1]
      (some ⟨some (labels (.drain 1)), clean ambient (clauseSigns clause), s₃⟩) =
      some ⟨some (labels (.drain 2)), clean ambient (clauseSigns clause), s₄⟩ := by
    have h := MachineDrain.drainTrace (tape 5) (labels (.drain 1)) (some (labels (.drain 2)))
      program (atLabels (.drain 1)) s₃ (List.replicate clause[1].variableIndex.val true)
      (ambient, clauseSigns clause) none
    have initial : Function.update s₃ (tape 5)
        (List.replicate clause[1].variableIndex.val true) = s₃ := by
      rw [← s₃old]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_replicate, clean, NormalizationEmitMachine.clean, s₄] using h
  have s₄old : s₄ (tape 6) = List.replicate clause[2].variableIndex.val true := by
    simpa [s₄, s₃, s₂, hd 6 5 (by decide), hd 6 4 (by decide), hd 6 8 (by decide),
      emitterTapes, emitterIndex, NormalizationEmitMachine.sourceIndex, clauseNames] using s₁old 2
  have drain₂ : (advance (TM2.step program))^[clause[2].variableIndex.val + 1]
      (some ⟨some (labels (.drain 2)), clean ambient (clauseSigns clause), s₄⟩) =
      some ⟨some (labels .tally), clean ambient (clauseSigns clause), s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 6) (labels (.drain 2)) (some (labels .tally))
      program (atLabels (.drain 2)) s₄ (List.replicate clause[2].variableIndex.val true)
      (ambient, clauseSigns clause) none
    have initial : Function.update s₄ (tape 6)
        (List.replicate clause[2].variableIndex.val true) = s₄ := by
      rw [← s₄old]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_replicate, clean, NormalizationEmitMachine.clean, s₅] using h
  have restored : s₅ = loopTapes tape base suffix freshBase remaining clauseCounter
      (word.reverse ++ output) := by
    funext k
    by_cases h8 : k = tape 8
    · subst k
      simp [s₅, s₄, s₃, s₂, loopTapes, hd]
    · by_cases h0 : k = tape 0
      · subst k
        simp [s₅, s₄, s₃, s₂, s₁, NormalizationReadMachine.tapes,
          readerTapes, readerIndex, loopTapes, hd]
      · by_cases h4 : k = tape 4
        · subst k
          simp [s₅, s₄, s₃, loopTapes, hd, he 4]
        · by_cases h5 : k = tape 5
          · subst k
            simp [s₅, s₄, loopTapes, hd, he 5]
          · by_cases h6 : k = tape 6
            · subst k
              simp [s₅, loopTapes, hd, he 6]
            · simp [s₅, s₄, s₃, s₂, s₁, NormalizationReadMachine.tapes,
                readerTapes, readerIndex, s₀, loopTapes, h8, h0, h4, h5, h6,
                Function.update_apply]
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient (clauseSigns clause), s₅⟩) =
      some ⟨some (labels .guard), reset ambient,
        loopTapes tape base suffix (freshBase + 4) remaining
          (List.replicate 13 true ++ clauseCounter) (word.reverse ++ output)⟩ := by
    rw [restored]
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done rejected program atLabels base ambient suffix
        freshBase remaining clauseCounter (word.reverse ++ output) (clauseSigns clause)
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace guard read) emit) drain₀) drain₁) drain₂) tally
  simpa only [bodySteps, nameSum, word] using full

theorem loopTrace {n : Nat} (clauses : List (Target.Clause n)) (suffix : List Bool)
    (freshBase : Nat) (clauseCounter output : List Bool)
    (empty : ∀ i : Fin 9, 4 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps freshBase clauses]
      (some ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauses.flatMap clauseWords) ++ suffix)
          freshBase clauses.length clauseCounter output⟩) =
      some ⟨done, reset ambient,
        loopTapes tape base suffix (freshBase + 4 * clauses.length) 0
          (List.replicate (13 * clauses.length) true ++ clauseCounter)
          ((NormalizationStream.blocks freshBase clauses).reverse ++ output)⟩ := by
  induction clauses generalizing freshBase clauseCounter output with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, List.flatMap_nil,
        encodeWords, List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero,
        List.replicate_zero, NormalizationStream.blocks, List.reverse_nil] using
        emptyStep tape distinct labels done rejected program atLabels base ambient suffix
          freshBase clauseCounter output
  | cons clause clauses ih =>
      have first := bodyTrace tape distinct labels done rejected program atLabels base ambient
        clause (encodeWords (clauses.flatMap clauseWords) ++ suffix) freshBase clauses.length
        clauseCounter output empty
      have rest := ih (freshBase + 4) (List.replicate 13 true ++ clauseCounter)
        ((bits (clauseSigns clause) (clauseNames clause) freshBase).reverse ++ output)
      have full := joinTrace first rest
      have freshEq : freshBase + 4 + 4 * clauses.length =
          freshBase + 4 * (clauses.length + 1) := by omega
      have countEq : List.replicate (13 * clauses.length) true ++
          (List.replicate 13 true ++ clauseCounter) =
          List.replicate (13 * (clauses.length + 1)) true ++ clauseCounter := by
        rw [Nat.mul_add, Nat.mul_one, List.replicate_add, List.append_assoc]
      simpa only [steps, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons, freshEq, countEq, NormalizationStream.blocks,
        List.reverse_append] using full

end Program

end PerfectCompleteness.NormalizationLoopMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_NormalizationMachine
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.NormalizationMachine


open Turing UniqueGamesTheorem.Foundations Complexity
open MachineComposition UniqueGamesTheorem.Reduction.MachineTransfer

inductive Label
  | readVariables | readCount
  | loop (label : NormalizationLoopMachine.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop | reject
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt Alphabet Label State
  | .readVariables => Hastad.SourceMachine.fieldLoop 0 1 .readVariables (some .readCount)
  | .readCount => Hastad.SourceMachine.fieldLoop 0 2 .readCount (some (.loop .guard))
  | .loop label => NormalizationLoopMachine.instruction loopTapes Label.loop
      (some .restore) (some .reject) label
  | .restore => loopAt 8 9 id false .restore (some .clauseStart)
  | .clauseStart => BinaryHeaderMachine.delimiter 9 .clauseLoop
  | .clauseLoop => loopAt 3 9 id false .clauseLoop (some .variableStart)
  | .variableStart => BinaryHeaderMachine.delimiter 9 .variableLoop
  | .variableLoop => loopAt 1 9 id false .variableLoop none
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 9
  Γ := Alphabet
  Λ := Label
  main := .readVariables
  σ := State
  initialState := NormalizationLoopMachine.reset ()
  m := program

def cfg (label : Option Label) (input fresh remaining clauseCounter reversed output : List Bool) :
    machine.Cfg := ⟨label, NormalizationLoopMachine.reset (),
      tapes input fresh remaining clauseCounter reversed output⟩

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .readVariables) input [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] [] [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem readVariablesTrace (n : Nat) (suffix : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .readVariables) (encodeWord n ++ suffix) [] [] [] [] [])) =
      some (cfg (some .readCount) suffix (List.replicate n true) [] [] [] []) := by
  have updated (input fresh : List Bool) :
      Hastad.SourceMachine.fieldTapes (0 : Tape) 1 (tapes [] [] [] [] [] []) input fresh =
        tapes input fresh [] [] [] [] := by
    funext k
    fin_cases k <;> simp [Hastad.SourceMachine.fieldTapes, tapes]
  have run := Hastad.SourceMachine.fieldLoopTrace (0 : Tape) 1 (by decide)
    .readVariables (some .readCount) program rfl (tapes [] [] [] [] [] []) n suffix []
    (NormalizationLoopMachine.reset ()).1 none
  simp only [updated, List.append_nil] at run
  exact run

theorem readCountTrace (n m : Nat) (suffix : List Bool) :
    (advance machine.step)^[m + 1]
      (some (cfg (some .readCount) (encodeWord m ++ suffix) (List.replicate n true) [] [] [] [])) =
      some (cfg (some (.loop .guard)) suffix (List.replicate n true) (List.replicate m true) [] [] []) := by
  have updated (input remaining : List Bool) :
      Hastad.SourceMachine.fieldTapes (0 : Tape) 2 (tapes [] (List.replicate n true) [] [] [] [])
        input remaining = tapes input (List.replicate n true) remaining [] [] [] := by
    funext k
    fin_cases k <;> simp [Hastad.SourceMachine.fieldTapes, tapes]
  have run := Hastad.SourceMachine.fieldLoopTrace (0 : Tape) 2 (by decide)
    .readCount (some (.loop .guard)) program rfl
    (tapes [] (List.replicate n true) [] [] [] []) m suffix []
    (NormalizationLoopMachine.reset ()).1 none
  simp only [updated, List.append_nil] at run
  exact run

theorem headersTrace (n m : Nat) (suffix : List Bool) :
    (advance machine.step)^[n + m + 2]
      (some (cfg (some .readVariables) (encodeWord n ++ encodeWord m ++ suffix) [] [] [] [] [])) =
      some (cfg (some (.loop .guard)) suffix (List.replicate n true) (List.replicate m true) [] [] []) := by
  have first := readVariablesTrace n (encodeWord m ++ suffix)
  have second := readCountTrace n m suffix
  have full := joinTrace first second
  have count : n + 1 + (m + 1) = n + m + 2 := by omega
  simpa only [count, List.append_assoc] using full

theorem restoreTrace (fresh clauseCounter body : List Bool) :
    (advance machine.step)^[body.length + 1]
      (some (cfg (some .restore) [] fresh [] clauseCounter body.reverse [])) =
      some (cfg (some .clauseStart) [] fresh [] clauseCounter [] body) := by
  change (nextAt (9 : Tape) program)^[body.length + 1]
    (some (cfg (some .restore) [] fresh [] clauseCounter body.reverse [])) = _
  have updated : tapesAt (8 : Tape) 9 (tapes [] fresh [] clauseCounter body.reverse []) [] body =
      tapes [] fresh [] clauseCounter [] body := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  have run := transferAt_fromTapes (Γ := Alphabet) (8 : Tape) 9 (by decide) id false
    .restore (some .clauseStart) program rfl (tapes [] fresh [] clauseCounter body.reverse [])
    (NormalizationLoopMachine.reset ()).1 none
  have source : tapes [] fresh [] clauseCounter body.reverse [] 8 = body.reverse := rfl
  have output : tapes [] fresh [] clauseCounter body.reverse [] 9 = [] := rfl
  rw [source, output, List.length_reverse, List.reverse_reverse, List.map_id_fun,
    List.append_nil, id_eq, updated] at run
  exact run

theorem headerOutputTrace (n m : Nat) (body : List Bool) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) [] (List.replicate n true) []
        (List.replicate m true) [] body)) =
      some (cfg none [] [] [] [] [] (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((NormalizationLoopMachine.reset ()).1, none),
      tapes [] (List.replicate n true) [] (List.replicate m true) [] body⟩) =
    some ⟨none, ((NormalizationLoopMachine.reset ()).1, none),
      tapes [] [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (fresh clauses output : List Bool) :
      BinaryHeaderMachine.tapes (1 : Tape) 3 9 (tapes [] [] [] [] [] []) fresh clauses output =
        tapes [] fresh [] clauses [] output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have run := BinaryHeaderMachine.headerTrace (1 : Tape) 3 9 (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop none program rfl rfl rfl rfl
    (tapes [] [] [] [] [] []) (NormalizationLoopMachine.reset ()).1 n m body none
  simp only [updated] at run
  exact run

theorem loopTrace (formula : Target.Formula) :
    (advance machine.step)^[NormalizationLoopMachine.steps formula.variables formula.clauses]
      (some (cfg (some (.loop .guard)) (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] [])) =
      some (cfg (some .restore) []
        (List.replicate (formula.variables + 4 * formula.clauses.length) true) []
        (List.replicate (13 * formula.clauses.length) true)
        (NormalizationStream.blocks formula.variables formula.clauses).reverse []) := by
  change (advance (TM2.step program))^[NormalizationLoopMachine.steps formula.variables formula.clauses]
    (some ⟨some (.loop .guard), NormalizationLoopMachine.reset (),
      tapes (encodeWords (formula.clauses.flatMap clauseWords))
        (List.replicate formula.variables true) (List.replicate formula.clauses.length true)
        [] [] []⟩) =
    some ⟨some .restore, NormalizationLoopMachine.reset (),
      tapes [] (List.replicate (formula.variables + 4 * formula.clauses.length) true) []
        (List.replicate (13 * formula.clauses.length) true)
        (NormalizationStream.blocks formula.variables formula.clauses).reverse []⟩
  have updated (input : List Bool) (fresh remaining : Nat) (counter output : List Bool) :
      NormalizationLoopMachine.loopTapes loopTapes (tapes [] [] [] [] [] [])
        input fresh remaining counter output =
      tapes input (List.replicate fresh true) (List.replicate remaining true) counter output [] := by
    funext k
    fin_cases k <;> simp [NormalizationLoopMachine.loopTapes, loopTapes, tapes]
  have run := NormalizationLoopMachine.loopTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes [] [] [] [] [] []) () formula.clauses [] formula.variables [] []
    (by intros; simp [tapes])
  simp only [updated, List.append_nil, List.replicate_zero] at run
  exact run

theorem formulaBits_eq (formula : Target.Formula) :
    formulaBits formula = encodeWord formula.variables ++ encodeWord formula.clauses.length ++
      encodeWords (formula.clauses.flatMap clauseWords) := by
  simp only [formulaBits, formulaWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]

def steps (formula : Target.Formula) : Nat :=
  (formula.variables + formula.clauses.length + 2) +
    NormalizationLoopMachine.steps formula.variables formula.clauses +
    ((NormalizationStream.blocks formula.variables formula.clauses).length + 1) +
    ((formula.variables + 4 * formula.clauses.length) + 13 * formula.clauses.length + 4)

theorem normalizationTrace (formula : Target.Formula) :
    (advance machine.step)^[steps formula] (some (initList machine (formulaBits formula))) =
      some (haltList machine (formulaBits (Normalization.normalize formula))) := by
  have first := headersTrace formula.variables formula.clauses.length
    (encodeWords (formula.clauses.flatMap clauseWords))
  have second := loopTrace formula
  have third := restoreTrace
    (List.replicate (formula.variables + 4 * formula.clauses.length) true)
    (List.replicate (13 * formula.clauses.length) true)
    (NormalizationStream.blocks formula.variables formula.clauses)
  have fourth := headerOutputTrace (formula.variables + 4 * formula.clauses.length)
    (13 * formula.clauses.length) (NormalizationStream.blocks formula.variables formula.clauses)
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  rw [initList_eq, haltList_eq, NormalizationStream.encoded_normalize, formulaBits_eq]
  exact full

theorem header_counts_le (formula : Target.Formula) :
    formula.variables ≤ (formulaBits formula).length ∧
      formula.clauses.length ≤ (formulaBits formula).length := by
  rw [formulaBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem steps_le (formula : Target.Formula) :
    steps formula ≤ timePolynomial.eval (formulaBits formula).length := by
  let B := (formulaBits formula).length
  let M := formula.variables + 4 * formula.clauses.length
  have variablesBound : formula.variables ≤ B := (header_counts_le formula).1
  have clausesBound : formula.clauses.length ≤ B := (header_counts_le formula).2
  have addressBound : M ≤ 5 * B := by dsimp [M]; omega
  have loopBound := NormalizationLoopMachine.steps_le formula.variables M formula.clauses
    (by dsimp [M]; omega) (Nat.le_refl M)
  have loopUniform : NormalizationLoopMachine.steps formula.variables formula.clauses ≤
      B * (420 * B + 128) + 1 :=
    loopBound.trans (Nat.add_le_add_right
      (Nat.mul_le_mul clausesBound (by omega)) 1)
  have bodyBound := NormalizationStream.blocks_length_le formula.clauses formula.variables M
    (by dsimp [M]; omega) (Nat.le_refl M)
  have bodyUniform : (NormalizationStream.blocks formula.variables formula.clauses).length ≤
      B * (39 * (5 * B + 3)) :=
    bodyBound.trans (Nat.mul_le_mul clausesBound (by omega))
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  change steps formula ≤ 1000 * (B + 1) ^ 2
  unfold steps
  nlinarith

def outputsInTime (formula : Target.Formula) :
    TM2OutputsInTime machine (formulaBits formula)
      (some (formulaBits (Normalization.normalize formula)))
      (timePolynomial.eval (formulaBits formula).length) where
  steps := steps formula
  evals_in_steps := normalizationTrace formula
  steps_le_m := steps_le formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits formulaBits Normalization.normalize where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((formulaBits (Normalization.normalize formula)).map id))
      (timePolynomial.eval (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

end PerfectCompleteness.NormalizationMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

abbrev Record (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots × (Values rows repeats p slots × BelowArrays rows p slots)

def callNumbering (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    OriginalCutCalls.Index rows repeats p ≃
      Fin (OriginalCutCalls.count rows repeats n (m + 1)) :=
  (Fintype.equivFin (OriginalCutCalls.Index rows repeats p)).trans
    (Equiv.cast (congrArg Fin (OriginalCutCalls.card_eq_count rows repeats p)))

def numberedValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (values : Values rows repeats p slots) :
    Fin (OriginalCutCalls.count rows repeats n (m + 1)) → H (cutSlots p slots) :=
  fun call => values ((callNumbering rows repeats p).symm call)

end
end PerfectCompleteness.OriginalWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCutBridge
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
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

def assembledEquiv (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    ((Fin calls → H slots) × ChildArrays rows slots) ≃
      CutChildGrouping.Assembled (C := Fin calls) slots rows := Equiv.refl _

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

abbrev NumberedRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots ×
    CutChildGrouping.Assembled
      (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows

def numberRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) : NumberedRecord rows repeats p slots :=
  (record.1, assembledEquiv (OriginalCutCalls.count rows repeats n (m + 1)) rows
    (cutSlots p slots) (numberedValues rows repeats p slots record.2.1, record.2.2))

end
end PerfectCompleteness.OriginalWholeCutBridge

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalUniformCutBase
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

@[instance_reducible] def valuesChildrenFintype (C : Type*)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat)
    [hValues : Fintype (C → H slots)] [hChildren : Fintype (ChildArrays rows slots)] :
    Fintype ((C → H slots) × ChildArrays rows slots) :=
  @instFintypeProd (C → H slots) (ChildArrays rows slots) hValues hChildren

attribute [local instance 2000] instFintypeProd

end
end PerfectCompleteness.OriginalUniformCutBase

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_NumberedUniformCut
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.NumberedUniformCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

variable {branch : Nat → Nat} {n m t : Nat}

def numberRecordEquiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Record rows repeats p slots ≃ OriginalWholeCutBridge.NumberedRecord rows repeats p slots :=
  Equiv.prodCongr (Equiv.refl (Exterior rows repeats p slots))
    ((Equiv.prodCongr
      (Equiv.arrowCongr (callNumbering rows repeats p) (Equiv.refl (H (cutSlots p slots))))
      (Equiv.refl (BelowArrays rows p slots))).trans
        (OriginalWholeCutBridge.assembledEquiv
          (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots)))

@[simp] theorem numberRecordEquiv_apply (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) :
    numberRecordEquiv rows repeats p slots record =
      OriginalWholeCutBridge.numberRecord rows repeats p slots record := rfl

end
end PerfectCompleteness.NumberedUniformCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ExtraCutCall
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExtraCutCall

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

def splitAssembled (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    CutChildGrouping.Assembled (C := Fin (calls + 1)) slots rows ≃
      CutChildGrouping.Assembled (C := Fin calls) slots rows × H slots :=
  (OriginalWholeCutBridge.assembledEquiv (calls + 1) rows slots).symm.trans
    ((Equiv.prodCongr (splitLast calls (H slots)) (Equiv.refl (ChildArrays rows slots))).trans
      ((middleSwap (Fin calls → H slots) (H slots) (ChildArrays rows slots)).trans
        (Equiv.prodCongr (OriginalWholeCutBridge.assembledEquiv calls rows slots)
          (Equiv.refl (H slots)))))

def observationLaw (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (CutChildGrouping.Assembled (C := Fin calls) slots rows) :=
  (OriginalChildBlocks.sourceLaw calls rows repeats chosen q slots).pushforward
    (OriginalChildBlocks.observed calls rows repeats chosen q slots)

abbrev EnlargedRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots × CutChildGrouping.Assembled
    (C := Fin (OriginalCutCalls.count rows repeats n (m + 1) + 1)) (cutSlots p slots) rows

def splitRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots) :
    OriginalWholeCutBridge.NumberedRecord rows repeats p slots × H (cutSlots p slots) :=
  let split := splitAssembled (OriginalCutCalls.count rows repeats n (m + 1)) rows
    (cutSlots p slots) record.2
  ((record.1, split.1), split.2)

@[simp] theorem splitRecord_oldCall (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots)
    (call : Fin (OriginalCutCalls.count rows repeats n (m + 1))) :
    (splitRecord rows repeats p slots record).1.2.1 call = record.2.1 call.castSucc := rfl

@[simp] theorem splitRecord_fresh (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : EnlargedRecord rows repeats p slots) :
    (splitRecord rows repeats p slots record).2 =
      record.2.1 (Fin.last (OriginalCutCalls.count rows repeats n (m + 1))) := rfl

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.ExtraCutCall

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_NormalizedTarget
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
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

def sourceShapes (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input) :
    Fin (TreeCanonical.locationCount branch n t) → CanonicalKeyShape.Shape :=
  fun position => SourceClauseReaderMachine.clauseShape
    (SourceTupleData.selectedClause input.formula indices position)

theorem numberedSlots_eq (input : NormalizedSourceInput.Input)
    (indices : SourceTuple (branch := branch) (n := n) (t := t) input)
    (position : Fin (TreeCanonical.locationCount branch n t)) :
    TreeCanonical.numberedSlots
        (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input)
          (tupleQuestion input indices)) position =
      KeyMetadataMachine.actualSlot (sourceShapes input indices position)
        (indices position).val (parsedVariableIDs input indices position) := by
  change SourceKeys.slot (NormalizedSourceInput.clauses input)
    (.clause (SourceQuestionOrder.questionToTuple
      (SourceQuestionOrder.tupleToQuestion
        (branch := branch) (n := n) (t := t) indices) position)) = _
  simp only [SourceQuestionOrder.questionToTuple_tupleToQuestion]; rfl

end
end PerfectCompleteness.NormalizedTarget

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceKeyBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.ExactTargetOdometer.baseTapes_edgeWork _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_extra _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_output _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_table _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceKeyBounds


open CanonicalKeys CanonicalKeyShape ClauseSupport MixedSupport
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

def SlotIDsLe (bound : Nat) : Slot → Prop
  | .clause occurrence variableIDs _ => occurrence ≤ bound ∧ ∀ i, variableIDs i ≤ bound
  | .bit variableID => variableID ≤ bound

theorem recover_entryID_le (bound : Nat) (slot : Slot) (support : SupportMode)
    (bounded : SlotIDsLe bound slot) : KeyMetadataEncoding.entryID (recover slot support) ≤ bound := by
  cases slot <;> cases support <;>
    simp_all [SlotIDsLe, recover, KeyMetadataEncoding.entryID]

theorem actualSlot_IDs_le (bound : Nat) (shape : Shape) (occurrence : Nat)
    (variableIDs : Fin 3 → Nat) (occurrenceBound : occurrence ≤ bound)
    (variableBounds : ∀ i, variableIDs i ≤ bound) :
    SlotIDsLe bound (KeyMetadataMachine.actualSlot shape occurrence variableIDs) := by
  cases shape <;> simp_all [KeyMetadataMachine.actualSlot, SlotIDsLe]

variable {width : Nat} {Y : Type*}

theorem retained_entryID_le (slots : Fin width → Slot) (support : Fin width → SupportMode)
    (bound : Nat) (bounded : ∀ i, SlotIDsLe bound (slots i))
    (entry : Fin width × SlotKey) (present : entry ∈ retained slots support) :
    KeyMetadataEncoding.entryID entry.2 ≤ bound := by
  unfold retained at present
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp present).1
  exact recover_entryID_le bound (slots i) (support i) (bounded i)

theorem key_entryID_le (side : Side) (slots : Fin width → Slot)
    (f : Assignment slots → Y) (bound : Nat) (bounded : ∀ i, SlotIDsLe bound (slots i))
    (entry : Fin width × SlotKey) (present : entry ∈ (CanonicalKeys.key side slots f).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ bound := by
  change entry ∈ retainedKeys slots f at present
  rw [retainedKeys_recover] at present
  exact retained_entryID_le slots _ bound bounded entry present

theorem variableCount_le_bits (input : NormalizedSourceInput.Input) :
    NormalizedSourceInput.variableCount input ≤ (NormalizedSourceInput.bits input).length := by
  rw [NormalizedSourceInput.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem clauseCount_le_bits (input : NormalizedSourceInput.Input) :
    NormalizedSourceInput.clauseCount input ≤ (NormalizedSourceInput.bits input).length := by
  rw [NormalizedSourceInput.bits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem source_variable_le_bits (input : NormalizedSourceInput.Input)
    (index : Fin (NormalizedSourceInput.clauseCount input)) (slot : Fin 3) :
    ((NormalizedSourceInput.clauses input index).variable slot).val ≤
      (NormalizedSourceInput.bits input).length :=
  (Nat.le_of_lt ((NormalizedSourceInput.clauses input index).variable slot).isLt).trans
    (variableCount_le_bits input)

variable {branch : Nat → Nat} {n t : Nat}

theorem numberedSlots_IDs_le (input : NormalizedSourceInput.Input)
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (position : Fin (TreeCanonical.locationCount branch n t)) :
    SlotIDsLe (NormalizedSourceInput.bits input).length
      (TreeCanonical.numberedSlots
        (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) position) := by
  let indices := SourceQuestionOrder.questionToTuple source
  have restored : NormalizedTarget.tupleQuestion input indices = source :=
    SourceQuestionOrder.tupleToQuestion_questionToTuple source
  have slotsEq := NormalizedTarget.numberedSlots_eq input indices position
  rw [restored] at slotsEq
  rw [slotsEq]
  apply actualSlot_IDs_le
  · exact (Nat.le_of_lt (indices position).isLt).trans (clauseCount_le_bits input)
  · intro slot
    rw [NormalizedTarget.parsedVariableIDs_eq]
    exact source_variable_le_bits input (indices position) slot

theorem source_key_retained_length (input : NormalizedSourceInput.Input)
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (side : Side)
    (f : TreeSourceSpaces.Domain
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) → Y) :
    (TreeCanonical.key side
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) f).retained.length ≤
        TreeCanonical.locationCount branch n t :=
  key_retained_length side _ _

theorem source_key_entryID_le (input : NormalizedSourceInput.Input)
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (side : Side)
    (f : TreeSourceSpaces.Domain
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) → Y)
    (entry : Fin (TreeCanonical.locationCount branch n t) × SlotKey)
    (present : entry ∈ (TreeCanonical.key side
      (MetadataFreeSampler.sourceSlots (NormalizedSourceInput.clauses input) source) f).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ (NormalizedSourceInput.bits input).length :=
  key_entryID_le side _ _ _ (numberedSlots_IDs_le input source) entry present


variable (input : NormalizedSourceInput.Input) (rows repeats : Nat → Nat)

local notation "clauses" => NormalizedSourceInput.clauses input
local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "family" => PreliminarySampler.family clauses branch n t rows repeats

theorem left_retained_length (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (CanonicalGame.leftKey F e).retained.length ≤ TreeCanonical.locationCount branch n t := by
  rw [HierarchicalGame.leftKey_eq family e]
  exact source_key_retained_length input e.1.1 .left _

theorem right_retained_length (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    (CanonicalGame.rightKey F e).retained.length ≤ TreeCanonical.locationCount branch n t := by
  rw [HierarchicalGame.rightKey_eq family e]
  exact source_key_retained_length input e.1.1 .right _

theorem left_entryID_le (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (entry : Fin (TreeCanonical.locationCount branch n t) × SlotKey)
    (present : entry ∈ (CanonicalGame.leftKey F e).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ (NormalizedSourceInput.bits input).length := by
  rw [HierarchicalGame.leftKey_eq family e] at present
  exact source_key_entryID_le input e.1.1 .left _ entry present

theorem right_entryID_le (e : PreliminarySampler.Raw clauses branch n t rows repeats)
    (entry : Fin (TreeCanonical.locationCount branch n t) × SlotKey)
    (present : entry ∈ (CanonicalGame.rightKey F e).retained) :
    KeyMetadataEncoding.entryID entry.2 ≤ (NormalizedSourceInput.bits input).length := by
  rw [HierarchicalGame.rightKey_eq family e] at present
  exact source_key_entryID_le input e.1.1 .right _ entry present

end

end PerfectCompleteness.SourceKeyBounds



namespace PerfectCompleteness.SignedSourceCost


open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {Extra : Type} [DecidableEq Extra]

local notation "width" => TreeCanonical.locationCount branch n t

theorem fieldValue_le_bits (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (position : Fin width) (field : Fin 4) :
    KeyMetadataMachine.fieldValue
      (SignedTupleLayout.ids input.formula indices position)
      (SignedTupleLayout.vars input.formula indices position) field ≤
        (NormalizedSourceInput.bits input).length := by
  refine Fin.cases ?_ (fun slot => ?_) field
  · change (indices position).val ≤ (NormalizedSourceInput.bits input).length
    exact (Nat.le_of_lt (indices position).isLt).trans
      (SourceKeyBounds.clauseCount_le_bits input)
  · change (SignedTupleLayout.vars input.formula indices position slot) ≤
      (NormalizedSourceInput.bits input).length
    exact SourceKeyBounds.source_variable_le_bits input (indices position) slot

theorem prepared_metadata (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (hinput : SignedTupleLayout.Input input.formula indices base)
    (data : SignedTupleBodyMachine.Data width) (position : Fin width) (field : Fin 4) :
    SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
      SignedTupleLayout.Tape.edgeCount
      (SignedTupleLayout.preparedTapes input.formula indices base) data
      (KeyMetadataMachine.idTape (SignedTupleLayout.metadata position) field) =
        encodeWord (KeyMetadataMachine.fieldValue
          (SignedTupleLayout.ids input.formula indices position)
          (SignedTupleLayout.vars input.formula indices position) field) := by
  have unchanged :
      SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
        SignedTupleLayout.Tape.edgeCount
        (SignedTupleLayout.preparedTapes input.formula indices base) data
        (KeyMetadataMachine.idTape (SignedTupleLayout.metadata position) field) =
      SignedTupleLayout.preparedTapes input.formula indices base
        (KeyMetadataMachine.idTape (SignedTupleLayout.metadata position) field) := by
    apply SignedTupleBodyMachine.tapes_frame
    all_goals
      fin_cases field <;>
        simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, SignedTupleLayout.metadata]
  exact unchanged.trans
    (SignedTupleLayout.prepared_metadata input.formula indices base hinput position field)

theorem prepared_sourceLength_le (input : NormalizedSourceInput.Input)
    (indices : Fin width → Fin (NormalizedSourceInput.clauseCount input))
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (hinput : SignedTupleLayout.Input input.formula indices base)
    (data : SignedTupleBodyMachine.Data width) :
    CanonicalKeyMachine.sourceLength SignedTupleLayout.metadata
      (SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
        SignedTupleLayout.Tape.edgeCount
        (SignedTupleLayout.preparedTapes input.formula indices base) data) ≤
      4 * width * ((NormalizedSourceInput.bits input).length + 1) := by
  calc
    CanonicalKeyMachine.sourceLength SignedTupleLayout.metadata
        (SignedTupleBodyMachine.tapes SignedTupleLayout.Tape.edgeWork
          SignedTupleLayout.Tape.edgeCount
          (SignedTupleLayout.preparedTapes input.formula indices base) data) ≤
        ∑ _ : Fin width, ∑ _ : Fin 4, ((NormalizedSourceInput.bits input).length + 1) := by
      unfold CanonicalKeyMachine.sourceLength KeyMetadataMachine.sourceLength
      apply Finset.sum_le_sum
      intro position _
      apply Finset.sum_le_sum
      intro field _
      rw [prepared_metadata input indices base hinput data position field, encodeWord_length]
      exact Nat.add_le_add_right (fieldValue_le_bits input indices position field) 1
    _ = 4 * width * ((NormalizedSourceInput.bits input).length + 1) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end
end PerfectCompleteness.SignedSourceCost

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SignedRuntimeBounds
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SignedRuntimeBounds


open CanonicalKeys MetadataFreeSampler
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators Classical

noncomputable section

section Fold

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1))

local notation "width" => TreeCanonical.locationCount branch n t
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

theorem fold_budget_le {K : Type} [DecidableEq K] (T count : Nat)
    (signs : SignTuple branch n t) (ids : Fin width → Nat)
    (vars : Fin width → Fin 3 → Nat) (source : Fin width → Fin 6 → K)
    (work : Fin 10 → K) (countTape : K) (base : K → List Bool)
    (sourceBound : ∀ data : SignedTupleBodyMachine.Data width,
      CanonicalKeyMachine.sourceLength source
        (SignedTupleBodyMachine.tapes work countTape base data) ≤ 4 * width * (T + 1))
    (leftBound : ∀ i : Fin D, KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows signs i) .left ids vars))
    (rightBound : ∀ i : Fin D, KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows signs i) .right ids vars))
    (indices : List (Fin D)) (data : SignedTupleBodyMachine.Data width)
    (leftEarlier : KeysBound T data.leftKeys) (rightEarlier : KeysBound T data.rightKeys)
    (leftCount : data.leftKeys.length + indices.length ≤ count)
    (rightCount : data.rightKeys.length + indices.length ≤ count) :
    SignedTupleBodyMachine.budget hq large hn hbranch hrows signs ids vars
        source work countTape base indices data ≤
      indices.length * (2 * SignedCostEnvelope.endpointBound width T count + 4) := by
  induction indices generalizing data with
  | nil => simp only [SignedTupleBodyMachine.budget, List.length_nil, Nat.zero_mul, le_refl]
  | cons i indices ih =>
    let descriptor := SignedScheduleIndex.atIndex hq large hn hbranch hrows signs i
    have leftCount' : data.leftKeys.length + 1 ≤ count := by
      simp only [List.length_cons] at leftCount
      omega
    have rightCount' : data.rightKeys.length + 1 ≤ count := by
      simp only [List.length_cons] at rightCount
      omega
    have leftCost := endpoint_budget_le source
      (SignedTupleBodyMachine.tapes work countTape base data) data.leftKeys
      (CompletedEdgeMachine.key hq large descriptor .left ids vars)
      (sourceBound data) leftEarlier (leftBound i) leftCount'
    have rightCost := endpoint_budget_le source
      (SignedTupleBodyMachine.tapes work countTape base data) data.rightKeys
      (CompletedEdgeMachine.key hq large descriptor .right ids vars)
      (sourceBound data) rightEarlier (rightBound i) rightCount'
    have edgeCost : CompletedEdgeMachine.budget hq large descriptor source
        (SignedTupleBodyMachine.tapes work countTape base data)
        data.leftKeys data.rightKeys ids vars ≤
        2 * SignedCostEnvelope.endpointBound width T count + 1 := by
      unfold CompletedEdgeMachine.budget
      omega
    have nextLeft : KeysBound T
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).leftKeys :=
      keysBound_append leftEarlier (leftBound i)
    have nextRight : KeysBound T
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).rightKeys :=
      keysBound_append rightEarlier (rightBound i)
    have nextLeftCount :
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).leftKeys.length +
          indices.length ≤ count := by
      simpa only [SignedTupleBodyMachine.next, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using leftCount
    have nextRightCount :
        (SignedTupleBodyMachine.next hq large descriptor ids vars data).rightKeys.length +
          indices.length ≤ count := by
      simpa only [SignedTupleBodyMachine.next, List.length_append, List.length_singleton,
        List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rightCount
    have rest := ih (SignedTupleBodyMachine.next hq large descriptor ids vars data)
      nextLeft nextRight nextLeftCount nextRightCount
    change CompletedEdgeMachine.budget hq large descriptor source
        (SignedTupleBodyMachine.tapes work countTape base data)
        data.leftKeys data.rightKeys ids vars + 3 +
        SignedTupleBodyMachine.budget hq large hn hbranch hrows signs ids vars
          source work countTape base indices
          (SignedTupleBodyMachine.next hq large descriptor ids vars data) ≤ _
    calc
      _ ≤ (2 * SignedCostEnvelope.endpointBound width T count + 1) + 3 +
          indices.length * (2 * SignedCostEnvelope.endpointBound width T count + 4) :=
        Nat.add_le_add (Nat.add_le_add_right edgeCost 3) rest
      _ = (i :: indices).length *
          (2 * SignedCostEnvelope.endpointBound width T count + 4) := by
        simp only [List.length_cons]
        ring

end Fold


variable {branch : Nat → Nat} {n t : Nat}
  (input : NormalizedSourceInput.Input) (rows repeats : Nat → Nat)
  (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "clauses" => NormalizedSourceInput.clauses input
local notation "T" => List.length (NormalizedSourceInput.bits input)
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "hq" => CanonicalLocalCompletion.alphabet_positive width δ
local notation "large" => CanonicalLocalCompletion.partitionWidth_le_alphabet width δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q
local notation "C" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "dataOfPrefix" => SignedTupleSemantics.dataOfPrefix
  (t := t) clauses rows repeats hn hbranch hrows δ

theorem completedOrder_length_le : (order).length ≤ D * (T + 1) ^ width := by
  rw [CompletedVisitOrder.completedOrder_length]
  exact Nat.mul_le_mul_left D
    (Nat.pow_le_pow_left ((SourceKeyBounds.clauseCount_le_bits input).trans (Nat.le_succ T)) width)

theorem left_atIndex_bound
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (i : Fin D) :
    KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i)
      .left (SignedTupleSemantics.sourceIDs source)
      (SignedTupleSemantics.sourceVariables clauses source)) := by
  let e := SignedTupleSemantics.occurrenceAt clauses rows repeats hn hbranch hrows δ source i
  have same := SignedTupleSemantics.left_key clauses rows repeats hn hbranch hrows δ e
  simp only [e, SignedTupleSemantics.descriptorOf_occurrenceAt,
    SignedTupleSemantics.occurrenceAt_source] at same
  rw [same]
  exact ⟨SourceKeyBounds.left_retained_length input rows repeats e.1,
    SourceKeyBounds.left_entryID_le input rows repeats e.1⟩

theorem right_atIndex_bound
    (source : PreliminarySampler.Questions branch n t (NormalizedSourceInput.clauseCount input))
    (i : Fin D) :
    KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows (sourceSigns clauses source) i)
      .right (SignedTupleSemantics.sourceIDs source)
      (SignedTupleSemantics.sourceVariables clauses source)) := by
  let e := SignedTupleSemantics.occurrenceAt clauses rows repeats hn hbranch hrows δ source i
  have same := SignedTupleSemantics.right_key clauses rows repeats hn hbranch hrows δ e
  simp only [e, SignedTupleSemantics.descriptorOf_occurrenceAt,
    SignedTupleSemantics.occurrenceAt_source] at same
  rw [same]
  exact ⟨SourceKeyBounds.right_retained_length input rows repeats e.1,
    SourceKeyBounds.right_entryID_le input rows repeats e.1⟩

theorem left_prefix_bound (earlier : List C) (tail : List Bool) :
    KeysBound T (dataOfPrefix earlier tail).leftKeys := by
  intro key present
  change key ∈ earlier.map _ at present
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
  exact ⟨SourceKeyBounds.left_retained_length input rows repeats e.1,
    SourceKeyBounds.left_entryID_le input rows repeats e.1⟩

theorem right_prefix_bound (earlier : List C) (tail : List Bool) :
    KeysBound T (dataOfPrefix earlier tail).rightKeys := by
  intro key present
  change key ∈ earlier.map _ at present
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp present
  exact ⟨SourceKeyBounds.right_retained_length input rows repeats e.1,
    SourceKeyBounds.right_entryID_le input rows repeats e.1⟩

theorem bodyBudget_le_envelope {Extra : Type} [DecidableEq Extra]
    (indices : NormalizedTarget.SourceTuple (branch := branch) (n := n) (t := t) input)
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (physical : SignedTupleLayout.Input input.formula indices base)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ localOrder (NormalizedTarget.tupleQuestion input indices) ++ suffix) :
    SignedTupleBodyMachine.bodyBudget
        (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows input.formula indices base
        (dataOfPrefix earlier tail) ≤ SignedCostEnvelope.bodyBound width D T := by
  let source := NormalizedTarget.tupleQuestion input indices
  have countBound : earlier.length + D ≤ D * (T + 1) ^ width := by
    have total := completedOrder_length_le (t := t) input rows repeats hn hbranch hrows δ
    rw [split, List.length_append, List.length_append,
      CompletedVisitOrder.localOrder_length] at total
    omega
  have ids_eq : SignedTupleLayout.ids input.formula indices =
      SignedTupleSemantics.sourceIDs source := by
    simp only [source, NormalizedTarget.tupleQuestion, SignedTupleSemantics.sourceIDs_tuple]
    rfl
  have vars_eq : SignedTupleLayout.vars input.formula indices =
      SignedTupleSemantics.sourceVariables clauses source := by
    simp only [source, NormalizedTarget.tupleQuestion, SignedTupleSemantics.sourceVariables_tuple]
    rfl
  have selectedLeft (i : Fin D) : KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows
        (SourceTupleScheduleMachine.sourceSigns input.formula indices) i)
      .left (SignedTupleLayout.ids input.formula indices) (SignedTupleLayout.vars input.formula indices)) := by
    rw [NormalizedTarget.sourceSigns_eq, ids_eq, vars_eq]
    exact left_atIndex_bound input rows repeats hn hbranch hrows δ source i
  have selectedRight (i : Fin D) : KeyBound T (CompletedEdgeMachine.key hq large
      (SignedScheduleIndex.atIndex hq large hn hbranch hrows
        (SourceTupleScheduleMachine.sourceSigns input.formula indices) i)
      .right (SignedTupleLayout.ids input.formula indices) (SignedTupleLayout.vars input.formula indices)) := by
    rw [NormalizedTarget.sourceSigns_eq, ids_eq, vars_eq]
    exact right_atIndex_bound input rows repeats hn hbranch hrows δ source i
  have leftCount : (dataOfPrefix earlier tail).leftKeys.length +
      (SignedTupleBodyMachine.allStages (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hn hbranch hrows).length ≤ D * (T + 1) ^ width := by
    simpa only [SignedTupleSemantics.dataOfPrefix, ExactTargetOnlineEncoding.leftKeys,
      List.length_map, SignedTupleBodyMachine.allStages, List.length_ofFn] using countBound
  have rightCount : (dataOfPrefix earlier tail).rightKeys.length +
      (SignedTupleBodyMachine.allStages (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hn hbranch hrows).length ≤ D * (T + 1) ^ width := by
    simpa only [SignedTupleSemantics.dataOfPrefix, ExactTargetOnlineEncoding.rightKeys,
      List.length_map, SignedTupleBodyMachine.allStages, List.length_ofFn] using countBound
  have folded := fold_budget_le hq large hn hbranch hrows T (D * (T + 1) ^ width)
    (SourceTupleScheduleMachine.sourceSigns input.formula indices)
    (SignedTupleLayout.ids input.formula indices) (SignedTupleLayout.vars input.formula indices)
    SignedTupleLayout.metadata SignedTupleLayout.Tape.edgeWork SignedTupleLayout.Tape.edgeCount
    (SignedTupleLayout.preparedTapes input.formula indices base)
    (SignedSourceCost.prepared_sourceLength_le input indices base physical)
    selectedLeft selectedRight (SignedTupleBodyMachine.allStages hn hbranch hrows)
    (dataOfPrefix earlier tail)
    (left_prefix_bound input rows repeats hn hbranch hrows δ earlier tail)
    (right_prefix_bound input rows repeats hn hbranch hrows δ earlier tail) leftCount rightCount
  have preparation := SignedTuplePreparationMachine.budget_le width T
  unfold SignedTupleBodyMachine.bodyBudget SignedCostEnvelope.bodyBound
  change 1 + SignedTuplePreparationMachine.budget width T + _ + 7 * width * (T + 2) + 1 ≤ _
  simp only [SignedTupleBodyMachine.allStages, List.length_ofFn] at folded ⊢
  change _ ≤ D * (2 * SignedCostEnvelope.endpointBound width T (D * (T + 1) ^ width) + 4)
    at folded
  omega

theorem bodyBudget_le_polynomial {Extra : Type} [DecidableEq Extra]
    (indices : NormalizedTarget.SourceTuple (branch := branch) (n := n) (t := t) input)
    (base : SignedTupleLayout.Tape width Extra → List Bool)
    (physical : SignedTupleLayout.Input input.formula indices base)
    (earlier suffix : List C) (tail : List Bool)
    (split : order = earlier ++ localOrder (NormalizedTarget.tupleQuestion input indices) ++ suffix) :
    SignedTupleBodyMachine.bodyBudget
        (branch := branch) (n := n) (t := t) («q» := q) (rows := rows) (repeats := repeats)
        hq large hn hbranch hrows input.formula indices base
        (dataOfPrefix earlier tail) ≤
      SignedCostEnvelope.bodyCoeff width D * (T + 1) ^ SignedCostEnvelope.degree width :=
  (bodyBudget_le_envelope input rows repeats hn hbranch hrows δ
    indices base physical earlier suffix tail split).trans (SignedCostEnvelope.bodyBound_le width D T)

theorem outerBudget_le_polynomial :
    (SignedCostEnvelope.bodyCoeff width D * (T + 1) ^ SignedCostEnvelope.degree width +
        2 * width) * (NormalizedSourceInput.clauseCount input) ^ width ≤
      (SignedCostEnvelope.bodyCoeff width D + 2 * width) *
        (T + 1) ^ (SignedCostEnvelope.degree width + width) := by
  have visits : (NormalizedSourceInput.clauseCount input) ^ width ≤ (T + 1) ^ width :=
    Nat.pow_le_pow_left ((SourceKeyBounds.clauseCount_le_bits input).trans (Nat.le_succ T)) width
  have positive : 1 ≤ (T + 1) ^ SignedCostEnvelope.degree width :=
    Nat.one_le_pow _ _ (Nat.succ_pos T)
  have overhead : 2 * width ≤ 2 * width * (T + 1) ^ SignedCostEnvelope.degree width := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * width) positive
  calc
    _ ≤ ((SignedCostEnvelope.bodyCoeff width D + 2 * width) *
        (T + 1) ^ SignedCostEnvelope.degree width) * (T + 1) ^ width := by
      apply Nat.mul_le_mul _ visits
      rw [Nat.add_mul]
      exact Nat.add_le_add_left overhead _
    _ = _ := by rw [Nat.pow_add]; ring

end

end PerfectCompleteness.SignedRuntimeBounds

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOdometer
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ExactTargetOdometer


open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section Native

variable {branch : Nat → Nat} {n t : Nat}
  (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
  (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "width" => TreeCanonical.locationCount branch n t

variable {Extra : Type} [DecidableEq Extra]

local notation "runProgram" => program (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ
local notation "entry" => body (branch := branch) (n := n) (t := t)
  (Extra := Extra) rows repeats hn hbranch hrows δ

local notation "cfg" => configuration rows repeats hn hbranch hrows δ

def enumerateInTimeOfBound (input : NormalizedSourceInput.Input)
    (data : SignedTupleBodyMachine.Data width) (extra : Extra → List Bool) (B : Nat)
    (costs : CostsAtMost rows repeats hn hbranch hrows δ input extra B width
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data) :
    StateTransition.EvalsToInTime (Turing.TM2.step runProgram)
      (cfg entry input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data extra)
      (some (cfg .exit input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩)
        (result rows repeats hn hbranch hrows δ input data) extra))
      ((B + 2 * width) * NormalizedSourceInput.clauseCount input ^ width) := by
  let witness := existsTree rows repeats hn hbranch hrows δ input extra B width (Nat.le_refl _)
    (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (fun _ _ => rfl) data costs
  let tree := Classical.choose witness
  have bounded := Classical.choose_spec witness
  refine { steps := tree.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · change (MachineComposition.advance (Turing.TM2.step runProgram))^[tree.steps]
      (some (cfg entry input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) data extra)) = _
    simpa only [checkAt, Nat.lt_irrefl, ↓reduceDIte, result] using tree.trace
  · exact tree.steps_le_power (NormalizedSourceInput.clauseCount_positive input) B bounded

end Native

noncomputable section Semantics

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
    (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "localOrder" => CompletedVisitOrder.localOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "pack" => SignedTupleSemantics.dataOfPrefix
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ

theorem result_dataOfPrefix (tail : List Bool) :
    ExactTargetOdometer.result rows repeats hn hbranch hrows δ input (pack [] tail) =
      pack order tail := by
  let digits : Fin width → Fin (NormalizedSourceInput.clauseCount input) :=
    fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩
  let xs := ExactTargetOdometer.visits width digits
  have chronology : xs.flatMap
      (fun indices => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) = order :=
    ExactTargetOdometer.visits_completedOrder (t := t)
      (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ digits
  have split : order = [] ++ xs.flatMap
      (fun indices => localOrder
        (SourceQuestionOrder.tupleToQuestion (branch := branch) (n := n) (t := t) indices)) ++ [] := by
    simpa only [List.nil_append, List.append_nil] using chronology.symm
  have folded := fold_tupleSteps_dataOfPrefix rows repeats hn hbranch hrows δ input
    xs [] [] tail split
  change xs.foldl
      (fun data indices =>
        ExactTargetOdometer.tupleStep rows repeats hn hbranch hrows δ input indices data)
      (pack [] tail) = pack order tail
  simpa only [List.nil_append, chronology] using folded

end Semantics

noncomputable section ChronologicalCosts

variable {branch : Nat → Nat} {n t : Nat}
    (rows repeats : Nat → Nat) (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)
    (input : NormalizedSourceInput.Input)

local notation "width" => TreeCanonical.locationCount branch n t
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ
local notation "pack" => SignedTupleSemantics.dataOfPrefix
  (t := t) (NormalizedSourceInput.clauses input) rows repeats hn hbranch hrows δ

variable {Extra : Type} [DecidableEq Extra]

local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "D" => SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q

def targetInTimePolynomial (tail : List Bool) (extra : Extra → List Bool) :
    StateTransition.EvalsToInTime
      (Turing.TM2.step (program (branch := branch) (n := n) (t := t)
        (Extra := Extra) rows repeats hn hbranch hrows δ))
      (configuration rows repeats hn hbranch hrows δ
        (body (branch := branch) (n := n) (t := t) (Extra := Extra) rows repeats hn hbranch hrows δ)
        input (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) extra)
      (some (configuration rows repeats hn hbranch hrows δ .exit input
        (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack order tail) extra))
      (timeBound (branch := branch) (n := n) (t := t)
        rows repeats hn hbranch hrows δ (NormalizedSourceInput.bits input).length) := by
  let B := SignedCostEnvelope.bodyCoeff width D *
    ((NormalizedSourceInput.bits input).length + 1) ^ SignedCostEnvelope.degree width
  have bounded : CostsAtMost rows repeats hn hbranch hrows δ input extra B width
      (fun _ => ⟨0, NormalizedSourceInput.clauseCount_positive input⟩) (pack [] tail) := by
    apply costsAtMost_full rows repeats hn hbranch hrows δ input extra B tail
    intro indices before after split
    simpa only [leafBudget] using SignedRuntimeBounds.bodyBudget_le_polynomial (t := t)
      input rows repeats hn hbranch hrows δ indices (baseTapes input indices extra)
      (baseTapes_input input indices extra) before after tail split
  let run := enumerateInTimeOfBound rows repeats hn hbranch hrows δ input
    (pack [] tail) extra B bounded
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [result_dataOfPrefix] using run.evals_in_steps
  · exact run.steps_le_m.trans
      (SignedRuntimeBounds.outerBudget_le_polynomial (t := t) input rows repeats hn hbranch hrows δ)

end ChronologicalCosts
end PerfectCompleteness.ExactTargetOdometer

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

def calls {δ : ℚ} (plan : Plan δ) : Nat :=
  2 * FixedCallBudget.budget plan.depth (rows plan) (repeats plan) + 1

structure Parameters (δ : ℚ) (positive : 0 < δ) where
  plan : Plan δ
  accuracy : ℝ
  accuracy_pos : 0 < accuracy
  accuracy_small : ∀ j ≤ plan.depth, accuracy < CommonAccuracy.tolerance plan j
  alphabetCost : Nat
  alphabetCost_pos : 0 < alphabetCost
  alphabetCost_bound : SourceOddLists.alphabetLog (cutoff plan positive)
    (sourceLength plan positive) ≤ alphabetCost
  cubeSize : Nat → Nat
  cube_errors : ∀ n,
    CubeErrors
      (ChildBlockCardinality.bound (fun k => cubeSize k ^ 3) n
        (sourceLength plan positive) (calls plan) (rows plan) : ℝ)
      (FixedBranching.cleanRate alphabetCost
        (ChildBlockCardinality.bound (fun k => cubeSize k ^ 3) n
          (sourceLength plan positive) (calls plan) (rows plan) : ℝ))
      accuracy (cubeSize n)

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

def branch (n : Nat) : Nat := p.cubeSize n ^ 3

theorem branch_pos (n : Nat) : 0 < branch p n := by
  have h := (p.cube_errors n).1
  unfold branch
  positivity

end
end PerfectCompleteness.FixedParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedPreliminaryGame

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem depth_pos : 0 < p.plan.depth := by have := p.plan.depth_ge; omega

theorem rows_pos (height : Nat) : 0 < rows p.plan height :=
  lt_of_lt_of_le Nat.zero_lt_one (p.plan.rows_pos (p.plan.depth - height))

def value (input : List Bool) : ℝ :=
  PreliminaryOutput.value (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1))

end
end PerfectCompleteness.FixedPreliminaryGame


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

def alphabet : Nat :=
  FinitePreliminaryCompletion.alphabet (branch p) p.plan.depth
    (sourceLength p.plan hδ) δ

theorem alphabet_ge_two : 2 ≤ alphabet p :=
  CanonicalLocalCompletion.alphabet_ge_two
    (TreeCanonical.locationCount (branch p) p.plan.depth (sourceLength p.plan hδ)) δ

def construct (input : List Bool) : Instance (alphabet p) :=
  NormalizedTarget.construct (branch := branch p) (n := p.plan.depth)
    (t := sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1)) δ
    (NormalizedSourceInput.raw input)

end
end PerfectCompleteness.FixedTarget

end

end OAI
end


