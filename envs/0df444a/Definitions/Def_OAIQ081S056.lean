-- Prove2me | Definitions.Def_OAIQ081S056
-- name    : OAIQ081S056
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:44:38.025999+00:00
-- url     : https://prove2.me/theorems/516940b6-7c93-423f-b86b-4d36d351701c
-- title:
--   Definitions bundle OAIQ081S056 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 108 definitions and 39 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.headOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IncidenceHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Literal.callLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Literal.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.readSignedCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.clearWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.readCached`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.reset`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.equalityProgram`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.finishCommand`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.sealCommand`, `OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryCompare.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryCompare.equality`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.emitPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.readCounter`, `OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram.lookup`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.cleanup`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.copy`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.coveredBody`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.finish`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.frame`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.header`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.leftoverBody`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.load`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.parse`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.transfer`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMetadata.volume`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.check`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.equality`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorGuardProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.read`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readOne`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixColorReadProgram.pull` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProducedMatrix`, `SubexponentialSAT_SqrtLog_LayoutProgramArrays`, `SubexponentialSAT_SqrtLog_LayoutProgramLiteral`, `SubexponentialSAT_SqrtLog_LayoutProgramPadded`, `SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic`, `SubexponentialSAT_SubexpHornerProgram`, `SubexponentialSAT_SubexpPlanAlphabetProgram`, `SubexponentialSAT_SubexpTupleRefinement`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_ConstraintEntryCompare`, `SubexponentialSAT_Subexp_ConstructivePacking`, `SubexponentialSAT_Subexp_DimensionProgram`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_MatrixAnchorGuardProgram`, `SubexponentialSAT_Subexp_MatrixAnchorReadProgram`, `SubexponentialSAT_Subexp_MatrixAnchorTypes`, `SubexponentialSAT_Subexp_MatrixColorReadProgram`, `SubexponentialSAT_Subexp_MatrixEntryCore`, `SubexponentialSAT_Subexp_MatrixEntryFrames`, `SubexponentialSAT_Subexp_MatrixExtendedEntryProgram`, `SubexponentialSAT_Subexp_MatrixInputAccess`, `SubexponentialSAT_Subexp_MatrixInputProgram`, `SubexponentialSAT_Subexp_MatrixPositionProgram`, `SubexponentialSAT_Subexp_MatrixProgramSupport`, `SubexponentialSAT_Subexp_MatrixScanStepProgram`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingEntryEmitter`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionCallback`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingFrameCount`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftoverStage`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingOutputSemantics`, `SubexponentialSAT_Subexp_PackingProgramSupport`, `SubexponentialSAT_Subexp_PackingUnaryMin`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_SelectorMapProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034`, `OAIQ081S035` and `OAIQ081S036` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S070`, `OAIQ081S073`, `OAIQ081S074`, `OAIQ081S075`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079` and `OAIQ081S081`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S034
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S036

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable complete-block packing

All execution definitions use supplied finite lists, filtering, minimum scans,
indexed list access, and index lookup. No execution definition uses classical
choice or an abstract inverse. Mathematical cardinalities occur only in proofs.
-/

namespace SubexponentialSAT.Subexp.ConstructivePacking

open scoped BigOperators

namespace PackingData

variable {V U : Type*} [DecidableEq U]

variable [DecidableEq V]

theorem leftovers_nodup (P : PackingData V U) : P.leftovers.Nodup :=
  P.vertices.nodup.filter _

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Representation and coverage of the fixed tuple program

The tuple program reverses its record order at each Cartesian expansion.
These theorems retain that actual order and show that it is a permutation of
the explicit coefficient-vector enumeration. Fixed-width injective encodings
then give uniqueness, not just coverage.
-/

namespace SubexponentialSAT.SubexpTupleRefinement

open Subexp.TupleProgram

/-- The actual fixed-control tuple program enumerates precisely the encoded
vectors for any fixed-width code, in its own explicit order. -/
theorem powerRows_encoded_perm {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (n : ℕ) :
    (powerRows (alphabet.map code.block) n [[]]).Perm
      ((QuarticSearch.vectors alphabet n).map (encodeTuple code)) := by
  have h := powerRows_empty_perm (alphabet.map code.block) n
  rw [vectors_map, List.map_map] at h
  simpa only [Function.comp_def, tuplePayload_map] using h

theorem powerRows_encoded_nodup {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (h : alphabet.Nodup) (n : ℕ) :
    (powerRows (alphabet.map code.block) n [[]]).Nodup := by
  apply (powerRows_encoded_perm code alphabet n).nodup_iff.mpr
  exact (SubexpVectorEnumeration.vectors_nodup alphabet h n).map
    (encodeTuple_injective code n)

theorem mem_powerRows_encoded {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (n : ℕ) (bits : List Bool) :
    bits ∈ powerRows (alphabet.map code.block) n [[]] ↔
      ∃ v ∈ QuarticSearch.vectors alphabet n, encodeTuple code v = bits := by
  rw [(powerRows_encoded_perm code alphabet n).mem_iff, List.mem_map]

/-- Every requested tuple is visited when the scalar alphabet is complete. -/
theorem encodeTuple_mem_powerRows {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (hfull : ∀ a, a ∈ alphabet) (n : ℕ) (v : Fin n → A) :
    encodeTuple code v ∈ powerRows (alphabet.map code.block) n [[]] := by
  rw [mem_powerRows_encoded]
  exact ⟨v, QuarticSearch.mem_vectors alphabet hfull n v, rfl⟩

end SubexponentialSAT.SubexpTupleRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_DimensionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed generator for all unary dimensions from zero through a runtime bound

The input bound is a unary stack, and the output is a framed list of unary
payloads. The program has no bound-dependent control labels.
-/

namespace SubexponentialSAT.Subexp.DimensionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram

def emitPorts : RecordPrograms.Ports 5 5 :=
  ⟨2, 3, 4, 2, 3, by decide, by decide, by decide, by decide⟩

abbrev readCounter : Cmd 5 5 := RecordPrograms.atom (.pop 0 0 1)

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

open BitProgram StackRoutines StructuredCalls

abbrev lookup : Cmd 3 10 :=
  .call (ProgramLinking.liftProgram
    (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1) id lookupPort)

/-- The parser supplies a reversed unary index. Only its length is read.
Each selected row is reversed into the growing accumulator on stack 9. -/
abbrev callback : Cmd 3 10 :=
  .seq lookup (.seq (.call (transferProgram (1 : Fin 10) 9 (0 : Fin 3) 1))
    (RecordPrograms.atom (.set 1 true)))

theorem transfer_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (regs : Fin 3 → Bool) (stk : Stacks (Fin 10)) :
    Eval (.call (transferProgram src dst (0 : Fin 3) 1)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have t := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 3) 1 hsd (by decide) regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using t

def effect (rows : List (List Bool)) (bits : List Bool) (a b : State 3 10) : Prop :=
  b.stacks 9 = (rows.getD bits.length []).reverse ++ a.stacks 9

theorem encoded_plan_length (plan : List ℕ) :
    (ProgramEncoding.encodeRecords (indexRecords plan)).length =
      2 * plan.sum + 2 * plan.length + 1 := by
  rw [ProgramEncoding.encodeRecords_length]
  have hm : (indexRecords plan).map List.length = plan := by
    simp [indexRecords, List.map_map, Function.comp_def]
  rw [hm]
  simp [indexRecords]

theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

/-- A polynomial bound in actual serialized width and plan data. In particular,
even a zero-width array needs no unencoded row-count parameter in the bound. -/
theorem traceCost_le_serialized (rows : List (List Bool)) (width : ℕ) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width) (hplan : ∀ i ∈ plan, i < rows.length) :
    traceCost rows width plan ≤
      100 * (width + (ProgramEncoding.encodeRecords (indexRecords plan)).length + 1)^2 := by
  let t := width + (ProgramEncoding.encodeRecords (indexRecords plan)).length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hw : width ≤ t := by dsimp [t]; omega
  have hs : plan.sum ≤ t := by dsimp [t]; rw [encoded_plan_length]; omega
  have hp : plan.length ≤ t := by dsimp [t]; rw [encoded_plan_length]; omega
  have heq : traceCost rows width plan =
      7 + (14 * width + 16) * plan.sum + (21 * width + 27) * plan.length := by
    rw [traceCost, iterator_budget_eq, gathered_length rows plan width hrows hplan]
    ring
  rw [heq]
  have hmono : 7 + (14 * width + 16) * plan.sum + (21 * width + 27) * plan.length ≤
      7 + (14 * t + 16) * t + (21 * t + 27) * t := by gcongr
  have ht2 : t ≤ t^2 := by nlinarith
  exact hmono.trans (by change _ ≤ 100 * t^2; nlinarith)

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

abbrev equalityProgram : Program 5 13 10 :=
  ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram id equalityPorts

abbrev finishCommand : Cmd 5 13 :=
  .seq (.call (clearProgram (1 : Fin 13) (0 : Fin 5) 1))
    (.seq (.call (clearProgram (12 : Fin 13) (0 : Fin 5) 1))
      (.seq (.base (.atom (.push 11 4)))
        (.seq (.base (.atom (.set 2 false)))
          (.seq (.base (.atom (.set 3 false))) (.base (.atom (.set 4 false)))))))

abbrev sealCommand : Cmd 5 13 := .seq (.call equalityProgram) finishCommand

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentAlphabetSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator order is retained in the initializer alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

open OneHotAlphabetProgram MulticolorTypes

theorem wordBytes_nodup {r : ℕ} (hr : 0 < r) (Q : ℕ) : (wordBytes r Q).Nodup := by
  rw [wordBytes, rows_eq_alphabet]
  exact SubexpTupleRefinement.powerRows_encoded_nodup (colorCode hr)
    (List.finRange r).reverse (List.nodup_reverse.mpr (List.nodup_finRange r)) Q

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPadded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A computable integer row for every incidence position. Inactive covered
positions and non-head uncovered positions are zero. Active rows are precisely
the raw block constraints, with repetitions and zero padding permitted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q : ℕ} {I O : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]

abbrev IncidenceHead (P : PackingData I (UniversalType r Q 1))
    (t : Fin Q) (g : Fin r) := {v : I // (P.label v).head t = g}

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputAccess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

open BitProgram StructuredCalls StackRoutines

abbrev read : Cmd 8 29 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1) id low)

abbrev replace : Cmd 8 29 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1) id low)

abbrev clear (src : Fin 29) : Cmd 8 29 := .call (clearProgram src 0 1)

def equalityInner := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11
abbrev equality : Cmd 8 29 :=
  .seq (.call (ProgramLinking.liftProgram equalityInner eqRegs eqPorts))
    (.seq (.base (.atom (.pop 11 7 0))) (.base (.atom (.set 0 false))))

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the selected color from each of four preserved word streams. The
position is a unary runtime cursor on stack37; color width is on stack21. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines

abbrev read : Cmd 10 42 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 10) 1) id low)

abbrev clear (src : Fin 42) : Cmd 10 42 := .call (clearProgram src 0 1)

abbrev readOne (i : Fin 4) : Cmd 10 42 :=
  .seq (copy (source i) 0) (.seq (copy 21 3) (.seq (copy 37 2)
    (.seq read (.seq (move 1 (target i)) (.seq (clear 0) (clear 3))))))

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

abbrev readFour : Cmd 10 42 := .seq (readOne 0) (.seq (readOne 1) (.seq (readOne 2) (readOne 3)))

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual integer entry program is a literal owner-fiber sum. Restricting
its columns to the emitted head IDs has exactly the canonical pulled row span,
up to harmless column omission/repetition. All incidence rows are retained. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutProgram

variable {r Q : ℕ} {I V O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [CommRing O]
variable {node : Fin Q → O}

def headOwner (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i)) (t : Fin Q) (g : Fin r) :
    IncidenceHead P t g → {v : V // head t v=g} :=
  LayoutHeadPullback.headOwner owner (fun i=>(P.label i).head t) (head t)
    (fun i=>hhead i t) g

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical access to the two-array integer matrix ABI. Every array entry is a
runtime-width binary word; its signed value is positive minus negative. The
fixed program below preserves both arrays, the index and width. It does not
assume a unit-cost array lookup or add an integer primitive to the machine. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.ArrayUpdateLifted

/-- Source arrays 0,1; preserved unary index 2; temporary index 3; preserved
unary width 4; positive/negative outputs 5,6; scratch 7--10. -/
abbrev readSignedCommand : Cmd 2 11 :=
  .seq (.call (copyProgram 2 3 7 0 1))
    (.seq (.call (readProgramAt positivePorts 0 1))
      (.seq (.call (copyProgram 2 3 7 0 1))
        (.call (readProgramAt negativePorts 0 1))))

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control source generation for factored Horner expressions

Input payloads are coefficient representations, never precomputed instruction
streams. The emitter writes the actual serialized postfix tags and frames.
-/

namespace SubexponentialSAT.SubexpHornerProgram

open BitProgram

namespace Literal

/-- Ports: payload 0, reverse output 1, empty scratch 2. -/
abbrev program : Program 3 3 13 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .set 0 false 2
    | 2 => .push 1 0 3
    | 3 => .pop 0 0 1 4
    | 4 => .branch 1 5 8
    | 5 => .push 2 0 6
    | 6 => .push 1 2 7
    | 7 => .push 1 0 3
    | 8 => .push 1 0 9
    | 9 => .pop 2 0 1 10
    | 10 => .branch 1 11 12
    | 11 => .push 0 0 9
    | _ => .halt

end Literal

end SubexponentialSAT.SubexpHornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid preserving conversion of one scalar word into a complete forward
postfix literal. This is used for uncovered identity entries and zero branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Literal

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev callLiteral : Cmd 3 4 := .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id ports)
abbrev command : Cmd 3 4 := .seq callLiteral (.call (StackRoutines.transferProgram 1 3 0 1))

end SubexponentialSAT.SqrtLog.LayoutProgram.Literal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstraintEntryCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compare the two preserved universal-type byte arrays without changing
the scalar result or any input stack of the matrix-entry service. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryCompare

open BitProgram StructuredCalls StackRoutines

abbrev equality : Cmd 10 46 :=
  liftCommand MatrixInputAccess.equality 0 0 registers ports

abbrev command : Cmd 10 46 := .seq (copy 23 43) (.seq (copy 24 44) equality)

end SubexponentialSAT.Subexp.ConstraintEntryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving comparison of the two type words using scratch0..3. All cache
ports42..48 remain intact. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev command : Cmd 10 64 := liftCommand ConstraintEntryCompare.command 23 23 id ports

end SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

abbrev Data (s : ℕ) := StructuredProgram.State 8 s

theorem transfer_eval (src dst : Fin s) (h : src ≠ dst) (d : Data s) :
    ∃ e, Eval (transfer src dst) (3 * (d.stacks src).length + 3) d e ∧
      e.stacks = StackRoutines.transferStacks src dst d.stacks := by
  let e : Data s := ⟨readRegs d.regs 0 1 none,
    StackRoutines.transferStacks src dst d.stacks⟩
  have ht := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1
    h (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 3 rfl rfl
  refine ⟨e, .call _ ?_, rfl⟩
  simpa [e, StackRoutines.transferResult, StructuredProgram.State.withPC,
    StackRoutines.transferProgram, Nat.add_assoc] using hh

theorem copy_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp = []) :
    ∃ e, Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d e ∧
      e.stacks = StackRoutines.copyStacks src dst d.stacks := by
  let e : Data s := ⟨readRegs d.regs 0 1 none,
    StackRoutines.copyStacks src dst d.stacks⟩
  have hc := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1
    hsd hst htd (by decide) d.regs d.stacks ht
  have hh := StackRoutines.halt_after_trace _ hc 7 rfl rfl
  refine ⟨e, .call _ ?_, rfl⟩
  simpa [e, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def readCached (binomial : Bool) : Code :=
  liftCommand LayoutProgram.readSignedCommand 0 5 smallRegisters (readPorts binomial)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def clearWork : Code := .seq (.call (StackRoutines.clearProgram 11 0 1))
  (.call (StackRoutines.clearProgram 12 0 1))

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramBody.lean

/-! A fixed, paid iteration producing the three real scalar operands. -/

/-! The native unary loop produces all triples in increasing binomial index. -/

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPlanAlphabetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed work bank for the all-vertex plan producer

The protected masters are the encoded scope list, D and Delta. A callback
copies them into the already checked per-vertex machine, emits a double-framed
plan record, and physically clears the work bank before the next vertex.
-/
namespace SubexponentialSAT.SubexpPlanAlphabetBase

open BitProgram StructuredCalls

def scopeBytes (scopes : List (List ℕ)) : List Bool :=
  Encoding.encodeList SubexpIncidencePlanScan.scopeBytes scopes

end SubexponentialSAT.SubexpPlanAlphabetBase

/-! A closed callback for producing one framed forward vertex plan. -/

/-! A physical record iterator invokes the closed plan-producing callback. -/

/-!
# Actual all-vertices forward-plan alphabet

The machine generates the vertex indices itself from unary D, in descending
order. The checked callback prepends its output, so the final alphabet is in
ascending vertex order. Every alphabet payload is a framed forward read plan.
-/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentSeedRange
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ascending framed unary seed indices from a runtime unary seed count. -/

namespace SubexponentialSAT.Subexp.AssignmentSeedRange

open BitProgram StructuredCalls TupleProgram

abbrev reset : Cmd 5 6 := .base (CandidateScoreProgram.resetList (List.finRange 5))

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


def copy (src dst : Fin 12) : Code := .call (StackRoutines.copyProgram src dst 11 0 1)
def transfer (src dst : Fin 12) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def clear (src : Fin 12) : Code := .call (StackRoutines.clearProgram src 0 1)

def load : Code := .seq (copy 0 5) (.seq (copy 1 6) (transfer 6 7))

def cleanup : Code := .seq (clear 5) (.seq (clear 7) (transfer 6 5))

def frame (src dst : Fin 12) : Code :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram parserReg (parserPort src dst))

def header : Code := .base (.atom (.pop 5 4 0))
def coveredBody : Code := .seq (frame 5 6)
  (.seq (transfer 6 2) (.seq (frame 5 6) (transfer 6 3)))
def leftoverBody : Code := .seq (frame 5 6) (transfer 6 4)
def finish : Code := RegisterResetProgram.clear [0, 1, 2, 3]
def parse : Code := .seq header (.seq (.ite 4 coveredBody leftoverBody) finish)

def volume (records : List (List Bool × List Bool)) (query : List Bool) : ℕ :=
  (SelectorProgram.rawRecords records).length + query.length + 1

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical comparison of the two color pairs at one matrix position.
The four color words occupy stacks 13--16. They are preserved. Actual copies,
the existing bit-equality table, and actual cleanup produce the comparison
bits; no semantic equality callback is assumed. -/

namespace SubexponentialSAT.Subexp.MatrixPositionProgram

open BitProgram StructuredCalls StackRoutines

def equalityInner := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11

abbrev equality : Cmd 8 17 := .call
  (ProgramLinking.liftProgram equalityInner smallRegs smallStacks)

abbrev comparePair (swapped : Bool) : Cmd 8 17 := .seq (prepare swapped) equality

end SubexponentialSAT.Subexp.MatrixPositionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Three physical byte comparisons for the selected joint coordinate. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

open BitProgram StructuredCalls StackRoutines

abbrev equality : Cmd 10 42 := .call
  (ProgramLinking.liftProgram MatrixPositionProgram.equalityInner eqRegs eqStacks)

abbrev check (left right : Fin 4) (expected : Bool) : Cmd 10 42 :=
  .seq (copy (slot left) 1) (.seq (copy (slot right) 12)
    (.seq equality (.seq pop (accept expected))))

abbrev command : Cmd 10 42 :=
  .seq (.base (.atom (.set 9 true)))
    (.seq (check 0 2 true) (.seq (check 1 2 false) (check 3 2 false)))

def program := compiled command 38 38

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixColorReadProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed program that consumes one color word from each of the four
matrix-input streams. The word width is supplied as a unary stack. -/

namespace SubexponentialSAT.Subexp.MatrixColorReadProgram

open BitProgram StructuredCalls StackRoutines ArrayPrograms

abbrev take (src : Fin 23) : Cmd 8 23 :=
  .call (countedTransferProgram 10 src 4 0 1)

abbrev pull (src dst : Fin 23) : Cmd 8 23 :=
  .seq copyWidth (.seq (take src) (restore dst))

abbrev pullFour : Cmd 8 23 :=
  .seq (pull 17 13) (.seq (pull 18 14) (.seq (pull 19 15) (pull 20 16)))

end SubexponentialSAT.Subexp.MatrixColorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed arithmetic workspace and subroutines of the joint-entry program. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 9 37

abbrev callLow {s l : ℕ} (p : Program 8 s l) (hs : s ≤ 37) : Code :=
  .call (ProgramLinking.liftProgram p lowRegisters (Fin.castLE hs))

def input (regs : Fin 9 → Bool)
    (colorWidth positions left right index rowWidth modulus zero coefficients count : List Bool) : Data :=
  ⟨regs, fun j =>
    if j = 21 then colorWidth else if j = 22 then positions
    else if j = 23 then left else if j = 24 then right
    else if j = 25 then index else if j = 26 then rowWidth
    else if j = 29 then modulus else if j = 30 then zero
    else if j = 31 then coefficients else if j = 32 then count else []⟩

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port execution rules used to assemble the concrete entry program.
The call rule consumes a trace of the supplied actual subprogram. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def install {s : ℕ} (a : Data) (b : State 8 s) : Data :=
  ⟨fun j => if h : j.val < 8 then b.regs ⟨j.val, h⟩ else a.regs j,
    fun j => if h : j.val < s then b.stacks ⟨j.val, h⟩ else a.stacks j⟩

@[simp] theorem install_stack_low {s : ℕ} (hs : s ≤ 37) (a : Data) (b : State 8 s) (j : Fin s) :
    (install a b).stacks (j.castLE hs) = b.stacks j := by simp [install, j.isLt]

@[simp] theorem install_reg8 {s : ℕ} (a : Data) (b : State 8 s) :
    (install a b).regs 8 = a.regs 8 := rfl

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanStepProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

abbrev clear (i : Fin 23) : Cmd 8 23 := .call (clearProgram i 0 1)

abbrev clearWords : Cmd 8 23 := .seq (clear 13) (.seq (clear 14) (.seq (clear 15) (clear 16)))

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Extract head/slot rows and compare the untouched spectator rows. All row
widths and selected-row indices are data; the instruction table is fixed. -/

namespace SubexponentialSAT.Subexp.MatrixInputProgram

open BitProgram StructuredCalls StackRoutines MatrixInputAccess


abbrev extract (second : Bool) : Cmd 8 29 :=
  .seq (copy (sourcePort second) 0) (.seq read
    (.seq (copy 1 (headPort second)) (.seq (clear 1)
      (.seq (copy 25 2) (.seq read
        (.seq (copy 1 (slotPort second)) (clear 1)))))))

abbrev normalize : Cmd 8 29 :=
  .seq (copy 17 1) (.seq replace (.seq (copy 25 2) (.seq replace (clear 1))))

abbrev command : Cmd 8 29 :=
  .seq (copy 26 3) (.seq (extract false) (.seq normalize
    (.seq (copy 0 28) (.seq (clear 0) (.seq (extract true)
      (.seq normalize (.seq equality (clear 3))))))))

def program := compiled command 23 17

end SubexponentialSAT.Subexp.MatrixInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for the zero-extended joint entry on arbitrary universal
types. The unary position cursor is preserved on37. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

abbrev Data := State 10 42

abbrev liftCall {k s l : ℕ} (p : Program k s l) (hk : k ≤ 10) (hs : s ≤ 42) : Code :=
  .call (ProgramLinking.liftProgram p (Fin.castLE hk) (Fin.castLE hs))

def readProgram := compiled MatrixAnchorReadProgram.readFour 17 38
def clear (src : Fin 42) : Code := .call (clearProgram src 0 1)

def clearColors : Code :=
  .seq (clear 17) (.seq (clear 18) (.seq (clear 19) (.seq (clear 20)
    (.seq (clear 38) (.seq (clear 39) (.seq (clear 40) (clear 41)))))))

def guardStage : Code :=
  .seq (liftCall MatrixInputProgram.program (by decide) (by decide))
    (.seq (.call readProgram) (.seq (.call MatrixAnchorGuardProgram.program)
      clearColors))

open BitProgram StructuredCalls StackRoutines

open BitProgram StructuredCalls StackRoutines MulticolorTypes


end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame counter for the complete-block packing controller. -/

namespace SubexponentialSAT.Subexp.PackingFrameCount

open BitProgram StructuredCalls MatrixProgramSupport

abbrev clearPayload : Cmd 8 3 := .call (StackRoutines.clearProgram 1 0 1)

end SubexponentialSAT.Subexp.PackingFrameCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingUnaryMin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed destructive minimum routine for unary packing counts. -/

namespace SubexponentialSAT.Subexp.PackingUnaryMin

open BitProgram StructuredCalls MatrixProgramSupport

abbrev command : Cmd 8 3 :=
  .seq (.call core)
    (.seq (.call (StackRoutines.clearProgram 0 0 1))
      (.call (StackRoutines.clearProgram 1 0 1)))

def program := compiled command 0 2

end SubexponentialSAT.Subexp.PackingUnaryMin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

def ports : RecordPrograms.Ports 8 9 :=
  ⟨5, 6, 7, 6, 2, by decide, by decide, by decide, by decide⟩

def emitPorts : RecordPrograms.Ports 8 9 :=
  ⟨0, 1, 2, 1, 8, by decide, by decide, by decide, by decide⟩

theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (base target : State R S) (inner : State r s)
    (hreg : ∀ i, target.regs (reg i) = inner.regs i)
    (hstk : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = base.regs j)
    (hfs : ∀ j, (¬ ∃ i, stk i = j) → target.stacks j = base.stacks j) :
    embedState reg stk base inner = target := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hr.extend_apply]
      exact (hreg i).symm
    · rw [Function.extend_apply' _ _ _ hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stk i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hs.extend_apply]
      exact (hstk i).symm
    · rw [Function.extend_apply' _ _ _ hj]
      exact (hfs j hj).symm

def callbackCost (records : List (List Bool × List Bool)) (query : List Bool) : ℕ :=
  9 * (SelectorProgram.rawRecords records).length +
    3 * SelectorProgram.budget query records + 2 * query.length +
      5 * (selected records query).length + 18

def budget (records : List (List Bool × List Bool)) (queries : List (List Bool)) : ℕ :=
  6 + RecordPrograms.budget (callbackCost records) queries

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical subroutine calls for the all-type packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketCalls

open BitProgram StructuredCalls MatrixProgramSupport

abbrev minimumCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram PackingUnaryMin.program id minimumPorts)

end SubexponentialSAT.Subexp.PackingBucketCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

def ports : RecordPrograms.Ports 8 15 :=
  ⟨5, 6, 7, 7, 2, by decide, by decide, by decide, by decide⟩

def bucketPayload (records : List BucketProgram.Record) (key : List Bool) : List Bool :=
  Encoding.frame key ++ words (BucketProgram.selected records key)

def table (records : List BucketProgram.Record) (keys : List (List Bool)) : List (List Bool) :=
  keys.map (bucketPayload records)

def budget (records : List BucketProgram.Record) (keys : List (List Bool)) : ℕ :=
  6 + RecordPrograms.budget (callbackCost records) keys +
    3 * (ProgramEncoding.encodeRecords (table records keys)).length + 3

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingEntryEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed emission of one covered packing vertex

The three accumulators are real runtime stacks. Storage receives one reversed
outer record; the two lookup streams receive raw pairs of framed words.
All payloads and counters are data, and every frame is built by fixed programs.
-/
namespace SubexponentialSAT.Subexp.PackingEntryEmitter

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 10

def sequence (commands : List Code) : Code :=
  commands.foldr Cmd.seq (.base .skip)

end SubexponentialSAT.Subexp.PackingEntryEmitter


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual bucket-record callback: select its indexed vertex and emit it. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

def ports : RecordPrograms.Ports 8 19 :=
  ⟨5, 6, 7, 7, 8, by decide, by decide, by decide, by decide⟩

def bucketWord (key : List Bool) (bucket : List (List Bool)) : List Bool :=
  Encoding.frame key ++ words bucket

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scan the ordered type buckets for one complete block. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

def entryWord (e : Entry) : List Bool := bucketWord e.1 e.2

def blockBudget (i : ℕ) : List Entry → Context → ℕ
  | [], _ => 0
  | e :: es, c => 6 * (entryWord e).length + callbackBudget (entryWord e) c.block c.address + 7 +
      blockBudget i es (emitted c e.1 (entryVertex i e))

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem emitEntries_static (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).block = c.block ∧
    (emitEntries i entries c).buckets = c.buckets ∧
    (emitEntries i entries c).remaining = c.remaining := by
  induction entries generalizing c with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e es ih =>
    simpa only [emitEntries, List.foldl_cons, emitted] using
      ih (emitted c e.1 (entryVertex i e))

theorem advanced_static (i : ℕ) (entries : List Entry) (c : Context) :
    (advanced i entries c).block = true :: c.block ∧
    (advanced i entries c).buckets = c.buckets ∧
    (advanced i entries c).remaining = c.remaining.tail := by
  obtain ⟨hb, ht, hr⟩ := emitEntries_static i entries c
  exact ⟨by simp [advanced, hb], by simp [advanced, ht], by simp [advanced, hr]⟩

def bodyBudget (i : ℕ) (entries : List Entry) (c : Context) : ℕ :=
  7 * c.buckets.length + blockBudget i entries c + 12

def loopBudget (entries : List Entry) : ℕ → ℕ → Context → ℕ
  | 0, _, _ => 1
  | n + 1, i, c => bodyBudget i entries c +
      loopBudget entries n (i + 1) (advanced i entries c) + 1

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The records emitted by block extraction have the exact computed packing order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open ConstructivePacking MatrixProgramSupport

def blockRows (i : ℕ) (entries : List Entry) (block : List Bool) :
    List (List Bool × List Bool) :=
  entries.map fun e => (entryVertex i e, PackingEntryEmitter.metadataPayload block e.1)

theorem emitEntries_metadata (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).metadata =
      SelectorProgram.rawRecords (blockRows i entries c.block).reverse ++ c.metadata := by
  induction entries generalizing c with
  | nil => simp [emitEntries, blockRows, SelectorProgram.rawRecords]
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).metadata = _
    rw [ih]
    simp [blockRows, emitted, PackingEntryEmitter.metadataOutput, SelectorProgram.rawRecords,
      List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem emitEntries_address (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).address = List.replicate entries.length true ++ c.address := by
  induction entries generalizing c with
  | nil => rfl
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).address = _
    rw [ih]
    simp only [List.length_cons, List.replicate_add, emitted]
    simp [List.append_assoc]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

open BitProgram StructuredCalls MatrixProgramSupport

def sequence (commands : List Code) : Code :=
  commands.foldr Cmd.seq (.base .skip)

end SubexponentialSAT.Subexp.PackingLeftoverEmitter


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact finite-port framing for the physical packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgramSupport

open BitProgram StructuredCalls

abbrev Data := State 16 48

def project {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48) (a : Data) : State r s :=
  ⟨a.regs ∘ registers hr, a.stacks ∘ stackPorts hs⟩

/-- A computable description of the exact state after a low-port call. -/
def install {r s : ℕ} (_hr : r ≤ 16) (_hs : s ≤ 48) (a : Data) (b : State r s) : Data :=
  ⟨fun i => if h : i.val < r then b.regs ⟨i.val, h⟩ else a.regs i,
   fun i => if h : i.val < s then b.stacks ⟨i.val, h⟩ else a.stacks i⟩

theorem install_register {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin r) :
    (install hr hs a b).regs (registers hr i) = b.regs i := by
  simp [install, registers, i.isLt]

theorem install_stack {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin s) :
    (install hr hs a b).stacks (stackPorts hs i) = b.stacks i := by
  simp [install, stackPorts, i.isLt]

theorem install_register_frame {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin 16) (hi : r ≤ i.val) :
    (install hr hs a b).regs i = a.regs i := by
  simp [install, Nat.not_lt.mpr hi]

theorem install_stack_frame {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) (i : Fin 48) (hi : s ≤ i.val) :
    (install hr hs a b).stacks i = a.stacks i := by
  simp [install, Nat.not_lt.mpr hi]

theorem install_project {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48) (a : Data) :
    install hr hs a (project hr hs a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : i.val < r <;> simp [ project, registers, h]
  · funext i
    by_cases h : i.val < s <;> simp [ project, stackPorts, h]

theorem embed_eq_install {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 48)
    (a : Data) (b : State r s) :
    embedState (registers hr) (stackPorts hs) a b = install hr hs a b := by
  apply SelectorMapProgram.embed_eq _ _ (registers_injective hr) (stackPorts_injective hs)
  · exact install_register hr hs a b
  · exact install_stack hr hs a b
  · intro i hi
    apply install_register_frame
    by_contra hn
    exact hi ⟨⟨i.val, Nat.lt_of_not_ge hn⟩, Fin.ext rfl⟩
  · intro i hi
    apply install_stack_frame
    by_contra hn
    exact hi ⟨⟨i.val, Nat.lt_of_not_ge hn⟩, Fin.ext rfl⟩

/-- The premise is the actual trace of the invoked finite program. The theorem
does not replace any run by a semantic instruction or a callback oracle. -/
theorem lowCall_eval {r s l n : ℕ} (p : Program r s l)
    (hr : r ≤ 16) (hs : s ≤ 48) (a : Data) (b : State r s)
    (ht : Trace p n ((project hr hs a).withPC (some p.entry)) (b.withPC none)) :
    Eval (lowCall p hr hs) n a (install hr hs a b) := by
  have h := eval_call_lifted p (registers hr) (stackPorts hs) a
    (registers_injective hr) (stackPorts_injective hs) ht
  rw [embed_eq_install, install_project, embed_eq_install] at h
  exact h

abbrev clear (src : Fin 48) : Cmd 16 48 :=
  .call (StackRoutines.clearProgram src 0 1)

end SubexponentialSAT.Subexp.PackingProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingVertexLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

open BitProgram StructuredCalls MatrixProgramSupport

def ports : RecordPrograms.Ports 8 15 :=
  ⟨5, 6, 7, 10, 11, by decide, by decide, by decide, by decide⟩

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 18

def clearVertex : Code := .call (StackRoutines.clearProgram 15 0 1)

def resetParser : Code := .seq (.base (.atom (.set 5 false)))
  (.seq (.base (.atom (.set 6 true))) (.base (.atom (.set 7 false))))

def callbackCost (records : Records) (v : ℕ) (s : Snapshot) : ℕ :=
  9*(SelectorProgram.rawRecords records).length+56*v+
    5*SelectorProgram.scanBudget (unary v) records+31*s.rank+15*s.address+143

def ports : RecordPrograms.Ports 8 18 :=
  ⟨5,6,7,7,8,by decide,by decide,by decide,by decide⟩

def iterationCost (records : Records) : List ℕ → Snapshot → ℕ
  | [], _ => 0
  | v::vertices, s => 6*v+callbackCost records v s+7+
      iterationCost records vertices (advance records s v)

def traceCost (records : Records) (vertices : List ℕ) (s : Snapshot) : ℕ :=
  4+iterationCost records vertices s

def leftovers (records : Records) (vertices : List ℕ) : List ℕ :=
  vertices.filter (fun v => !(covered records v))

/-- Filtering is a specification of the proved scan; the machine itself
performs the selector call for every vertex. -/
theorem fold_advance_eq (records : Records) (vertices : List ℕ) (s : Snapshot) :
    vertices.foldl (advance records) s = (leftovers records vertices).foldl appendVertex s := by
  induction vertices generalizing s with
  | nil => rfl
  | cons v vertices ih =>
      cases hc : covered records v <;>
        simp [List.foldl_cons,advance,leftovers,hc,ih]

theorem append_fold_rank (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).rank = s.rank+vertices.length := by
  induction vertices generalizing s with
  | nil => simp
  | cons v vertices ih =>
      rw [List.foldl_cons,ih]
      change s.rank+1+vertices.length = s.rank+(vertices.length+1)
      omega

theorem append_fold_address (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).address = s.address+vertices.length := by
  induction vertices generalizing s with
  | nil => simp
  | cons v vertices ih =>
      rw [List.foldl_cons,ih]
      change s.address+1+vertices.length = s.address+(vertices.length+1)
      omega

theorem final_counters (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).rank = s.rank+(leftovers records vertices).length ∧
    (vertices.foldl (advance records) s).address = s.address+(leftovers records vertices).length := by
  rw [fold_advance_eq]
  exact ⟨append_fold_rank _ _,append_fold_address _ _⟩

theorem append_fold_storage (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).storage = (storageRecords vertices).reverse ++ s.storage := by
  induction vertices generalizing s with
  | nil => simp [storageRecords]
  | cons v vertices ih =>
      simpa [storageRecords,appendVertex,PackingLeftoverEmitter.storageOutput,
        List.reverse_append,List.append_assoc] using ih (appendVertex s v)

theorem final_storage (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).storage =
      (storageRecords (leftovers records vertices)).reverse ++ s.storage := by
  rw [fold_advance_eq,append_fold_storage]

def metadataRecords : ℕ → List ℕ → Records
  | _, [] => []
  | rank, v::vertices =>
      (unary v,PackingLeftoverEmitter.metadataPayload (unary rank)) ::
        metadataRecords (rank+1) vertices

def addressRecords : ℕ → List ℕ → Records
  | _, [] => []
  | address, v::vertices => (unary v,unary address) :: addressRecords (address+1) vertices

theorem rawRecords_append (a b : Records) :
    SelectorProgram.rawRecords (a++b) =
      SelectorProgram.rawRecords a ++ SelectorProgram.rawRecords b := by
  simp [SelectorProgram.rawRecords]

@[simp] theorem rawRecords_singleton (key value : List Bool) :
    SelectorProgram.rawRecords [(key,value)] = Encoding.frame key ++ Encoding.frame value := by
  simp [SelectorProgram.rawRecords]

theorem append_fold_metadata (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).metadata =
      SelectorProgram.rawRecords (metadataRecords s.rank vertices).reverse ++ s.metadata := by
  induction vertices generalizing s with
  | nil => simp [metadataRecords,SelectorProgram.rawRecords]
  | cons v vertices ih =>
      simpa [metadataRecords,List.reverse_cons,rawRecords_append,appendVertex,
        PackingLeftoverEmitter.metadataOutput,List.append_assoc] using ih (appendVertex s v)

theorem append_fold_addresses (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl appendVertex s).addresses =
      SelectorProgram.rawRecords (addressRecords s.address vertices).reverse ++ s.addresses := by
  induction vertices generalizing s with
  | nil => simp [addressRecords,SelectorProgram.rawRecords]
  | cons v vertices ih =>
      simpa [addressRecords,List.reverse_cons,rawRecords_append,appendVertex,
        PackingLeftoverEmitter.addressOutput,List.append_assoc] using ih (appendVertex s v)

theorem final_metadata (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).metadata =
      SelectorProgram.rawRecords (metadataRecords s.rank (leftovers records vertices)).reverse ++ s.metadata := by
  rw [fold_advance_eq,append_fold_metadata]

theorem final_addresses (records : Records) (vertices : List ℕ) (s : Snapshot) :
    (vertices.foldl (advance records) s).addresses =
      SelectorProgram.rawRecords (addressRecords s.address (leftovers records vertices)).reverse ++ s.addresses := by
  rw [fold_advance_eq,append_fold_addresses]

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingOutputSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual leftover scan completes the metadata, storage order, and
address table produced by complete-block extraction. -/

namespace SubexponentialSAT.Subexp.PackingOutputSemantics

open ConstructivePacking

theorem addressRecords_eq_addressRows (vertices : List ℕ) (start : ℕ) :
    PackingLeftovers.addressRecords start vertices =
      PackingAddressSemantics.addressRows (vertices.map PackingLeftovers.unary) start := by
  induction vertices generalizing start with
  | nil => rfl
  | cons v vertices ih =>
    simp only [PackingLeftovers.addressRecords, List.map_cons,
      PackingAddressSemantics.addressRows_cons, ih]

end SubexponentialSAT.Subexp.PackingOutputSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def leftoverResult (records : PackingLeftovers.Records) (D : ℕ)
    (c : PackingExtraction.Context) : PackingLeftovers.Snapshot :=
  (List.range D).foldl (PackingLeftovers.advance records) (PackingOutputSemantics.snapshotOf c)

def leftoversBudget (records : PackingLeftovers.Records) (D : ℕ)
    (c : PackingExtraction.Context) : ℕ :=
  let result := leftoverResult records D c
  PackingLeftovers.traceCost records (List.range D) (PackingOutputSemantics.snapshotOf c) +
    6 * result.rank + 6 * result.metadata.length + 6 * result.addresses.length +
    3 * result.storage.length + 2 * (SelectorProgram.rawRecords records).length +
    2 * result.address + 32

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end


