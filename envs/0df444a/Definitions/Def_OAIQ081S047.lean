-- Prove2me | Definitions.Def_OAIQ081S047
-- name    : OAIQ081S047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:40:27.58948+00:00
-- url     : https://prove2.me/theorems/8b4083ba-d526-4f27-8b1c-609b4015aeb0
-- title:
--   Definitions bundle OAIQ081S047 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 137 declarations of OpenAI's Lean: 83 definitions, 1 inductive type or structure and 53 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer.cfg`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.clear`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.clearSource`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.clearCandidate`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram.clear`, `OAI.Algorithms.SubexponentialSAT.FrontendProgram.bodyFrame`, `OAI.Algorithms.SubexponentialSAT.FrontendProgram.cfg`, `OAI.Algorithms.SubexponentialSAT.FrontendProgram.emptyFrame`, `OAI.Algorithms.SubexponentialSAT.FrontendProgram.initializeProgram`, `OAI.Algorithms.SubexponentialSAT.ModularArithmetic.mulModRun`, `OAI.Algorithms.SubexponentialSAT.ModularPrograms.paddingLEProgram`, `OAI.Algorithms.SubexponentialSAT.ModularPrograms.subtractLEProgram`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientLift.programAt`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms.quotientInitializeProgram`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms.quotientLoopProgram`, `OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms.quotientProgram`, `OAI.Algorithms.SubexponentialSAT.ModularRingPrograms.mulModProgram`, `OAI.Algorithms.SubexponentialSAT.ModularRingPrograms.mulWideProgram`, `OAI.Algorithms.SubexponentialSAT.ModularRingPrograms.wordMulProgram`, `OAI.Algorithms.SubexponentialSAT.ParserProgram.unframeProgram`, `OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms.Contract`, `OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms.afterTag`, `OAI.Algorithms.SubexponentialSAT.RecordPrograms.CallbackContractOn`, `OAI.Algorithms.SubexponentialSAT.RecordPrograms.CallbackContractWith`, `OAI.Algorithms.SubexponentialSAT.RecordPrograms.CallbackContractWithOn`, `OAI.Algorithms.SubexponentialSAT.RecordPrograms.Visits`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.clearOutput`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.command`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.padAt`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.program`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.setBorrow`, `OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram.subtractAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.afterCleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.afterClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.afterCopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.afterReplace`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin.cleanup` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ExecCNFTupleOdometer`, `SubexponentialSAT_ExecClauseFiltersProgram`, `SubexponentialSAT_ExecClauseRelationScan`, `SubexponentialSAT_ExecClauseRelationScanPreserve`, `SubexponentialSAT_ExecClauseRelationsProgram`, `SubexponentialSAT_FrontendProgram`, `SubexponentialSAT_ListRegisterProgram`, `SubexponentialSAT_LocalExpectation`, `SubexponentialSAT_ModularArithmetic`, `SubexponentialSAT_ModularPrograms`, `SubexponentialSAT_ModularQuotientArithmetic`, `SubexponentialSAT_ModularQuotientLift`, `SubexponentialSAT_ModularQuotientPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_ParserProgram`, `SubexponentialSAT_ProgramEncoding`, `SubexponentialSAT_ProgramLinking`, `SubexponentialSAT_RecordMappedPrograms`, `SubexponentialSAT_RecordPrograms`, `SubexponentialSAT_RegisterResetProgram`, `SubexponentialSAT_SaturatingSubtractionProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_BinaryArgmin`, `SubexponentialSAT_SqrtLog_BinaryArgminBootstrap`, `SubexponentialSAT_SqrtLog_BucketProgramArithmetic`, `SubexponentialSAT_SqrtLog_BucketProgramDot`, `SubexponentialSAT_SqrtLog_BucketProgramNormalize`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep`, `SubexponentialSAT_SqrtLog_BucketProgramProducedRankJoin`, `SubexponentialSAT_SqrtLog_BucketProgramProducedRankLiteral`, `SubexponentialSAT_SqrtLog_BucketProgramRow`, `SubexponentialSAT_SqrtLog_BucketProgramSemantics`, `SubexponentialSAT_SqrtLog_BucketProgramShift`, `SubexponentialSAT_SqrtLog_LayoutProducedMatrixNatural`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_PackingWords`, `SubexponentialSAT_Subexp_MatrixProgramSupport`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingReorder`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_WorkspaceCleanupProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027` and `OAIQ081S035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S067`, `OAIQ081S068`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S074`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S035

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLinking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite program relocation and linking

Every linked block is an instruction table inside one finite program.  A block's
halt can be replaced by a jump to a caller-specified continuation.  The proofs
below transfer actual instruction traces, including that final instruction, and
preserve all ambient registers and stacks outside the block's assigned ports.

The finite sizes and maps are fixed when the linked program is constructed; they
do not inspect the unbounded input stacks.
-/

namespace SubexponentialSAT.ProgramLinking

open BitProgram

variable {r s l R S L : ℕ}

/-! ## Concrete disjoint linking -/

theorem link_complete_runsIn {m : ℕ} (p : Program r s l) (q : Program r s m)
    (input output : List Bool) {n₁ n₂ : ℕ} {b : Cfg r s l}
    (hp : RunsIn p n₁ (initial p input) b) (hb : b.pc = none)
    (hq : RunsIn q n₂ (enter q b) (terminal q output)) :
    RunsIn (link p q) (n₁ + n₂) (initial (link p q) input) (terminal (link p q) output) := by
  rw [← link_initial p q input, ← link_terminal p q output]
  exact link_runsIn p q hp hb hq

end SubexponentialSAT.ProgramLinking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleOdometer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control increment of framed binary tuples

Tuple components are little-endian Boolean words carried by
`Encoding.encodeList id`. The finite table below skips framing bits and
increments only payload bits, with carry continuing into the next component.
Neither the number of components nor their widths enters the control table.
-/

namespace SubexponentialSAT.ExecCNFTupleOdometer

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

def cfg (pc : Option (Fin 18)) (v present carry : Bool)
    (input scratch : List Bool) : Cfg 3 2 18 :=
  ⟨pc, counterRegs v present carry, counterStacks input scratch⟩

end SubexponentialSAT.ExecCNFTupleOdometer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

/-! ## In-place removal of one escape frame -/

/-- Eleven fixed labels implement one complete in-place frame removal. -/
abbrev unframeProgram : Program 2 2 11 := ProgramLinking.link frameProgram restoreProgram

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared record representation for executable programs

A scalar is stored as a Boolean payload (little-endian bits for natural
numbers; the scalar module specifies any fixed padding). A record list uses
the existing `Encoding.encodeList id`: false terminates the list; true starts
an escaped frame. Matrices and other fixed-depth schemas nest this same
representation. These are executable decoders and exact size identities,
not assertions that a machine has run them.
-/

namespace SubexponentialSAT.ProgramEncoding

theorem encodeRecords_length_le (records : Records) (width : ℕ)
    (hwidth : ∀ payload ∈ records, payload.length ≤ width) :
    (encodeRecords records).length ≤ 1 + (2 * width + 2) * records.length :=
  Encoding.length_encodeList_upper id records width hwidth

end SubexponentialSAT.ProgramEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable actual iterator over the project's framed-record representation.
The callback is a fixed structured program, whose executions are measured in the
same semantics as the parser and iterator. It is never an atomic semantic oracle.
-/

namespace SubexponentialSAT.RecordPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem state_stack_frame {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) (i : Fin s)
    (hs : i ≠ p.source) (hp : i ≠ p.payload) :
    (state p base v pr f src out).stacks i = base.stacks i := by
  simp [state, hs, hp]

/-- A callback contract that additionally records its change to auxiliary data. -/
abbrev CallbackContractWith {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧ effect bits base next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

/-- The ordered auxiliary effects of all callbacks actually visited before
the first successful match, or until the list ends. -/
inductive Visits {r s : ℕ} (test : List Bool → Bool)
    (effect : List Bool → State r s → State r s → Prop) :
    List (List Bool) → State r s → State r s → Prop
  | nil (base) : Visits test effect [] base base
  | hit {bits rest base next} : test bits = true → effect bits base next →
      Visits test effect (bits :: rest) base next
  | miss {bits rest base middle next} : test bits = false → effect bits base middle →
      Visits test effect rest middle next → Visits test effect (bits :: rest) base next

/-- Linear callbacks give a polynomial bound in the actual serialized input,
with all payload bits and record delimiters included. -/
theorem program_budget_le_input (cost : List Bool → ℕ) (records : List (List Bool))
    (a b : ℕ) (h : ∀ bits ∈ records, cost bits ≤ a * bits.length + b) :
    4 + budget cost records ≤
      (a + b + 17) * ((ProgramEncoding.encodeRecords records).length + 1) := by
  have hb := budget_le_linear cost records a b h
  rw [ProgramEncoding.encodeRecords_length]
  let k := a + b + 17
  have hs : (a + 6) * (records.map List.length).sum ≤ k * (records.map List.length).sum :=
    Nat.mul_le_mul_right _ (by dsimp [k]; omega)
  have hr : (b + 7) * records.length ≤ k * records.length :=
    Nat.mul_le_mul_right _ (by dsimp [k]; omega)
  have hfour : 4 ≤ k * 2 := by dsimp [k]; omega
  calc
    4 + budget cost records ≤ k * 2 +
        (k * (records.map List.length).sum + k * records.length) :=
      Nat.add_le_add hfour (hb.trans (Nat.add_le_add hs hr))
    _ = k * ((records.map List.length).sum + records.length + 2) := by ring
    _ ≤ k * (2 * (records.map List.length).sum + 2 * records.length + 1 + 1) :=
      Nat.mul_le_mul_left _ (by omega)

/-- When every callback continues, its auxiliary-state relation folds over
the whole input list in order. This supports exact filter/map output proofs. -/
theorem Visits.fold_of_false {r s : ℕ} {α : Type*}
    {test : List Bool → Bool} {effect : List Bool → State r s → State r s → Prop}
    {records : List (List Bool)} {base next : State r s}
    (h : Visits test effect records base next)
    (never : ∀ bits ∈ records, test bits = false)
    (measure : State r s → α) (update : α → List Bool → α)
    (stepEffect : ∀ bits a b, effect bits a b → measure b = update (measure a) bits) :
    measure next = records.foldl update (measure base) := by
  induction h with
  | nil base => rfl
  | @hit bits rest base next ht he =>
      have hf := never bits (by simp)
      simp [ht] at hf
  | @miss bits rest base middle next ht he hr ih =>
      have hrest : ∀ bits ∈ rest, test bits = false := fun item hi => never item (by simp [hi])
      rw [List.foldl_cons, ← stepEffect bits base middle he]
      exact ih hrest

/-- A typed callback only needs to execute on payloads satisfying its schema. -/
abbrev CallbackContractOn {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), validPayload bits → invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

abbrev CallbackContractWithOn {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  ∀ (bits tail : List Bool) (base : State r s), validPayload bits → invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧ invariant next ∧ effect bits base next ∧
      Eval callback n (state p base false true false tail bits.reverse)
        (state p next false true (test bits) tail [])

end SubexponentialSAT.RecordPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

abbrev clear (port : Fin 10) : Cmd 12 10 := .call (StackRoutines.clearProgram port 0 1)

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordMappedPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual record iteration over encoded logical values

The instruction sequence is `RecordPrograms.iterate`. The contract below is
required only for payloads emitted by the supplied encoder. It does not ask a
callback for correct behavior on malformed encodings, and it does not install
the encoder, test, or cost function as a machine instruction.
-/

namespace SubexponentialSAT.RecordMappedPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {α : Type*} {r s : ℕ}

abbrev Contract (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop) : Prop :=
  ∀ (a : α) (tail : List Bool) (base : State r s), invariant base →
    ∃ (n : ℕ) (next : State r s), n ≤ cost a ∧ invariant next ∧
      Eval callback n (state p base false true false tail (enc a).reverse)
        (state p next false true (test a) tail [])

def afterTag (p : Ports r s) (enc : α → List Bool) (base : State r s)
    (values : List α) (suffix : List Bool) : State r s :=
  match values with
  | [] => state p base false true false suffix []
  | a :: rest => state p base true true false
      (Encoding.frame (enc a) ++ (Encoding.encodeList enc rest ++ suffix)) []

end SubexponentialSAT.RecordMappedPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clause-relation scans over encoded formulas

All modes use a fixed finite Boolean program. An outer record iterator parses
each encoded clause, then invokes the concrete preserving clause-relation
program. The query clause is preserved for callers that subsequently emit it.
-/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

abbrev clearCandidate : Cmd 15 12 := .call (StackRoutines.clearProgram 8 0 1)

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A preserving wrapper for repeated clause-vs-formula scans. A real copy of
the full formula is scanned, and its residual copy is explicitly cleared. -/
namespace SubexponentialSAT.ExecClauseRelationScan.Preserving
open BitProgram StructuredCalls

abbrev clearSource : Cmd 15 13 := .call (StackRoutines.clearProgram 10 0 1)

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ListRegisterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unbounded Boolean-list registers implemented by finite programs

Logical words are Boolean stacks.  Three fixed scratch stacks suffice for
alias-safe word assignment, prefixing, and appending; all are restored empty.
The programs below contain only the existing finite Boolean/stack instructions.
Every stated cost is proved by an actual execution trace.
-/

namespace SubexponentialSAT.ListRegisterProgram

open BitProgram StackRoutines ProgramLinking

theorem transfer_run {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Run (transferProgram src dst value present) (3 * (stk src).length + 3)
      regs stk (readRegs regs value present none) (transferStacks src dst stk) := by
  have h := halt_after_trace _ (transferProgram_trace src dst value present hsd hvp regs stk)
    3 rfl rfl
  simpa [Run, transferProgram, transferResult, Nat.add_assoc] using h

end SubexponentialSAT.ListRegisterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

abbrev clear (port : Fin 16) : Cmd 15 16 := .call (StackRoutines.clearProgram port 0 1)

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FrontendProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual initialization of the canonical SAT input

The nineteen-label program splits the variable-count header and counts its
unary marks into a binary stack word. The untouched encoded CNF body remains
on stack 0. All growing values live on Boolean stacks, not in finite control.
-/

namespace SubexponentialSAT.FrontendProgram

open SubexponentialSAT.BitProgram

def cfg (pc : Option (Fin 19)) (b p : Bool) (body unary binary scratch : List Bool) :
    Cfg 3 4 19 := ⟨pc, CounterPrograms.counterRegs b p false, storage body unary binary scratch⟩

/-- The port maps are fixed once. Counter input/output/scratch are stacks 1/2/3. -/
abbrev initializeProgram : Program 3 4 19 :=
  ProgramLinking.linkInto ParserProgram.natProgram CounterPrograms.lengthProgram
    Fin.castSucc (Fin.castAdd 2) id Fin.succ

def emptyFrame : Cfg 3 4 19 := cfg none false false [] [] [] []
def bodyFrame (body : List Bool) : Cfg 3 4 19 := cfg none false false body [] [] []

end SubexponentialSAT.FrontendProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LocalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Conditional expectations of local objectives

A local term is evaluated only on the still-unassigned coordinates in its
support. The resulting evaluator is proved equal to exhaustive conditional
expectation. Instrumentation counts calls to local terms, separately from
arithmetic and data-structure costs.
-/

namespace SubexponentialSAT.LocalExpectation

open SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

theorem wordExpectation_dependsOn (alphabet : List W) (support : Finset I)
    (f : (I → W) → ℚ) (hf : DependsOn support f) (remaining : List I) :
    DependsOn support (wordExpectation alphabet f remaining) := by
  induction remaining with
  | nil => exact hf
  | cons i remaining ih =>
      intro ω ω' h
      simp only [wordExpectation]
      apply congrArg (mean alphabet)
      funext w
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp [Function.update_of_ne hji, h j hj]

/-- Removing unread free indices leaves the exact conditional average. -/
theorem wordExpectation_filter (alphabet : List W) (hne : alphabet ≠ [])
    (support : Finset I) (f : (I → W) → ℚ) (hf : DependsOn support f)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet f remaining ω =
      wordExpectation alphabet f (active support remaining) ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      by_cases hi : i ∈ support
      · simp only [active, List.filter_cons, hi, decide_true,
          ite_true, if_true, wordExpectation]
        apply congrArg (mean alphabet)
        funext w
        exact ih _
      · have hignore (w : W) :
            wordExpectation alphabet f remaining (Function.update ω i w) =
              wordExpectation alphabet f remaining ω := by
          apply wordExpectation_dependsOn alphabet support f hf remaining
          intro j hj
          have hji : j ≠ i := by intro h; subst j; exact hi hj
          simp [Function.update_of_ne hji]
        simp only [wordExpectation, active, List.filter_cons, hi, decide_false,
          Bool.false_eq_true, ite_false]
        simp_rw [hignore]
        rw [mean_const alphabet hne]
        exact ih ω

theorem wordExpectation_const (alphabet : List W) (hne : alphabet ≠ [])
    (r : ℚ) (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun _ => r) remaining ω = r := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      exact mean_const alphabet hne r

end SubexponentialSAT.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Binary long division with finite-bit operations

The executable functions below inspect Bool/list constructors only: they do not
call Nat division, multiplication, comparison, or subtraction on encoded values.
Natural arithmetic appears solely in specifications and event-count proofs.
The event count is not asserted to be a primitive Turing-machine runtime.
-/

namespace SubexponentialSAT.ModularArithmetic

open SubexponentialSAT.BinaryArithmetic

/-! A measured finite-control subtraction transducer. -/

/-! Instrumentation with events carrying only finitely many Boolean values.
The logs record every padding/subtraction cell and each shift/selection.
They are not a primitive-machine simulation certificate. -/

/-! Modular addition and multiplication combine the concrete binary
arithmetic runs with the concrete long-division run. -/

def mulModRun (m xs ys : List Bool) : List Bool × List ModularEvent :=
  let product := SubexponentialSAT.BinaryArithmetic.mulRun xs ys
  let reduced := reduceLogged m product.1
  (reduced.1, product.2.map Sum.inl ++ reduced.2.map Sum.inr)

/-! An explicit finite ring expression for geometric correction. Its
operation-node count is a ring-operation bound, separately from bit costs. -/

end SubexponentialSAT.ModularArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

abbrev subtractLEProgram : Program 8 3 17 :=
  SubexponentialSAT.ProgramLinking.link subtractProgram reverseOutput

abbrev paddingLEProgram : Program 8 3 9 :=
  SubexponentialSAT.ProgramLinking.link paddingProgram reverseOutput

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The quotient bits emitted by binary long division

These bit/list functions specify the output of the finite division program.
Each quotient bit is the complement of the actual subtraction borrow; neither
the recurrence nor the bit selector calls natural-number division.
-/

namespace SubexponentialSAT.ModularQuotientArithmetic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic

/-- One subtraction records exactly the multiple of the modulus removed. -/
theorem quotientBit_step (m r : List Bool) (b : Bool) (hlen : m.length ≤ r.length) :
    BinaryArithmetic.toNat (b :: r) =
      BinaryArithmetic.toNat m * bitVal (quotientBit m r b) + BinaryArithmetic.toNat (shiftReduce m r b) := by
  have hp : BinaryArithmetic.toNat (padTo (b :: r) m) = BinaryArithmetic.toNat m :=
    padTo_correct _ _ (by simp only [List.length_cons]; omega)
  have hv := subCarry_correct false (b :: r) (padTo (b :: r) m)
    (padTo_length _ _).symm
  cases hb : (subCarry false (b :: r) (padTo (b :: r) m)).2 with
  | false =>
      simpa [quotientBit, shiftReduce, hb, hp] using hv
  | true => simp [quotientBit, shiftReduce, hb]

/-- The division identity itself only requires words, including a zero modulus. -/
theorem divide_identity (m xs : List Bool) :
    BinaryArithmetic.toNat xs = BinaryArithmetic.toNat m * BinaryArithmetic.toNat (divide m xs).1 + BinaryArithmetic.toNat (divide m xs).2 := by
  induction xs with
  | nil => simp [padTo_correct m [] (Nat.zero_le _)]
  | cons b bs ih =>
      have hl : m.length ≤ (divide m bs).2.length := by
        rw [divide_remainder_length]
        omega
      have hs := quotientBit_step m (divide m bs).2 b hl
      simp only [divide_cons, toNat_cons ] at hs ⊢
      rw [ih]
      nlinarith

theorem divide_remainder_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).2 = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m := by
  rw [divide_remainder, reduce_correct m xs hm]

theorem divide_remainder_lt (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).2 < BinaryArithmetic.toNat m := by
  rw [divide_remainder_correct m xs hm]
  exact Nat.mod_lt _ hm

theorem divide_quotient_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).1 = BinaryArithmetic.toNat xs / BinaryArithmetic.toNat m := by
  have hi := divide_identity m xs
  have hr := divide_remainder_lt m xs hm
  conv_rhs => rw [hi]
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]

end SubexponentialSAT.ModularQuotientArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Binary quotient and remainder from a fixed finite Boolean-stack program. -/

namespace SubexponentialSAT.ModularQuotientPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularDivisionPrograms
open SubexponentialSAT.ModularQuotientArithmetic

theorem embed_ports {s S l L : ℕ}
    (port : Fin s → Fin S) (hinj : Function.Injective port)
    (label : Fin l → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (localStk : Fin s → List Bool) (frame target : Fin S → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port label ret (⟨none, frameRegs, frame⟩ : Cfg 8 S L)
      ⟨pc, regs, localStk⟩ = ⟨relocatePc label ret pc, regs, target⟩ := by
  apply cfg_ext
  · rfl
  · simp [embedCfg]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port label ret _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port label ret _ _ i hi).trans (hframe i hi).symm

theorem embed_conditional (pc : Option (Fin 31)) (regs frameRegs : Fin 8 → Bool)
    (candidate modulus input left right output : List Bool) :
    embedCfg id conditionalPorts id none
      (⟨none, frameRegs, resting [] modulus input⟩ : Cfg 8 7 31)
      ⟨pc, regs, wideStacks candidate left right output⟩ =
      ⟨pc, regs, seven candidate modulus input right left output []⟩ := by
  have he :
      embedCfg id conditionalPorts id none
        (⟨none, frameRegs, resting [] modulus input⟩ : Cfg 8 7 31)
        ⟨pc, regs, wideStacks candidate left right output⟩ =
        ⟨relocatePc id none pc, regs, seven candidate modulus input right left output []⟩ := by
    apply embed_ports conditionalPorts conditionalPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · exact False.elim (hi ⟨0, rfl⟩)
      · exact False.elim (hi ⟨1, rfl⟩)
      · exact False.elim (hi ⟨2, rfl⟩)
      · exact False.elim (hi ⟨3, rfl⟩)
      · exact False.elim (hi ⟨4, rfl⟩)
      · rfl
      · rfl
  cases pc <;> exact he

theorem embed_quotient {l L : ℕ} (label : Fin l → Fin L) (ret : Option (Fin L))
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (remainder modulus input quotient : List Bool) :
    embedCfg id quotientPorts label ret
      (⟨none, frameRegs, quotientStacks [] [] [] quotient⟩ : Cfg 8 8 L)
      ⟨pc, regs, resting remainder modulus input⟩ =
      ⟨relocatePc label ret pc, regs, quotientStacks remainder modulus input quotient⟩ := by
  apply embed_ports quotientPorts quotientPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

def quotientLoopProgram : Program 8 8 65 where
  inputStack := 6
  outputStack := 7
  entry := 0
  code := Fin.addCases
    (motive := fun _ : Fin (4 + (58 + 3)) => Instr 8 8 65)
    (![.pop 6 1 3 1, .branch 3 2 3, .push 0 1 4, .halt] : Fin 4 → Instr 8 8 65)
    (Fin.addCases
      (motive := fun _ : Fin (58 + 3) => Instr 8 8 65)
      (fun pc : Fin 58 =>
        relocateInstr id quotientPorts stepLabel (some 62) (reductionStepProgram.code pc))
      (![.bnot 0 0 63, .push 7 0 64, .goto 0] : Fin 3 → Instr 8 8 65))

@[simp] theorem quotientLoop_entry : quotientLoopProgram.entry = 0 := rfl

theorem quotient_step_code :
    CodeEmbedding reductionStepProgram quotientLoopProgram
      id quotientPorts stepLabel (some 62) := by
  intro pc
  simp [quotientLoopProgram, stepLabel]

@[simp] theorem quotient_code_0 : quotientLoopProgram.code 0 = .pop 6 1 3 1 := rfl
@[simp] theorem quotient_code_1 : quotientLoopProgram.code 1 = .branch 3 2 3 := rfl
@[simp] theorem quotient_code_2 : quotientLoopProgram.code 2 = .push 0 1 4 := rfl
@[simp] theorem quotient_code_3 : quotientLoopProgram.code 3 = .halt := rfl
@[simp] theorem quotient_code_62 : quotientLoopProgram.code 62 = .bnot 0 0 63 := rfl
@[simp] theorem quotient_code_63 : quotientLoopProgram.code 63 = .push 7 0 64 := rfl
@[simp] theorem quotient_code_64 : quotientLoopProgram.code 64 = .goto 0 := rfl

@[simp] theorem quotient_stack_0 (r m x q : List Bool) : quotientStacks r m x q 0 = r := rfl
@[simp] theorem quotient_stack_6 (r m x q : List Bool) : quotientStacks r m x q 6 = x := rfl
@[simp] theorem quotient_stack_7 (r m x q : List Bool) : quotientStacks r m x q 7 = q := rfl

theorem update_remainder (r m x q next : List Bool) :
    Function.update (quotientStacks r m x q) 0 next = quotientStacks next m x q := by
  funext i; fin_cases i <;> simp [quotientStacks]

theorem update_dividend (r m x q next : List Bool) :
    Function.update (quotientStacks r m x q) 6 next = quotientStacks r m next q := by
  funext i; fin_cases i <;> simp [quotientStacks]

theorem update_quotient (r m x q next : List Bool) :
    Function.update (quotientStacks r m x q) 7 next = quotientStacks r m x next := by
  funext i; fin_cases i <;> simp [quotientStacks]

theorem quotientLoop_head (regs : Fin 8 → Bool) (r m x q : List Bool) (b : Bool) :
    Trace quotientLoopProgram 3
      ⟨some 0, regs, quotientStacks r m (b :: x) q⟩
      ⟨some 4, readRegs regs 1 3 (some b), quotientStacks (b :: r) m x q⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, readRegs,
    update_remainder, update_dividend, Function.update_apply]

theorem quotientLoop_digit (regs : Fin 8 → Bool) (r m x q : List Bool) :
    Trace quotientLoopProgram 3
      ⟨some 62, regs, quotientStacks r m x q⟩
      ⟨some 0, Function.update regs 0 (!(regs 0)), quotientStacks r m x ((!(regs 0)) :: q)⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, update_quotient]

theorem quotientLoop_exit (regs : Fin 8 → Bool) (r m q : List Bool) :
    Trace quotientLoopProgram 3
      ⟨some 0, regs, quotientStacks r m [] q⟩
      ⟨none, readRegs regs 1 3 none, quotientStacks r m [] q⟩ := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, execInstr, readRegs,
    update_dividend, Function.update_apply]

theorem divideFrom_reverse (m input : List Bool) :
    divideFrom m [] (padTo m []) input.reverse = divide m input := by
  induction input with
  | nil => rfl
  | cons b bs ih =>
    simp [List.reverse_cons, divideFrom_append, divideFrom, divide, ih]

abbrev quotientInitializeProgram : Program 8 8 27 :=
  liftProgram initializeProgram id quotientPorts

abbrev quotientProgram : Program 8 8 92 := link quotientInitializeProgram quotientLoopProgram

end SubexponentialSAT.ModularQuotientPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularQuotientLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Binary quotient and remainder on caller-selected stack ports

The fixed quotient program is relocated to eight distinct caller ports.  Its
existing instruction-trace bound is retained exactly.  Endpoints are explicit
updates of the caller's own stack store, so every unassigned stack is framed.
-/

namespace SubexponentialSAT.ModularQuotientLift

open BitProgram StackRoutines StructuredCalls
open ModularQuotientPrograms ModularQuotientArithmetic

/-- Relocation changes only the fixed port names, not the instruction table size. -/
abbrev programAt {s : ℕ} (ports : Fin 8 ↪ Fin s) : Program 8 s 92 :=
  ProgramLinking.liftProgram quotientProgram id ports

@[simp] theorem programAt_entry {s : ℕ} (ports : Fin 8 ↪ Fin s) :
    (programAt ports).entry = 0 := rfl

@[simp] theorem quotientStacksAt_remainder {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 0) = remainder := by
  simp [quotientStacksAt, ports.injective.eq_iff]

@[simp] theorem quotientStacksAt_input {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 6) = [] := by
  simp [quotientStacksAt, ports.injective.eq_iff]

@[simp] theorem quotientStacksAt_quotient {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 7) = quotient := by
  simp [quotientStacksAt]

@[simp] theorem quotientStacksAt_modulus {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (remainder quotient : List Bool) (stk : Stacks (Fin s)) :
    quotientStacksAt ports remainder quotient stk (ports 5) = stk (ports 5) := by
  simp [quotientStacksAt, ports.injective.eq_iff]

theorem extend_restrict {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (stk : Stacks (Fin s)) :
    Function.extend ports (fun i => stk (ports i)) stk = stk := by
  classical
  funext j
  by_cases hj : ∃ i, ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact ports.injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hj

theorem quotientStacks_update (m x remainder quotient : List Bool) :
    Function.update (Function.update (Function.update (quotientStacks [] m x [])
      (0 : Fin 8) remainder) 6 []) 7 quotient =
      quotientStacks remainder m [] quotient := by
  funext i
  fin_cases i <;> simp [quotientStacks]

theorem extend_result {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x remainder quotient : List Bool) (stk : Stacks (Fin s))
    (hlocal : (fun i => stk (ports i)) = quotientStacks [] m x []) :
    Function.extend ports (quotientStacks remainder m [] quotient) stk =
      quotientStacksAt ports remainder quotient stk := by
  rw [← quotientStacks_update m x remainder quotient, ← hlocal]
  simp only [ProgramLinking.extend_update ports.injective, extend_restrict]
  rfl

end SubexponentialSAT.ModularQuotientLift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed Boolean-stack programs for arithmetic with a supplied binary modulus. -/

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

abbrev mulWideProgram : Program 8 7 32 :=
  liftProgram SubexponentialSAT.BinaryPrograms.Mul.program id mulPorts

abbrev mulModProgram : Program 8 7 121 := link mulWideProgram remainderProgram


end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

abbrev wordMulProgram : Program 8 8 141 := canonicalProgram mulModProgram

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RegisterResetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite register initialization. The list of ports is part of the
program, not input data; every reset is one actual Boolean-register instruction. -/

namespace SubexponentialSAT.RegisterResetProgram

open BitProgram StructuredCalls

theorem clear_eval {r s : ℕ} (ports : List (Fin r)) (a : State r s) :
    Eval (clear ports) ports.length a (cleared ports a) := by
  induction ports generalizing a with
  | nil =>
      have he : cleared [] a = a := by cases a; rfl
      rw [he]
      exact .base (.skip _)
  | cons i rest ih =>
      let b : State r s := ⟨Function.update a.regs i false, a.stacks⟩
      have hfirst : Eval (.base (.atom (.set i false))) 1 a b :=
        .base (.atom _ _)
      have hlast : cleared rest b = cleared (i :: rest) a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hj : j = i <;> by_cases hr : j ∈ rest <;>
            simp [ b, hj, hr ]
        · rfl
      have h := hfirst.seq (ih b)
      rw [hlast] at h
      simpa only [clear, List.length_cons, Nat.add_comm] using h

theorem all_eval {r s : ℕ} (a : State r s) : Eval all r a (zeroed a) := by
  have h := clear_eval (List.finRange r) a
  have he : cleared (List.finRange r) a = zeroed a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      simp [ ]
    · rfl
  simpa only [all, List.length_finRange, he] using h

end SubexponentialSAT.RegisterResetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SaturatingSubtractionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving saturating binary subtraction

Eight Boolean registers and eight stacks suffice. The two operands remain
on stacks 0 and 1; stack 2 receives their natural-number difference and
stacks 3 through 7 return empty. Copied concatenations supply a common
padding shape without computing a numeric width. The final borrow bit
controls a real clear loop. Every copy, pad, subtraction, and clear is
charged in the linear instruction bound.
-/

namespace SubexponentialSAT.SaturatingSubtractionProgram

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic

def copy (src dst : Fin 8) : Code :=
  .call (StackRoutines.copyProgram src dst 6 0 1)

def padAt (p : Fin 3 → Fin 8) : Code :=
  .call (ProgramLinking.liftProgram ModularPrograms.paddingLEProgram id p)

def subtractAt (p : Fin 3 → Fin 8) : Code :=
  .call (ProgramLinking.liftProgram ModularPrograms.subtractLEProgram id p)

local infixr:60 " ;; " => Cmd.seq

def prepare : Code := copy 1 2 ;; copy 0 2 ;; copy 1 3 ;; copy 0 3 ;; copy 0 4 ;; copy 1 5

def clearOutput : Code := .call (StackRoutines.clearProgram 2 0 1)
def finish : Code := .ite 0 clearOutput (.base .skip) ;; RegisterResetProgram.all

def setBorrow : Code := .base (.atom (.set 0 false))

def command : Code :=
  prepare ;; padAt leftPorts ;; padAt rightPorts ;; setBorrow ;; subtractAt subtractPorts ;; finish

def program := compiled command 0 2

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Filter

def formulaCode (F : Formula) : List Bool := Encoding.encodeList clauseCode F


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgmin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A binary-score minimum update implemented by finite bit programs

The score is a little-endian bit word. Comparisons inspect its numeric value,
not its length. Candidate payloads may themselves be binary indices or encoded
rows. Ports 0/1 hold the incoming payload/score, 2/3 the incumbent, 4--7 are
scratch, and 8 is an untouched caller queue. Every copy and comparison below
has a measured trace of a fixed finite instruction table.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def data (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) : Data :=
  ⟨regs, store next best queue⟩

abbrev clear (dst : Fin 9) : Cmd 8 9 := .call (clearProgram dst 1 2)

def afterClear (d : Data) (dst : Fin 9) : Data :=
  ⟨readRegs d.regs 1 2 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 9) : Data :=
  ⟨readRegs d.regs 1 2 none, copyStacks src dst d.stacks⟩
def reset (d : Data) : Data := ⟨Function.update d.regs 0 false, d.stacks⟩

abbrev comparator : Program 8 9 13 :=
  ProgramLinking.liftProgram ModularPrograms.subtractProgram id compareStacks

abbrev replace : Cmd 8 9 :=
  .seq (clear 2) (.seq (copy 0 2) (.seq (clear 3) (copy 1 3)))

def afterReplace (d : Data) : Data :=
  afterCopy (afterClear (afterCopy (afterClear d 2) 0 2) 3) 1 3

abbrev cleanup : Cmd 8 9 := .seq (clear 0) (.seq (clear 1) (clear 6))
def afterCleanup (d : Data) : Data := afterClear (afterClear (afterClear d 0) 1) 6

abbrev update : Cmd 8 9 :=
  .seq (copy 1 4) (.seq (copy 3 5) (.seq (atom (.set 0 false))
    (.seq (.call comparator) (.seq (.ite 0 replace (.base .skip)) cleanup))))

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgminBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bootstrap the binary argmin from an empty incumbent. The initial candidate
load is paid explicitly, including the empty-input case. -/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev installFirst : Cmd 8 9 := .seq replace cleanup

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary conditional-add kernel for exact offset signatures. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open scoped BigOperators

def addReady (d : AddData) : Prop :=
  d.stacks 3 = [] ∧ ∀ i, d.stacks (addWork i) = []

def addInputLength (d : AddData) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev escape {r s : ℕ} (p : RecordPrograms.Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram escapeProgram
    (RecordPrograms.registerMap p) (RecordPrograms.stackMap p))

abbrev pushConst {r s : ℕ} (dst : Fin s) (value : Fin r) (b : Bool) : Cmd r s :=
  .seq (RecordPrograms.atom (.set value b)) (RecordPrograms.atom (.push dst value))

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

end SubexponentialSAT.Subexp.TupleProgram

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

def fieldPorts (src dst : Fin s) (h : src ≠ dst) : RecordPrograms.Ports 8 s where
  tag := 0
  present := 1
  found := 2
  source := src
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := h

abbrev readFrame (src dst : Fin s) (h : src ≠ dst) : Cmd 8 s :=
  RecordPrograms.reader (fieldPorts src dst h)

abbrev readWord (src dst tmp : Fin s) (hst : src ≠ tmp) : Cmd 8 s :=
  .seq (readFrame src tmp hst) (transfer tmp dst)

abbrev emitFrame (src dst tmp : Fin s) (htd : tmp ≠ dst) : Cmd 8 s :=
  .seq (transfer src tmp)
    (.seq (TupleProgram.pushConst dst 0 false)
      (TupleProgram.escape (fieldPorts tmp dst htd)))

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_WorkspaceCleanupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

def finish {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (d : State r s) : State r s :=
  ⟨finalRegs value present ports d.regs, BankRoutines.clearBankStacks ports d.stacks⟩

def command {r s : ℕ} (value present : Fin r) : List (Fin s) → Cmd r s
  | [] => .base .skip
  | port :: rest => .seq (.call (clearProgram port value present)) (command value present rest)

@[simp] theorem finish_stack {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (d : State r s) (i : Fin s) :
    (finish value present ports d).stacks i = if i ∈ ports then [] else d.stacks i := rfl

end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row-entry parsing, assignment-bit scanning, binary addition and
workspace recycling for one exact offset-signature row. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

def choiceCall : DotCode := .call (ProgramLinking.liftProgram choiceAddProgram id choicePort)

def popAssignment : DotCode := .base (.atom (.pop 10 0 1))

def dotStep : DotCode :=
  .seq (readWord 9 1 11 (by decide))
    (.seq popAssignment
      (.seq choiceCall
        (.seq (WorkspaceCleanupProgram.command 0 1 [1, 2]) (move 3 2 11))))

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete measured coefficient scan for one integer signature row.
Runtime EOF controls the loop; no instruction count depends on row length. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

def dotBody : DotCode := .seq dotStep dotPeek
def dotLoop : DotCode := .while 1 dotBody
def rowCommand : DotCode := .seq dotPeek dotLoop

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical, positive encodings for exact integer row signatures.  The
added one is common to all assignments and makes the normalizer total on
all legitimate row results, including the empty head. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def normalizeCall : DotCode := .call
  (ProgramLinking.liftProgram SubexponentialSAT.CounterNormalizeProgram.program normalizeRegs normalizePorts)

def canonicalRowCommand : DotCode := .seq rowCommand normalizeCall
def canonicalRowProgram := compiled canonicalRowCommand 9 2

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed EOF-controlled reversal of a raw list of framed words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev PreReverseData := State 8 4

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev subtractCall : Cmd 8 10 := .call
  (ProgramLinking.liftProgram SubexponentialSAT.SaturatingSubtractionProgram.program id subtractPort)

abbrev shiftCommand : Cmd 8 10 := .seq subtractCall (addAt shiftAddPorts)
def shiftProgram := compiled shiftCommand 0 9

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def preShiftCall : PreCode := .call
  (ProgramLinking.liftProgram shiftProgram id preShiftPort)

def preStep : PreCode :=
  .seq (readWord 10 8 12 (by decide))
    (.seq (readWord 10 1 12 (by decide))
      (.seq preShiftCall (.seq (WorkspaceCleanupProgram.command 0 1 [1,2,8])
        (emitFrame 9 11 12 (by decide)))))

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def prePeek : PreCode := .base (.atom (.peek 10 0 1))
def preBody : PreCode := .seq preStep prePeek

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact integer meaning of the physical, canonical row keys. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

@[simp] theorem canonical_value (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (canonical n) = n := by
  apply SubexponentialSAT.SubexpLiftRing.toNat_fixedBits_of_lt
  simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two n

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingReorder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Represented reordering of packed coordinates

The input table contains block-major scalar records followed by the residual
coordinate records. A concrete `idxOf` plan reorders this table into the original
vertex order. The value proof connects the represented records with the actual
computable packing split; the fixed gathering program executes the read plan.
-/

namespace SubexponentialSAT.Subexp.PackingReorder

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

/-- Coordinates in the same block-major order as the copied local tables. -/
def packedVertices (P : PackingData V U) : List V :=
  (List.finRange P.blockCount).flatMap fun i => P.types.values.map (P.vertexAt i)

/-- Actual input-table coordinate order: complete blocks, then leftovers. -/
def storageVertices (P : PackingData V U) : List V :=
  packedVertices P ++ P.leftovers

/-- Explicit index plan; it is data, not part of the finite program control. -/
def readPlan (P : PackingData V U) : List ℕ :=
  P.vertices.values.map (storageVertices P).idxOf

@[simp] theorem readPlan_length (P : PackingData V U) :
    (readPlan P).length = P.vertices.values.length := by simp [readPlan]

end SubexponentialSAT.Subexp.PackingReorder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def value (P : PackingData V U) (encodeType : U → List Bool) (v : V) : Metadata :=
  match P.lookup v with
  | some z => .covered (unary z.1.val) (encodeType z.2)
  | none => .leftover (unary (P.leftovers.idxOf v))

@[simp] theorem value_at (P : PackingData V U) (encodeType : U → List Bool)
    (i : Fin P.blockCount) (u : U) :
    value P encodeType (P.vertexAt i u) = .covered (unary i.val) (encodeType u) := by
  simp [value]

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrixNatural
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Natural-address interface for the produced row-major matrix. Row indices
are incidence-plan positions; columns are the emitted original variable IDs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutExactBuckets LayoutProgram

variable {r Q D N : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}

def literalNat (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin N) (A R : ℕ) (t : Fin Q) (j v : ℕ) : ℤ :=
  if hj : j < D then if hv : v < N then
    literalMatrix P owner A R t ⟨j,hj⟩ ⟨v,hv⟩ else 0 else 0

@[simp] theorem literalNat_fin (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin N) (A R : ℕ) (t : Fin Q) (j : Fin D) (v : Fin N) :
    literalNat P owner A R t j.val v.val=literalMatrix P owner A R t j v := by
  simp [literalNat]

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native fiber relation realizes the literal owner-sum matrix. Signed
component mass bounds imply both safe shifting and a signature-height bound. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q D n : ℕ}

def entryNat (P : PackingData (Fin D) (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (j i : ℕ) : ℤ :=
  if hj : j < D then if hi : i < D then
    LayoutProgram.localEntry P A R t ⟨j,hj⟩ ⟨i,hi⟩ else 0 else 0

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

noncomputable section

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceType (ω : WordAssignment V E r Q) (i : I) : UniversalType r Q 1 :=
  ⟨ω (.inl (ivar i)), fun _ => ω (.inr (factor i))⟩

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
@[simp] theorem incidenceType_head (ω : WordAssignment V E r Q) (i : I) :
    (incidenceType ivar factor ω i).head = ω (.inl (ivar i)) := rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
@[simp] theorem incidenceType_slot (ω : WordAssignment V E r Q) (i : I) (j : Fin 1) :
    (incidenceType ivar factor ω i).slot j = ω (.inr (factor i)) := rfl

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual produced matrices, attained head tables and Cartesian inventory
share one proof-only maximum rank. Selection is in the emitted original-ID
order, and the canonical rank bound is discharged by literal pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LeafHeadSetupProgram

variable {r Q D n : ℕ}

def actualRank (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (rows : List (List Bool)) (low : List Bool)
    (t : Fin Q) (g : Fin r) : ℕ :=
  headRank (LayoutProducedMatrix.literalNat P owner A R t) D n rows low (t.val*r+g.val)

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev clear (src : Fin 56) : Cmd 8 56 := .call (clearProgram src 0 1)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end


