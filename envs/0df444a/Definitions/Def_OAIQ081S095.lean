-- Prove2me | Definitions.Def_OAIQ081S095
-- name    : OAIQ081S095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:18:03.312464+00:00
-- url     : https://prove2.me/theorems/8de5eabd-6545-4dce-aea9-08c517ef4552
-- title:
--   Definitions bundle OAIQ081S095 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 36 definitions and 22 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.setDelta`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.after`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.afterCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.before`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.beforeCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Trivial.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Trivial.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.read`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.popped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.choose`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.dropTag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.increment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.lookup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.read`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.generatedIncidenceLeaves`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceCompletionLeaves`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.numberedIncidenceTest`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate.Code`, `OAI.Algorithms.SubexponentialSAT.SubexpEmptyClauseProgram.command`, `OAI.Algorithms.SubexponentialSAT.SubexpEmptyClauseProgram.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramSourceControls`, `SubexponentialSAT_SqrtLog_LeafProgramSourceStaging`, `SubexponentialSAT_SqrtLog_LeafProgramTrivial`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope`, `SubexponentialSAT_SqrtLog_NativePackingBoundsGenerated`, `SubexponentialSAT_SqrtLog_PackingCompletion`, `SubexponentialSAT_SqrtLog_PackingCompletionGenerated`, `SubexponentialSAT_SqrtLog_PackingRelations`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic`, `SubexponentialSAT_SqrtLog_RingNodeProgramPrepare`, `SubexponentialSAT_SqrtLog_RingProgramTableFinish`, `SubexponentialSAT_SubexpEmptyClauseProgram`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_PackingTupleBounds`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairScoreBounds`, `SubexponentialSAT_Subexp_SelectorMapProgram`.
--
--   **Imports.** It imports the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S076`, `OAIQ081S077` and `OAIQ081S078` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S113`, `OAIQ081S115` and `OAIQ081S129`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S077
import Definitions.Def_OAIQ081S078

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

theorem install_other_stack (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin S)
    (ht : i ≠ target p q) (hs : i ≠ p.scratch) :
    (install p q d b present flag xs ys).stacks i = d.stacks i := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact ht hj.symm
  · exact hs hj.symm

theorem install_stacks_self (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (hs : d.stacks p.scratch = []) :
    (install p q d b present flag (d.stacks (target p q)) []).stacks = d.stacks := by
  have h := congrArg State.stacks (install_self p q d)
  simpa only [install, StructuredCalls.embedState, localData, hs] using h

theorem testResult_stacks (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) : (testResult p d).stacks = d.stacks := by
  change (zeroResult p d).stacks = d.stacks
  exact install_stacks_self p false d _ _ _ hs

theorem rippleResult_other (p : Ports R S) (q c : Bool) (d : Data R S)
    (i : Fin S) (ht : i ≠ target p q) (hs : i ≠ p.scratch) :
    (rippleResult p q c d).stacks i = d.stacks i :=
  install_other_stack p q d _ _ _ _ _ i ht hs

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev before : Cmd 16 768 := .seq (copyMany 684 savePairs) (clearMany cachePorts)
def beforeCost (a : Data) : ℕ :=
  copyManyCost savePairs a + clearManyCost cachePorts (copyManyState savePairs a)

abbrev after : Cmd 16 768 := .seq (clearMany cachePorts)
  (.seq (copyMany 684 restorePairs) (.seq (clearMany backupPorts) (clearMany lowClearPorts)))
def afterCost (a : Data) : ℕ :=
  clearManyCost cachePorts a + copyManyCost restorePairs (clearManyState cachePorts a) +
  clearManyCost backupPorts (copyManyState restorePairs (clearManyState cachePorts a)) +
  clearManyCost lowClearPorts (restored a)

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev setDelta : Cmd 16 768 :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 365 0)))

abbrev prepare : Cmd 16 768 := .seq (copyMany 684 pairs) setDelta
abbrev cleanup : Cmd 16 768 := clearMany extraPorts

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEmptyClauseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

abbrev command : Cmd 10 10 :=
  .seq copyLeaf (.seq loadQuery (.seq SubexpScopeMembershipProgram.member
    (.seq (clear 0) (.seq (clear 1) (.seq (clear 2) resetWork)))))

def program := StructuredCalls.compiled command (9 : Fin 10) 9

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramTrivial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual classification of the two trivial leaf cases. The empty formula
and an empty clause are detected separately on the preserved encoded leaf. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Trivial

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev command : Cmd 10 10 :=
  .seq (.call SubexpEmptyClauseProgram.program) (.base (.atom (.peek 9 7 8)))

def program := compiled command 9 9

end SubexponentialSAT.SqrtLog.LeafProgram.Trivial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native bit lookup at a unary index. The mask source is preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 5

abbrev state (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) : Data :=
  ⟨r, ![mask,index,scan,tmp,saved]⟩

abbrev popped (r : Fin 4 → Bool) (mask index scan tmp saved : List Bool) : Data :=
  state (readRegs r 0 1 index.head?) mask index.tail scan tmp saved

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count precisely the unpinned identifiers in an explicit scope. The mask is
in original coordinate order and the framed natural identifiers are read at
runtime. No arity or other statistic is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 7 7
abbrev Code := Cmd 7 7

def state (r : Fin 7 → Bool) (mask index scan tmp acc source payload : List Bool) : Data :=
  ⟨r, ![mask,index,scan,tmp,acc,source,payload]⟩
def lookup : Code := .call (ProgramLinking.liftProgram Lookup.program lookupRegs lookupStacks)

def dropTag : Code := .base (.atom (.pop 6 0 1))
def transfer : Code := .call (StackRoutines.transferProgram 6 1 0 1)
def increment : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 4 0)))
def choose : Code := .ite 2 (.base .skip) increment
def callback : Code := .seq dropTag (.seq transfer (.seq lookup choose))

def invariant (mask : List Bool) (d : Data) : Prop :=
  ∃ r acc, d = state r mask [] [] [] acc [] []
def read (d : Data) := d.stacks 4

def program := LeafProgram.foldProgram ports callback

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 10 12

def state (r : Fin 10 → Bool) (mask current source payload : List Bool) (a q : ℕ) : Data :=
  ⟨r, ![mask,[],[],[],[],current,[],source,payload,unary a,[],unary q]⟩

def invariant (mask : List Bool) (d : Data) : Prop :=
  ∃ r a q, d = state r mask [] [] [] a q
def read (d : Data) : ℕ × ℕ := ((d.stacks 9).length,(d.stacks 11).length)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-register local operations for the actual residual statistics scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 10 21

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

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

/-- A polynomial bound in the literal serialized table and query lengths. -/
theorem budget_bound (records : List (List Bool × List Bool)) (queries : List (List Bool)) :
    budget records queries ≤
      500 * ((SelectorProgram.rawRecords records).length + 1) *
        ((ProgramEncoding.encodeRecords queries).length + 1) := by
  let L := (SelectorProgram.rawRecords records).length
  let Q := (ProgramEncoding.encodeRecords queries).length
  have hb := RecordPrograms.program_budget_le_input (callbackCost records) queries
    (220 * (L + 1)) (220 * (L + 1)) (fun query _ => by
      have h := callbackCost_bound records query
      dsimp [L]
      nlinarith)
  change 4 + RecordPrograms.budget (callbackCost records) queries ≤
    (220 * (L + 1) + 220 * (L + 1) + 17) * (Q + 1) at hb
  have hp : 1 ≤ (L + 1) * (Q + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  change 6 + RecordPrograms.budget (callbackCost records) queries ≤
    500 * (L + 1) * (Q + 1)
  nlinarith [Nat.zero_le (L * Q)]

end SubexponentialSAT.Subexp.SelectorMapProgram

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

theorem wordBytes_width {r Q : ℕ} (hr : 0 < r) (bits : List Bool)
    (hb : bits ∈ wordBytes r Q) : bits.length = Q * r := by
  obtain ⟨w, rfl⟩ := wordBytes_mem_encode hr bits hb
  exact ReadPlan.encodeWord_length w

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Closed bounds for the actual tuple generator and pair scorer

All costs below are the explicit bounds attached to proved executions of the
fixed programs.  The tuple recurrence is bounded from its actual list sizes;
no scalar-operation or callback-cost oracle is assumed.
-/

namespace SubexponentialSAT.Subexp.PairScoreBounds

open BitProgram

theorem stepCost_eq (rows alphabet : List (List Bool)) :
    TupleProgram.stepCost rows alphabet =
      17 + (24 * alphabet.length + 8) * volume rows +
        (37 * volume alphabet + 48 * alphabet.length + 25) * rows.length := by
  rw [TupleProgram.stepCost, expansionCost_eq, ProgramEncoding.encodeRecords_length]
  change 3 + (12 * alphabet.length + 8) * volume rows +
      (25 * volume alphabet + 36 * alphabet.length + 25) * rows.length +
      6 * (2 * volume (TupleProgram.cartesianOutput rows alphabet) +
        2 * (TupleProgram.cartesianOutput rows alphabet).length + 1) + 8 = _
  rw [volume_cartesian, TupleProgram.cartesianOutput_length]
  ring

/-- One actual expansion, including its loop overhead, has a uniform bound
in the number and maximum width of its input records. -/
theorem stepCost_add_two_le (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    TupleProgram.stepCost rows alphabet + 2 ≤
      200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := by
  have hv := volume_le rows L hr
  have hu := volume_le alphabet W ha
  rw [stepCost_eq]
  calc
    _ = 19 + (24 * alphabet.length + 8) * volume rows +
        (37 * volume alphabet + 48 * alphabet.length + 25) * rows.length := by ring
    _ ≤ 19 + (24 * alphabet.length + 8) * (rows.length * L) +
        (37 * (alphabet.length * W) + 48 * alphabet.length + 25) * rows.length := by
      gcongr
    _ ≤ _ + (176 * rows.length * alphabet.length * L + 163 * rows.length * alphabet.length * W +
        152 * rows.length * alphabet.length + 192 * rows.length * L + 200 * rows.length * W +
        175 * rows.length + 200 * alphabet.length * L + 200 * alphabet.length * W +
        200 * alphabet.length + 200 * L + 200 * W + 181) := Nat.le_add_right _ _
    _ = _ := by ring

/-- The actual repeated Cartesian expansion is linear in its final tuple
count, with a fixed polynomial factor in depth and physical word width. -/
theorem powerCost_le (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hA : 1 ≤ alphabet.length)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    TupleProgram.powerCost alphabet n rows ≤
      400 * (n + 1) * (rows.length + 1) * alphabet.length ^ n * (L + n * W + W + 1) := by
  induction n generalizing rows L with
  | zero =>
    simp only [TupleProgram.powerCost, Nat.zero_add, pow_zero, Nat.mul_one, Nat.zero_mul]
    nlinarith
  | succ n ih =>
    have hi := ih (TupleProgram.cartesianOutput rows alphabet) (L + W)
      (cartesian_width rows alphabet L W hr ha)
    rw [TupleProgram.cartesianOutput_length] at hi
    have hs := stepCost_add_two_le rows alphabet L W hr ha
    have hA' : alphabet.length + 1 ≤ 2 * alphabet.length := by omega
    have hs' : TupleProgram.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length * (L + W + 1) := by
      calc
        _ ≤ 200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := hs
        _ ≤ 200 * (rows.length + 1) * (2 * alphabet.length) * (L + W + 1) := by gcongr
        _ = _ := by ring
    have hpow : alphabet.length ≤ alphabet.length ^ (n + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hA (show 1 ≤ n + 1 by omega)
    have hwidth : L + W + 1 ≤ L + (n + 1) * W + W + 1 := by nlinarith
    have hstep : TupleProgram.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      exact hs'.trans (by gcongr)
    have hrA : rows.length * alphabet.length + 1 ≤ (rows.length + 1) * alphabet.length := by
      nlinarith
    have hrec : TupleProgram.powerCost alphabet n (TupleProgram.cartesianOutput rows alphabet) ≤
        400 * (n + 1) * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      calc
        _ ≤ 400 * (n + 1) * (rows.length * alphabet.length + 1) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := hi
        _ ≤ 400 * (n + 1) * ((rows.length + 1) * alphabet.length) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    rw [TupleProgram.powerCost]
    have hsum := Nat.add_le_add hstep hrec
    nlinarith

theorem generated_powerCost_le (alphabet : List (List Bool)) (n W : ℕ)
    (hA : 1 ≤ alphabet.length) (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    TupleProgram.powerCost alphabet n [[]] ≤
      800 * (n + 1) * alphabet.length ^ n * ((n + 1) * W + 1) := by
  have h := powerCost_le alphabet [[]] n 0 W hA (by simp) ha
  calc
    _ ≤ 400 * (n + 1) * ([[]] : List (List Bool)).length.succ * alphabet.length ^ n *
        (0 + n * W + W + 1) := h
    _ = _ := by simp only [List.length_cons, List.length_nil, Nat.succ_eq_add_one]; ring

end SubexponentialSAT.Subexp.PairScoreBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingTupleBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual tuple tables used by packing

These estimates use the concrete framed record encoding and the executable
Cartesian-power recurrence.  The cost bound includes an empty alphabet.
-/

namespace SubexponentialSAT.Subexp.PackingTupleBounds

theorem powerCost_nil_rows (n : ℕ) :
    TupleProgram.powerCost [] n [] = 19 * n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [TupleProgram.powerCost, PairScoreBounds.stepCost_eq,
        PairScoreBounds.volume_nil, List.length_nil, TupleProgram.cartesianOutput,
        List.flatMap_nil, List.reverse_nil, ih]
      ring

theorem powerCost_nil_singleton_succ (n : ℕ) :
    TupleProgram.powerCost [] (n + 1) [[]] = 19 * n + 46 := by
  simp only [TupleProgram.powerCost, PairScoreBounds.stepCost_eq,
    PairScoreBounds.volume_cons, PairScoreBounds.volume_nil,
    List.length_cons, List.length_nil, TupleProgram.cartesianOutput,
    List.flatMap_cons, List.flatMap_nil, List.map_nil, List.nil_append,
    List.reverse_nil, powerCost_nil_rows]
  ring

/-- The generated-table bound is valid also when no alphabet record exists.
In that case the first expansion empties the table, and subsequent iterations
have the exact linear cost shown above. -/
theorem generated_powerCost_le (alphabet : List (List Bool)) (n W : ℕ)
    (ha : ∀ x ∈ alphabet, x.length ≤ W) :
    TupleProgram.powerCost alphabet n [[]] ≤
      800 * (n + 1) * (alphabet.length ^ n + 1) * ((n + 1) * W + 1) := by
  cases alphabet with
  | nil =>
      cases n with
      | zero =>
          simp only [TupleProgram.powerCost, List.length_nil, pow_zero,
            Nat.zero_add, Nat.one_mul, Nat.mul_one]
          omega
      | succ n =>
          rw [powerCost_nil_singleton_succ]
          simp only [List.length_nil, zero_pow (Nat.succ_ne_zero n),
            Nat.zero_add, Nat.mul_one]
          calc
            19 * n + 46 ≤ 800 * (n + 1 + 1) := by omega
            _ = 800 * (n + 1 + 1) * 1 := by ring
            _ ≤ 800 * (n + 1 + 1) * ((n + 1 + 1) * W + 1) :=
              Nat.mul_le_mul_left _ (by omega)
  | cons a alphabet =>
      have h := PairScoreBounds.generated_powerCost_le (a :: alphabet) n W (by simp) ha
      exact h.trans (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))

end SubexponentialSAT.Subexp.PackingTupleBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native address-plan frontend bounds. The source size includes the actual
input plans and the number of represented types, not a scope-generated plan. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp LayoutProgram LayoutProgram.NativePacking
variable {U : Type*} [DecidableEq U]

theorem type_rows_count (s : Spec U) : s.params.typeRows.length = s.types.values.length := by
  rw [s.type_records, List.length_map]

theorem type_power_count (s : Spec U) :
    s.params.alphabet.length ^ (s.params.Δ + 1) = s.types.values.length := by
  have h := type_rows_count s
  simpa only [NativeFrontend.Params.typeRows, TupleProgram.powerRows_length,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] using h

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingRelations
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality tests for shared-head incidence words and individual head colors. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
/-- Incidence equality reads the actual shared variable and shared factor seeds. -/
theorem incidenceType_eq_iff (ω η : WordAssignment V E r Q) (i j : I) :
    incidenceType ivar factor ω i = incidenceType ivar factor η j ↔
      ω (.inl (ivar i)) = η (.inl (ivar j)) ∧
      ω (.inr (factor i)) = η (.inr (factor j)) := by
  constructor
  · intro h
    exact ⟨congrArg UniversalType.head h,
      congrArg (fun u : UniversalType r Q 1 => u.slot 0) h⟩
  · rintro ⟨hh, hs⟩
    apply UniversalType.ext
    · exact hh
    · funext a
      exact hs

/-- Two word records are sufficient even when multiple incidences share a seed. -/
def incidenceWords (ω : WordAssignment V E r Q) (i : I) : List (Word r Q) :=
  [ω (.inl (ivar i)), ω (.inr (factor i))]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem incidenceWords_eq_iff (ω η : WordAssignment V E r Q) (i j : I) :
    incidenceWords ivar factor ω i = incidenceWords ivar factor η j ↔
      incidenceType ivar factor ω i = incidenceType ivar factor η j := by
  rw [incidenceType_eq_iff]
  simp [incidenceWords]

end Incidences

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Boolean local completion trees for the two exact packing score counters. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp.PaddedCompletion SubexponentialSAT.Subexp.ReadPlan

section Completion
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

/-- A collision is equality of the two actual word records, with shared seeds read once. -/
def numberedIncidenceTest (indices : List (V ⊕ E)) :
    ScoreTerm I V Q → (ℕ → Word r Q) → Bool
  | .inl (i,j), η => decide
      (incidenceWords ivar factor (fun a => η (indexCode indices a)) i =
       incidenceWords ivar factor (fun a => η (indexCode indices a)) j)
  | .inr _, _ => false

def incidenceCompletionLeaves (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (z : ScoreTerm I V Q) (remaining : List ℕ) (η : ℕ → Word r Q) : List Bool :=
  paddedLeaves alphabet (numberedIncidenceTest ivar factor indices z)
    (active (numberedScoreSupport ivar factor indices z) remaining) 4 η

end Completion
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletionGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-generated incidence collision leaves, using actual two-word read plans. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp

section Plans
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem encode_incidenceType (ω : WordAssignment V E r Q) (i : I) :
    CollisionProgram.encodeType (incidenceType ivar factor ω i) =
      ReadPlan.encodeWord (ω (.inl (ivar i))) ++
      ReadPlan.encodeWord (ω (.inr (factor i))) := by
  rw [ReadPlan.encodeType_eq_words]
  simp [List.ofFn_succ, CollisionProgram.registerWord, incidenceType]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem gather_incidenceSelectedPlan (indices : List (V ⊕ E))
    (hi : ∀ a, a ∈ indices) (default : Word r Q) (current candidate : List (Word r Q))
    (remaining : List ℕ) (hc : indices.length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (i : I) :
    GatherProgram.gathered ((current ++ candidate).map ReadPlan.encodeWord)
      (incidenceSelectedPlan ivar factor indices current.length remaining i) =
      CollisionProgram.encodeType (incidenceType ivar factor
        (fun a => ReadPlan.completedAt default current remaining candidate (indexCode indices a)) i) := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  have hget (n : ℕ) (hn : n < current.length) :
      ((current ++ candidate).map ReadPlan.encodeWord).getD
        (ReadPlan.selectPosition current.length remaining n) [] =
        ReadPlan.encodeWord (ReadPlan.completedAt default current remaining candidate n) := by
    rw [ReadPlan.getD_map_of_lt ReadPlan.encodeWord _ default [] _
      (by simpa using ReadPlan.selected_valid current.length candidate.length remaining hr n hn),
      ReadPlan.selected_getD default current remaining candidate n hn]
  rw [encode_incidenceType]
  simp only [GatherProgram.gathered, incidenceSelectedPlan, ReadPlan.completionPlan,
    incidenceReadPlan, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [hget (indexCode indices (.inl (ivar i))) ((List.idxOf_lt_length_iff.mpr (hi _)).trans_le hc),
    hget (indexCode indices (.inr (factor i))) ((List.idxOf_lt_length_iff.mpr (hi _)).trans_le hc)]

def generatedIncidenceLeaves (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (current : List (Word r Q)) (remaining : List ℕ) (i j : I) : List Bool :=
  CollisionTupleProgram.streamed (CollisionTupleProgram.tupleBytes current)
    (ReadPlan.wordWidth r Q)
    (incidenceSelectedPlan ivar factor indices current.length remaining i)
    (incidenceSelectedPlan ivar factor indices current.length remaining j)
    (TupleProgram.powerRows (alphabet.map ReadPlan.encodeWord) 4 [[]]) []

end Plans
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 4 7

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Constant-control preparation of the padded radix and the final node stream.
The only supplied words are zero padding, binary Q, and unary d. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation BinaryArithmetic SubexpLiftRing

theorem prepareRadix_eval (r : Fin 8 → Bool) (tail rank arity out : List Bool) :
    ∃ rf, Eval prepareRadix 4 (data r (false :: false :: tail) rank arity [] [] out)
      (data rf (true :: true :: tail) rank arity [] [] out) := by
  let x0 := data r (false :: false :: tail) rank arity [] [] out
  let x1 := (StructuredProgram.Atom.pop 5 1 3).eval x0
  let x2 := (StructuredProgram.Atom.pop 5 1 3).eval x1
  let x3 := (StructuredProgram.Atom.push 5 3).eval x2
  let x4 := (StructuredProgram.Atom.push 5 3).eval x3
  have he := StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 5 1 3) x0)
    (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 5 1 3) x1)
      (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.push 5 3) x2)
        (StructuredProgram.Eval.atom (.push 5 3) x3)))
  refine ⟨x4.regs, ?_⟩
  have hx : x4 = data x4.regs (true :: true :: tail) rank arity [] [] out := by
    apply SubexpEnumerationProgram.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [x0, x1, x2, x3, x4, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, execInstr, StructuredProgram.State.ofCfg, data, tapes]
  exact hx ▸ Eval.base he

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem finishVector_eval (s : Store) (regs : Fin 8 → Bool)
    (hempty : s.vector = []) (hsource : s.source = []) :
    Eval finishVector
      (2*s.left.length + 13*s.output.length + 2*s.tail.length + 9*s.newTail.length + 25)
      (state regs s)
      (state (readRegs regs 1 3 none) {s with left := [], source := [], vector := s.output.reverse, tail := s.newTail, newTail := [], output := [], powers := s.output ++ s.powers}) := by
  let s1 := {s with left := []}
  let s2 := {s1 with vector := s.output.reverse, output := []}
  let s3 := {s2 with tail := []}
  let s4 := {s3 with tail := s.newTail}
  let s5 := {s4 with newTail := []}
  let s6 := {s5 with source := s.output.reverse}
  let s7 := {s6 with source := [], powers := s.output ++ s.powers}
  let rr := readRegs regs 1 3 none
  have h1 := clear_store_eval s s1 regs 0 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s1])
  have h2 := transfer_store_eval s1 s2 rr 20 15 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s2, s1, hempty])
  have h3 := clear_store_eval s2 s3 rr 18 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s3])
  have h4 := copy_store_eval s3 s4 rr 19 18 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s4, s3, s2, s1])
  have h5 := clear_store_eval s4 s5 rr 19 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s5])
  have h6 := copy_store_eval s5 s6 rr 15 9 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s6, s5, s4, s3, s2, s1, hsource])
  have h7 := transfer_store_eval s6 s7 rr 9 25 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s7, s6, s5, s4, s3, s2, s1])
  simp only [rr, readRegs_reset] at h2 h3 h4 h5 h6 h7
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7))))) using 1
  all_goals try with_reducible_and_instances rfl
  simp [s1, s2, s3, s4, s5, s6, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual once-per-step pair preparation
program. The common parameter bounds physical input lengths and record count. -/

namespace SubexponentialSAT.Subexp.PairPreparationBounds

open BitProgram PairPreparationProgram

theorem planBytes_eq (plan : List ℕ) :
    CollisionStreamProgram.planBytes plan =
      ProgramEncoding.encodeRecords (plan.map SelectionTableProgram.unary) := rfl

end SubexponentialSAT.Subexp.PairPreparationBounds

end OAI.Algorithms
end


