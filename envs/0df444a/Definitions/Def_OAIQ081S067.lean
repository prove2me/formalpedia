-- Prove2me | Definitions.Def_OAIQ081S067
-- name    : OAIQ081S067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:52:41.138028+00:00
-- url     : https://prove2.me/theorems/bd9aa505-b1be-42b1-8fc5-9623b8e13896
-- title:
--   Definitions bundle OAIQ081S067 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 145 declarations of OpenAI's Lean: 114 definitions and 31 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.Data`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.buildChild`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.callChild`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.cleanFront`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.cleanInputs`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.clearFront`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.copyInto`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.emitAfter`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.emitInto`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.emitPort`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.emittedRegs`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.emptyBank`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.frameChild`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.idle`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.load`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.loadCost`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.loaded`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.reset`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.state`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.toPayload`, `OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport.wordBank`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.pushed`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.reverseCall`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse.command`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse.program`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.emit`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.invariant`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.pushed`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.smallState`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.transferred`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.cleared`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.copied`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.invariant`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.restrict`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.clean`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.cleared`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.invariant`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.marked` and 74 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ExecBranchControllerSupport`, `SubexponentialSAT_ExecClauseCost39Lift`, `SubexponentialSAT_ExecClauseDedupProgram`, `SubexponentialSAT_ExecClauseFilterReverse`, `SubexponentialSAT_ExecClauseFiltersProgram`, `SubexponentialSAT_ExecClauseRelationScan`, `SubexponentialSAT_ExecClauseRelationScanPreserve`, `SubexponentialSAT_ExecClauseSelfFilterProgram`, `SubexponentialSAT_ExecCleanLiteralsProgram`, `SubexponentialSAT_ExecCoreChildProgram`, `SubexponentialSAT_ExecLiteralDedupProgram`, `SubexponentialSAT_ExecPetalChildProgram`, `SubexponentialSAT_ExecPetalFamilyProgram`, `SubexponentialSAT_ExecPetalProgram`, `SubexponentialSAT_ModularArithmetic`, `SubexponentialSAT_ModularQuotientLift`, `SubexponentialSAT_ModularQuotientPrograms`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ProgramStateFrames`, `SubexponentialSAT_RecordMappedPrograms`, `SubexponentialSAT_RecordPrograms`, `SubexponentialSAT_SaturatingSubtractionProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_BucketProgramDot`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep`, `SubexponentialSAT_SqrtLog_BucketProgramShift`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_HashParametersProgramFinal`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpScanPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047` and `OAIQ081S048` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S086`, `OAIQ081S087`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S094`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097`, `OAIQ081S098` and `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.familyCall_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.command_run` and `OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost39Lift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms
namespace SubexponentialSAT.ExecClauseCost
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The actual comparator call framed in the membership routine's fixed ports.
Unassigned data is preserved, and the inspected stacks retain bounded tails. -/
theorem membershipEq_eval (d : State 7 5) :
    ∃ n ≤ 9 * ((d.stacks 1).length + 1), ∃ e : State 7 5,
      Eval (.call membershipEqProgram) n d e ∧
      e.regs 4 = decide (d.stacks 1 = d.stacks 3) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 2 = d.stacks 2 ∧ e.stacks 4 = d.stacks 4 ∧
      (e.stacks 1).length ≤ (d.stacks 1).length ∧
      (e.stacks 3).length ≤ (d.stacks 3).length ∧
      e.regs 5 = d.regs 5 ∧ e.regs 6 = d.regs 6 := by
  let a : State 5 2 := ⟨d.regs ∘ membershipEqReg, d.stacks ∘ membershipEqStack⟩
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    bitEquality_runsIn_bounded (d.regs ∘ membershipEqReg) (d.stacks 1) (d.stacks 3)
  have ha : a.withPC (some bitEqualityProgram.entry) =
      bitEqualityStart (d.regs ∘ membershipEqReg) (d.stacks 1) (d.stacks 3) := by
    unfold a SubexponentialSAT.StructuredProgram.State.withPC bitEqualityStart bitEqualityProgram
    congr 1
    first | done | (funext i; fin_cases i <;> rfl)
  have hc : (SubexponentialSAT.StructuredProgram.State.ofCfg c).withPC (none : Option (Fin 10)) = c := by
    cases c
    simp_all [SubexponentialSAT.StructuredProgram.State.ofCfg, SubexponentialSAT.StructuredProgram.State.withPC]
  have htrace : Trace bitEqualityProgram n (a.withPC (some bitEqualityProgram.entry))
      ((SubexponentialSAT.StructuredProgram.State.ofCfg c).withPC none) := by
    rw [ha, hc]
    exact ht
  have heval := eval_call_lifted bitEqualityProgram membershipEqReg membershipEqStack d
    membershipEqReg_injective membershipEqStack_injective htrace
  have hstart : embedState membershipEqReg membershipEqStack d a = d :=
    embed_restricted _ _ membershipEqReg_injective membershipEqStack_injective d
  rw [hstart] at heval
  let e := embedState membershipEqReg membershipEqStack d (SubexponentialSAT.StructuredProgram.State.ofCfg c)
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change e.regs (membershipEqReg 4) = _
    rw [embedState_register _ _ _ _ membershipEqReg_injective]
    exact hout
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · change (e.stacks (membershipEqStack 0)).length ≤ _
    rw [embedState_stack _ _ _ _ membershipEqStack_injective]
    exact hleft
  · change (e.stacks (membershipEqStack 1)).length ≤ _
    rw [embedState_stack _ _ _ _ membershipEqStack_injective]
    exact hright
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

end SubexponentialSAT.ExecClauseCost

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

theorem loop_run_with {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop)
    (contract : CallbackContractWith p callback test cost invariant effect)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, Visits.nil _, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, heffect, hcallback⟩ := contract bits tail base valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle,
            Visits.hit ht heffect, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hhistory, hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext,
            Visits.miss ht heffect hhistory, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

/-- The effect-sensitive form is useful for map/filter/fold builders. -/
theorem iterate_run_with {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop)
    (contract : CallbackContractWith p callback test cost invariant effect)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hloop⟩ :=
    loop_run_with p callback test cost invariant effect contract records suffix base valid
  refine ⟨1 + (1 + n), next, by omega, hnext, hhistory, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)

theorem loop_run_with_on {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : CallbackContractWithOn p callback test cost invariant effect validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, Visits.nil _, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, heffect, hcallback⟩ :=
        contract bits tail base (validRecords bits (by simp)) valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle,
            Visits.hit ht heffect, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hhistory, hrest⟩ :=
            ih middle (fun item hi => validRecords item (by simp [hi])) hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext,
            Visits.miss ht heffect hhistory, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

theorem iterate_run_with_on {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : CallbackContractWithOn p callback test cost invariant effect validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base)
    (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Visits test effect records base next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hloop⟩ :=
    loop_run_with_on p callback test cost invariant effect validPayload contract
      records suffix base validRecords valid
  refine ⟨1 + (1 + n), next, by omega, hnext, hhistory, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)

theorem iterate_run_on {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : CallbackContractOn p callback test cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base)
    (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ invariant next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  have hc : CallbackContractWithOn p callback test cost invariant (fun _ _ _ => True) validPayload := by
    intro bits tail state hv hi
    obtain ⟨n, next, hn, hnext, hrun⟩ := contract bits tail state hv hi
    exact ⟨n, next, hn, hnext, trivial, hrun⟩
  obtain ⟨n, next, hn, hnext, _, hrun⟩ := iterate_run_with_on p callback test cost invariant
    (fun _ _ _ => True) validPayload hc records suffix base validRecords valid v pr f
  exact ⟨n, next, hn, hnext, hrun⟩

end SubexponentialSAT.RecordPrograms

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

theorem pop_list_eval (p : Ports r s) (enc : α → List Bool) (base : State r s)
    (values : List α) (suffix : List Bool) (v pr : Bool) :
    Eval (atom (.pop p.source p.tag p.present)) 1
      (state p base v pr false (Encoding.encodeList enc values ++ suffix) [])
      (afterTag p enc base values suffix) := by
  cases values with
  | nil =>
      simpa [Encoding.encodeList, afterTag] using
        RecordPrograms.pop_eval p base v pr false false suffix []
  | cons a rest =>
      simpa [Encoding.encodeList, afterTag, List.append_assoc] using
        RecordPrograms.pop_eval p base v pr false true
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

def restrict (d : Data) : State 12 10 := ⟨d.regs ∘ regPort, d.stacks ∘ stackPort⟩

def clean (d : Data) : Prop := ∀ i : Fin 8, d.stacks (Fin.castAdd 4 i) = []

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 11 8 d.stacks⟩

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 8 d.stacks⟩

def marked (mode : Mode) (d : Data) : Data :=
  ⟨Function.update d.regs 14 (d.regs (resultRegister mode)), d.stacks⟩

def invariant (Q : Clause) (d : Data) : Prop :=
  d.stacks 9 = encodeClause Q ∧ ∀ i : Fin 9, d.stacks (Fin.castAdd 3 i) = []

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

def restrict (d : Data) : State 15 12 := ⟨d.regs, d.stacks ∘ stackPort⟩

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 12 10 d.stacks⟩

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 10 d.stacks⟩

def invariant (F : Formula) (Q : Clause) (d : Data) : Prop :=
  d.stacks 12 = encodeFormula F ∧ ExecClauseRelationScan.invariant Q (restrict d) ∧
    d.stacks 10 = []

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

abbrev emitIfSelected : StructuredCalls.Cmd 3 4 :=
  .seq (.ite 2 (.call emitRecordProgram) (.call discardRecordProgram))
    (.base resetFilterFlags)

def emitIfSelectedProgram := StructuredCalls.compiled emitIfSelected 3 2

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

abbrev emitEveryRecord : StructuredCalls.Cmd 3 4 :=
  .seq (.base (.atom (.set 2 true))) emitIfSelected

abbrev reverseRecordsCmd : StructuredCalls.Cmd 3 4 :=
  RecordPrograms.iterate filterPorts emitEveryRecord

def reverseRecordsProgram := StructuredCalls.compiled reverseRecordsCmd 0 2

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFilterReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared actual record reversal for the clause-filter storage layout. -/

namespace SubexponentialSAT.ExecClauseFilterReverse

open BitProgram StructuredCalls

def program := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram regPort stackPort
abbrev command : Cmd 15 16 := .call program

end SubexponentialSAT.ExecClauseFilterReverse

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

def smallState (regs : Regs) (query answer master : List Bool) :
    StructuredProgram.State 15 13 :=
  ⟨regs, ![[], [], [], [], [], [], [], [], [], query, [], answer, master]⟩

def transferred (source target : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks source target d.stacks⟩

def cleared (port : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

abbrev emit : Cmd 15 16 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks)

def invariant (F : Formula) (d : Data) : Prop :=
  ∃ regs source output payload, d = state regs [] [] (encodeFormula F) source output payload

def pushed (stack : Fin 16) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseSelfFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Complete fixed-master clause filtering

This wrapper performs the actual initial copy, record scan, cleanup, and
record-order restoration. Its input and output are on stack 13; every other
stack is empty at both boundaries.
-/

namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)


def Ready (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks i = []

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

def emitProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack
abbrev emitCall : Cmd 10 8 := .call emitProgram

abbrev callback : Cmd 10 8 :=
  .seq copySuffix (.seq ExecCNFSubset.memberCall (.seq selectMissing
    (.seq (ExecCNFSubset.clear 3) (.seq (ExecCNFSubset.clear 4) emitCall))))

abbrev scan : Cmd 10 8 := RecordPrograms.iterate ports callback

def reverseProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitReg reverseStack
abbrev reverseCall : Cmd 10 8 := .call reverseProgram

/-- The complete routine uses its input stack again for the final ordered
output. Its reversed accumulator and every work stack finish empty. -/
abbrev dedup : Cmd 10 8 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

def dedupProgram := compiled dedup 0 0

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program for last-occurrence clause deduplication

The current clause is compared with the unread suffix using actual set
equivalence of its literal records. The suffix copy is cleared after each
query, and the final record reversal restores the prescribed clause order.
-/

namespace SubexponentialSAT.ExecClauseDedupProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram (Regs Data state reset flags)

abbrev reverseCall : Cmd 15 16 := ExecClauseFilterReverse.command

def pushed (stack : Fin 16) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCleanLiteralsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clausewise literal cleanup

Each framed clause is decoded, passed to the fixed literal-deduplication
program, and framed again. An outer record reversal restores clause order.
The finite control is independent of the input formula and its clause sizes.
-/

namespace SubexponentialSAT.ExecCleanLiteralsProgram

open BitProgram StructuredCalls

def literalProgram := ProgramLinking.liftProgram
  ExecLiteralDedupProgram.dedupProgram bankReg bankStack
abbrev literalCall : Cmd 13 11 := .call literalProgram

def emitProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack
abbrev emitCall : Cmd 13 11 := .call emitProgram

abbrev callback : Cmd 13 11 :=
  .seq (transfer 1 3) (.seq literalCall (.seq (transfer 3 1) (.seq select emitCall)))

abbrev scan : Cmd 13 11 := RecordPrograms.iterate ports callback

def reverseProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitReg reverseStack
abbrev reverseCall : Cmd 13 11 := .call reverseProgram

/-- One fixed program maps literal cleanup over every clause and restores
the original clause order. No formula-dependent control table is used. -/
abbrev clean : Cmd 13 11 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

end SubexponentialSAT.ExecCleanLiteralsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


abbrev seedCore : Cmd 15 16 :=
  .seq (transfer 9 15) (.seq (pushFalse 14)
    (.seq (.base (.atom (.set 14 true))) emit))

def InputReady (d : Data) : Prop :=
  ∀ i : Fin 16, i ≠ 9 → i ≠ 12 → i ≠ 13 → d.stacks i = []

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

@[simp] theorem projectState_embed {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    projectState register stack (embedState register stack frame d) = d := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact embedState_register register stack frame d hr i
  · funext i
    exact embedState_stack register stack frame d hs i

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecBranchControllerSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual copying, child calls, and framed output for the two-child controller.
Ports 0--6 hold pending work, leaves, both outputs, parent, core, and selection.
Ports 7--22 are a reusable 16-stack child workspace. -/

namespace SubexponentialSAT.ExecBranchControllerSupport

open BitProgram StructuredCalls


abbrev Data := State 15 23

def state (regs : Regs) (front : Front) (bank : Bank) : Data :=
  ⟨regs, Fin.addCases (m := 7) (n := 16) (motive := fun _ => List Bool) front bank⟩

@[simp] theorem state_regs (regs : Regs) (front : Front) (bank : Bank) :
    (state regs front bank).regs = regs := rfl

def emptyBank : Bank := fun _ => []
def idle (regs : Regs) (front : Front) : Data := state regs front emptyBank
def wordBank (port : Fin 16) (bits : List Bool) : Bank := Function.update emptyBank port bits

@[simp] theorem state_front (regs : Regs) (front : Front) (bank : Bank) (i : Fin 7) :
    (state regs front bank).stacks (frontPort i) = front i := by
  simp [state, frontPort]

@[simp] theorem state_bank (regs : Regs) (front : Front) (bank : Bank) (i : Fin 16) :
    (state regs front bank).stacks (bankPort i) = bank i := by
  simp [state, bankPort]

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

@[simp] theorem reset_reset (regs : Regs) : reset (reset regs) = reset regs :=
  StackRoutines.readRegs_reset _ _ _ _

abbrev copyInto (src : Fin 7) (dst tmp : Fin 16) : Cmd 15 23 :=
  .call (StackRoutines.copyProgram (frontPort src) (bankPort dst) (bankPort tmp) 0 1)

abbrev load : Cmd 15 23 :=
  .seq (copyInto 5 9 0) (.seq (copyInto 6 12 0) (copyInto 4 13 0))

def loadCost (front : Front) : ℕ :=
  7 * ((front 4).length + (front 5).length + (front 6).length) + 15

def loaded (regs : Regs) (front : Front) : State 15 16 :=
  ExecClauseFiltersProgram.state regs (front 5) [] (front 6) (front 4) [] []

abbrev callChild {l : ℕ} (p : Program 15 16 l) : Cmd 15 23 :=
  .call (ProgramLinking.liftProgram p id bankPort)

@[simp] theorem outputPort_ne_zero (i : Fin 2) : outputPort i ≠ 0 := by
  intro h
  have he := congrArg Fin.val h
  change 2 + i.val = 0 at he
  omega
@[simp] theorem outputPort_ne_one (i : Fin 2) : outputPort i ≠ 1 := by
  intro h
  have he := congrArg Fin.val h
  change 2 + i.val = 1 at he
  omega

def emitPort (i : Fin 2) : Fin 4 → Fin 23 :=
  ![frontPort 0, frontPort 1, frontPort (outputPort i), bankPort 0]

abbrev emitInto (i : Fin 2) : Cmd 15 23 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram emitReg (emitPort i))

def emittedRegs (regs : Regs) : Regs := Function.update (Function.update regs 0 true) 1 false

def emitAfter (i : Fin 2) (bits : List Bool) (d : Data) : Data :=
  ⟨emittedRegs d.regs, Function.update (Function.update d.stacks (bankPort 0) [])
    (frontPort (outputPort i)) (ExecWorklistProgram.record bits ++ d.stacks (frontPort (outputPort i)))⟩

abbrev toPayload : Cmd 15 23 :=
  .call (StackRoutines.transferProgram (bankPort 13) (bankPort 0) 0 1)

abbrev frameChild (i : Fin 2) : Cmd 15 23 := .seq toPayload (emitInto i)

abbrev buildChild {l : ℕ} (p : Program 15 16 l) (i : Fin 2) : Cmd 15 23 :=
  .seq load (.seq (callChild p) (frameChild i))

abbrev clearFront (i : Fin 7) : Cmd 15 23 :=
  .call (StackRoutines.clearProgram (frontPort i) 0 1)

abbrev cleanInputs : Cmd 15 23 := .seq (clearFront 4) (.seq (clearFront 5) (clearFront 6))
def cleanFront (front : Front) : Front :=
  Function.update (Function.update (Function.update front 4 []) 5 []) 6 []

end SubexponentialSAT.ExecBranchControllerSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual stable subtraction of a core from an encoded clause. Membership
tests, core copies, record emission, and order restoration use finite code. -/
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

abbrev probe : Cmd 10 8 :=
  .seq ExecCNFSubset.memberCall (.seq (ExecCNFSubset.clear 3) (ExecCNFSubset.clear 4))

def probeProgram := compiled probe 3 4

abbrev wideProbe : Cmd 10 9 := .call (ProgramLinking.liftProgram probeProgram id lowStack)

abbrev emit : Cmd 10 9 :=
  .call (ProgramLinking.liftProgram ExecLiteralDedupProgram.emitProgram id lowStack)

abbrev callback : Cmd 10 9 :=
  .seq copyCore (.seq wideProbe (.seq (RecordPrograms.atom (.bnot 9 4)) emit))

end SubexponentialSAT.ExecPetalProgram
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

abbrev scan : Cmd 10 9 := RecordPrograms.iterate ports callback

abbrev reverseCall : Cmd 10 9 :=
  .call (ProgramLinking.liftProgram ExecLiteralDedupProgram.reverseProgram id lowStack)

abbrev command : Cmd 10 9 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

def program := compiled command 0 0

end SubexponentialSAT.ExecPetalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalFamilyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecPetalFamilyProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)

def state (regs : Regs) (source payload output clause core : List Bool) : Data :=
  ⟨regs, ![source, payload, output, clause, [], [], [], [], [], [], [], core]⟩

abbrev petalCall : Cmd 13 12 :=
  .call (ProgramLinking.liftProgram ExecPetalProgram.program bankReg bankStack)

abbrev emit : Cmd 13 12 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack)

abbrev callback : Cmd 13 12 := .seq (transfer 1 3) (.seq petalCall
  (.seq (transfer 3 1) (.seq (RecordPrograms.atom (.set 12 true)) emit)))

def invariant (H : Clause) (d : Data) : Prop :=
  ∃ regs source output payload, d = state regs source payload output [] (encodeClause H)

def Effect (H : Clause) (bits : List Bool) (before after : Data) : Prop :=
  after.stacks 2 = true :: (Encoding.frame (mapPayload H bits) ++ before.stacks 2)

abbrev scan : Cmd 13 12 := RecordPrograms.iterate ports callback

abbrev command : Cmd 13 12 := .seq pushOutput scan
def program := compiled command 0 2

end SubexponentialSAT.ExecPetalFamilyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

def frame (regs : Regs) (working core selected parent output : List Bool) : Data :=
  ⟨regs, ![working, [], [], [], [], [], [], [], [], core, [], [], selected, parent, output, []]⟩

abbrev familyCall : Cmd 15 16 := .call
  (ProgramLinking.liftProgram ExecPetalFamilyProgram.program familyReg familyStack)

abbrev InputReady := ExecCoreChildProgram.InputReady

end SubexponentialSAT.ExecPetalChildProgram

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

theorem mulModRun_correct (m xs ys : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (mulModRun m xs ys).1 = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat m := by
  simp only [mulModRun, reduceLogged_correct _ _ hm]
  rw [(SubexponentialSAT.BinaryArithmetic.mulRun_correct_and_cost xs ys).1]

/-! An explicit finite ring expression for geometric correction. Its
operation-node count is a ring-operation bound, separately from bit costs. -/

end SubexponentialSAT.ModularArithmetic

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

theorem conditional_borrow (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (candidate modulus input padded : List Bool)
    (hlen : candidate.length = padded.length) :
    ∃ finalRegs,
      RunsIn conditionalWideProgram (24 * candidate.length + 14)
        ⟨some 0, regs, seven candidate modulus input padded [] [] []⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate padded) modulus input⟩ ∧
      finalRegs 0 = (subCarry false candidate padded).2 := by
  obtain ⟨rf, hr, hb⟩ := conditionalSubtract_correct regs hzero candidate padded hlen
  have hw := liftProgram_runsIn conditionalSubtractProgram id conditionalPorts
    (⟨none, regs, resting [] modulus input⟩ : Cfg 8 7 31)
    Function.injective_id conditionalPorts_injective hr
  rw [embed_conditional, embed_conditional] at hw
  exact ⟨rf, hw, hb⟩

theorem reductionStep_borrow (regs : Fin 8 → Bool)
    (candidate modulus input : List Bool) (hlen : modulus.length ≤ candidate.length) :
    ∃ finalRegs,
      RunsIn reductionStepProgram (38 * candidate.length + 7 * modulus.length + 32)
        ⟨some 0, regs, resting candidate modulus input⟩
        ⟨none, finalRegs,
          resting (conditionalDifference candidate (padTo candidate modulus)) modulus input⟩ ∧
      finalRegs 0 = (subCarry false candidate (padTo candidate modulus)).2 := by
  obtain ⟨r1, h1⟩ := preparePadding_correct regs candidate modulus input hlen
  have h2 := resetBorrow_correct r1
    (seven candidate modulus input (padTo candidate modulus) [] [] [])
  obtain ⟨rf, h3, hb⟩ := conditional_borrow (Function.update r1 0 false) (by simp)
    candidate modulus input (padTo candidate modulus) (padTo_length _ _).symm
  have h12 := link_trace preparePaddingProgram resetBorrowProgram h1 rfl h2
  have h123 := link_runsIn (link preparePaddingProgram resetBorrowProgram)
    conditionalWideProgram ⟨_, le_rfl, h12⟩ rfl h3
  refine ⟨rf, ?_, hb⟩
  convert h123 using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try omega
  all_goals
    apply cfg_ext
    · simp [ relocatePc
         ]
    · rfl
    · rfl

theorem quotientLoop_iteration (regs : Fin 8 → Bool)
    (r m x q : List Bool) (b : Bool) (hlen : m.length ≤ r.length) :
    ∃ finalRegs,
      RunsIn quotientLoopProgram (38 * (r.length + 1) + 7 * m.length + 38)
        ⟨some 0, regs, quotientStacks r m (b :: x) q⟩
        ⟨some 0, finalRegs,
          quotientStacks (shiftReduce m r b) m x (quotientBit m r b :: q)⟩ := by
  obtain ⟨rf, hr, hb⟩ := reductionStep_borrow (readRegs regs 1 3 (some b))
    (b :: r) m x (by simpa using hlen.trans (Nat.le_succ _))
  have hw := relocate_runsIn reductionStepProgram quotientLoopProgram
    id quotientPorts stepLabel (some 62)
    (⟨none, regs, quotientStacks [] [] [] q⟩ : Cfg 8 8 65)
    Function.injective_id quotientPorts_injective quotient_step_code hr
  rw [embed_quotient, embed_quotient] at hw
  have hw' : RunsIn quotientLoopProgram
      (38 * (r.length + 1) + 7 * m.length + 32)
      ⟨some 4, readRegs regs 1 3 (some b), quotientStacks (b :: r) m x q⟩
      ⟨some 62, rf, quotientStacks (shiftReduce m r b) m x q⟩ := by
    simpa [relocatePc, stepLabel, shiftReduce, conditionalDifference] using hw
  have hhead := quotientLoop_head regs r m x q b
  have hdigit := quotientLoop_digit rf (shiftReduce m r b) m x q
  have ht := (SubexponentialSAT.Computation.RunsIn.trans
    (⟨3, le_rfl, hhead⟩ : RunsIn quotientLoopProgram 3 _ _) hw').trans
    (⟨3, le_rfl, hdigit⟩ : RunsIn quotientLoopProgram 3 _ _)
  refine ⟨Function.update rf 0 (!(rf 0)), ?_⟩
  convert ht using 1
  · omega
  · simp [quotientBit, hb]

theorem quotientLoop_correct (regs : Fin 8 → Bool) (r m x q : List Bool)
    (hlen : m.length ≤ r.length) :
    ∃ finalRegs,
      RunsIn quotientLoopProgram
        (50 * (x.length + 1) * (r.length + m.length + x.length + 1))
        ⟨some 0, regs, quotientStacks r m x q⟩
        ⟨none, finalRegs,
          quotientStacks (divideFrom m q r x).2 m [] (divideFrom m q r x).1⟩ := by
  induction x generalizing regs r q with
  | nil =>
    refine ⟨readRegs regs 1 3 none, 3, ?_, quotientLoop_exit regs r m q⟩
    simp only [List.length_nil]
    omega
  | cons b bs ih =>
    obtain ⟨r1, h1⟩ := quotientLoop_iteration regs r m bs q b hlen
    have hlen' : m.length ≤ (shiftReduce m r b).length := by rw [shiftReduce_length]; omega
    obtain ⟨rf, h2⟩ := ih r1 (shiftReduce m r b) (quotientBit m r b :: q) hlen'
    refine ⟨rf, ?_⟩
    apply (h1.trans h2).mono
    simp only [List.length_cons, shiftReduce_length]
    nlinarith

theorem quotientInitialize_correct (regs : Fin 8 → Bool) (m x : List Bool) :
    ∃ finalRegs,
      Trace quotientInitializeProgram (14 * m.length + 9 * x.length + 18)
        ⟨some 0, regs, quotientStacks [] m x []⟩
        ⟨none, finalRegs, quotientStacks (padTo m []) m x.reverse []⟩ := by
  obtain ⟨rf, hr⟩ := initialize_correct regs m x
  have hw := liftProgram_trace initializeProgram id quotientPorts
    (⟨none, regs, quotientStacks [] [] [] []⟩ : Cfg 8 8 27)
    Function.injective_id quotientPorts_injective hr
  rw [embed_quotient, embed_quotient] at hw
  exact ⟨rf, hw⟩

theorem quotient_correct (regs : Fin 8 → Bool) (m x : List Bool) :
    ∃ finalRegs,
      RunsIn quotientProgram (100 * (m.length + x.length + 1) ^ 2)
        ⟨some 0, regs, quotientStacks [] m x []⟩
        ⟨none, finalRegs, quotientStacks (divide m x).2 m [] (divide m x).1⟩ := by
  obtain ⟨r1, h1⟩ := quotientInitialize_correct regs m x
  obtain ⟨rf, h2⟩ := quotientLoop_correct r1 (padTo m []) m x.reverse [] (by rw [padTo_length])
  have ht := link_runsIn quotientInitializeProgram quotientLoopProgram ⟨_, le_rfl, h1⟩ rfl h2
  have hbound :
      14 * m.length + 9 * x.length + 18 +
        50 * (x.reverse.length + 1) * ((padTo m []).length + m.length + x.reverse.length + 1) ≤
        100 * (m.length + x.length + 1) ^ 2 := by
    simp only [List.length_reverse, padTo_length]
    nlinarith [Nat.zero_le m.length, Nat.zero_le x.length]
  refine ⟨rf, ?_⟩
  simpa [quotientProgram, divideFrom_reverse, relabelCfg, relocatePc] using ht.mono hbound

theorem quotient_value (regs : Fin 8 → Bool) (m x : List Bool)
    (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat m) :
    ∃ finalRegs quotient remainder,
      RunsIn quotientProgram (100 * (m.length + x.length + 1) ^ 2)
        ⟨some 0, regs, quotientStacks [] m x []⟩
        ⟨none, finalRegs, quotientStacks remainder m [] quotient⟩ ∧
      quotient.length = x.length ∧ remainder.length = m.length + x.length ∧
      SubexponentialSAT.BinaryArithmetic.toNat quotient = SubexponentialSAT.BinaryArithmetic.toNat x / SubexponentialSAT.BinaryArithmetic.toNat m ∧
      SubexponentialSAT.BinaryArithmetic.toNat remainder = SubexponentialSAT.BinaryArithmetic.toNat x % SubexponentialSAT.BinaryArithmetic.toNat m := by
  obtain ⟨rf, hr⟩ := quotient_correct regs m x
  exact ⟨rf, (divide m x).1, (divide m x).2, hr,
    divide_quotient_length m x, divide_remainder_length m x,
    divide_quotient_correct m x hm, divide_remainder_correct m x hm⟩

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

/-- The actual quotient routine runs within its proved bound on arbitrary
caller storage.  Ports `1` through `4` are initially empty work stacks. -/
theorem programAt_runsIn {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (h0 : stk (ports 0) = []) (h1 : stk (ports 1) = [])
    (h2 : stk (ports 2) = []) (h3 : stk (ports 3) = [])
    (h4 : stk (ports 4) = []) (h5 : stk (ports 5) = m)
    (h6 : stk (ports 6) = x) (h7 : stk (ports 7) = []) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn (programAt ports) (100 * (m.length + x.length + 1) ^ 2)
        ⟨some (programAt ports).entry, regs, stk⟩
        ⟨none, finalRegs, quotientStacksAt ports (divide m x).2 (divide m x).1 stk⟩ := by
  have hlocal : (fun i => stk (ports i)) = quotientStacks [] m x [] := by
    funext i
    fin_cases i <;> simpa [quotientStacks] using (by assumption)
  have hin : Function.extend ports (quotientStacks [] m x []) stk = stk := by
    rw [← hlocal]
    exact extend_restrict ports stk
  have hout := extend_result ports m x (divide m x).2 (divide m x).1 stk hlocal
  obtain ⟨finalRegs, run⟩ := quotient_correct regs m x
  have lifted := ProgramLinking.liftProgram_runsIn quotientProgram id ports
    (⟨none, regs, stk⟩ : Cfg 8 s 92) Function.injective_id ports.injective run
  refine ⟨finalRegs, ?_⟩
  rw [show (programAt ports).entry = 0 by apply Fin.ext; rfl]
  simpa only [programAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    ProgramLinking.liftProgram, ProgramLinking.extend_id, id_eq, hin, hout] using lifted

/-- A direct structured-call interface, retaining the genuine trace length
rather than padding it to the upper bound. -/
theorem programAt_eval {s : ℕ} (ports : Fin 8 ↪ Fin s)
    (m x : List Bool) (regs : Fin 8 → Bool) (stk : Stacks (Fin s))
    (h0 : stk (ports 0) = []) (h1 : stk (ports 1) = [])
    (h2 : stk (ports 2) = []) (h3 : stk (ports 3) = [])
    (h4 : stk (ports 4) = []) (h5 : stk (ports 5) = m)
    (h6 : stk (ports 6) = x) (h7 : stk (ports 7) = []) :
    ∃ n ≤ 100 * (m.length + x.length + 1) ^ 2, ∃ finalRegs : Fin 8 → Bool,
      Eval (.call (programAt ports)) n ⟨regs, stk⟩
        ⟨finalRegs, quotientStacksAt ports (divide m x).2 (divide m x).1 stk⟩ := by
  obtain ⟨finalRegs, n, hn, trace⟩ :=
    programAt_runsIn ports m x regs stk h0 h1 h2 h3 h4 h5 h6 h7
  exact ⟨n, hn, finalRegs, .call _ trace⟩

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

theorem embed_mul (pc : Option (Fin 32)) (regs frameRegs : Fin 8 → Bool)
    (xs ys acc cp tmp rev modulus : List Bool) :
    embedCfg id mulPorts id none
      (⟨none, frameRegs, resting [] modulus []⟩ : Cfg 8 7 32)
      (SubexponentialSAT.BinaryPrograms.Mul.cfg pc regs xs ys acc cp tmp rev) =
      ⟨pc, regs, seven xs modulus acc ys cp tmp rev⟩ := by
  apply embed_ports mulPorts mulPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨2, rfl⟩)

theorem mulWide_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn mulWideProgram (30 * (xs.length + 1) * (ys.length + xs.length + 1))
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs,
          resting [] modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys [])⟩ := by
  obtain ⟨finalRegs, hr⟩ := SubexponentialSAT.BinaryPrograms.Mul.run regs xs ys [] ys.length le_rfl (by simp)
  have hw := liftProgram_runsIn SubexponentialSAT.BinaryPrograms.Mul.program id mulPorts
    (⟨none, regs, resting [] modulus []⟩ : Cfg 8 7 32)
    Function.injective_id mulPorts_injective hr
  change RunsIn mulWideProgram _ (embedCfg _ _ _ _ _ (SubexponentialSAT.BinaryPrograms.Mul.cfg _ _ _ _ _ _ _ _))
    _ at hw
  rw [embed_mul, embed_mul] at hw
  exact ⟨finalRegs, hw⟩

theorem mulMod_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn mulModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs,
          resting (reduce modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys [])) modulus []⟩ := by
  obtain ⟨r1, h1⟩ := mulWide_correct regs xs ys modulus
  obtain ⟨r2, h2⟩ := remainder_correct r1 modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys [])
  have ht := sequence_runs mulWideProgram remainderProgram _ _ _ _ _ _ h1 h2
  refine ⟨r2, ht.mono ?_⟩
  have hl := SubexponentialSAT.BinaryPrograms.Mul.accumulate_length xs ys []
  simp only [List.length_nil, Nat.zero_max] at hl
  have hsquare :
      (modulus.length + (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys []).length + 1) ^ 2 ≤
        (modulus.length + xs.length + ys.length + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hprod : (xs.length + 1) * (ys.length + xs.length + 1) ≤
      (modulus.length + xs.length + ys.length + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  simp only [Nat.mul_assoc]
  omega

theorem mulMod_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ finalRegs output,
      RunsIn mulModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting output modulus []⟩ ∧
      output.length ≤ modulus.length + xs.length + ys.length + 1 ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨finalRegs, hr⟩ := mulMod_correct regs xs ys modulus
  refine ⟨finalRegs, reduce modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys []), hr, ?_, ?_⟩
  · rw [reduce_length]
    have hl := SubexponentialSAT.BinaryPrograms.Mul.accumulate_length xs ys []
    simp only [List.length_nil, Nat.zero_max] at hl
    omega
  · rw [reduce_correct _ _ hm, SubexponentialSAT.BinaryPrograms.Mul.accumulate_value]
    simp


end SubexponentialSAT.ModularRingPrograms

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

abbrev Data := State 8 8

abbrev store (regs : Fin 8 → Bool) (xs ys w₂ w₃ w₄ w₅ w₆ : List Bool) : Data :=
  ⟨regs, ![xs, ys, w₂, w₃, w₄, w₅, w₆, []]⟩

abbrev state (regs : Fin 8 → Bool) (xs ys output : List Bool) : Data :=
  store regs xs ys output [] [] [] []

abbrev copied (src dst : Fin 8) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

def three (d : Data) (regs : Fin 8 → Bool) (p : Fin 3 → Fin 8)
    (a b c : List Bool) : Data :=
  ⟨regs, Function.update (Function.update (Function.update d.stacks (p 0) a) (p 1) b) (p 2) c⟩

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

abbrev Data := State 16 14


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
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

abbrev DotData := State 8 12

def dotState (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) : DotData :=
  ⟨regs, ![W, [], acc, [], [], [], [], [], [], words coeffs, bits, []]⟩

def addView (d : DotData) : AddData := projectState id choicePort d

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

abbrev preReverseStep : PreReverseCode :=
  .seq (readWord 0 1 2 (by decide)) (emitFrame 1 3 2 (by decide))

abbrev preReverseBody : PreReverseCode := .seq preReverseStep preReversePeek
abbrev preReverseLoop : PreReverseCode := .while 1 preReverseBody
abbrev preReverseCommand : PreReverseCode := .seq preReversePeek preReverseLoop
abbrev preReverseProgram := compiled preReverseCommand 0 3

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

abbrev ShiftData := State 8 10

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

abbrev PreData := State 8 14

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

def preLoop : PreCode := .while 1 preBody
abbrev preScan : PreCode := .seq prePeek preLoop

def preRepair : PreCode := .seq
  (.call (ProgramLinking.liftProgram preReverseProgram id preReversePorts))
  (move 13 11 12)

def preRowCommand : PreCode := .seq preScan preRepair
def preRowProgram := compiled preRowCommand 10 11

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev PreMatrixData := State 8 17

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev SignatureData := State 8 15

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := State 16 44

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def next (m : Model) (i : Instr) : Model :=
  ⟨Function.update m.val (output i) (value m.val i),
   Function.update m.len (output i) (lengthBound m.val m.len i)⟩

def result : List Instr → Model → Model
  | [],m => m
  | i::is,m => result is (next m i)

def budget : List Instr → Model → ℕ
  | [],_ => 0
  | i::is,m => cost m.val m.len i+budget is (next m i)

@[simp] theorem result_append (xs ys : List Instr) (m : Model) :
    result (xs++ys) m=result ys (result xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => exact ih (next m x)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

theorem counted_eval {r s : ℕ} (d : State r s) (counter src dst : Fin s) (v p : Fin r)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hsd : src ≠ dst) (hvp : v ≠ p)
    (bits rest count : List Bool) (hsrc : d.stacks src = bits ++ rest)
    (hc : d.stacks counter = count) (hlen : count.length = bits.length) :
    Eval (.call (ArrayPrograms.countedTransferProgram counter src dst v p))
      (4 * bits.length + 3) d (afterCounted d counter src dst v p bits rest) := by
  apply Eval.call
  have ht := ArrayPrograms.countedTransferProgram_trace counter src dst v p
    hcs hcd hsd hvp bits rest count d.regs d.stacks hsrc hc hlen
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  simpa [afterCounted, ArrayPrograms.countedTransferResult, StructuredProgram.State.withPC,
    ArrayPrograms.countedTransferProgram, Nat.add_assoc] using hh

theorem takeWord_eval {r s : ℕ} (d : State r s)
    (width counter tmp src dst : Fin s) (v p : Fin r)
    (distinct : Function.Injective (![width, counter, tmp, src, dst] : Fin 5 → Fin s))
    (hvp : v ≠ p) (bits rest : List Bool)
    (hsrc : d.stacks src = bits ++ rest)
    (hc : d.stacks counter = []) (ht : d.stacks tmp = [])
    (hlen : (d.stacks width).length = bits.length) :
    Eval (takeWord width counter tmp src dst v p) (14 * bits.length + 11)
      d (afterTake d src dst v p bits rest) := by
  have hwc : width ≠ counter := distinct.ne (by decide : (0 : Fin 5) ≠ 1)
  have hwt : width ≠ tmp := distinct.ne (by decide : (0 : Fin 5) ≠ 2)
  have htc : tmp ≠ counter := distinct.ne (by decide : (2 : Fin 5) ≠ 1)
  have hcs : counter ≠ src := distinct.ne (by decide : (1 : Fin 5) ≠ 3)
  have hst : src ≠ tmp := distinct.ne (by decide : (3 : Fin 5) ≠ 2)
  have htd : tmp ≠ dst := distinct.ne (by decide : (2 : Fin 5) ≠ 4)
  have hcd : counter ≠ dst := distinct.ne (by decide : (1 : Fin 5) ≠ 4)
  have hsd : src ≠ dst := distinct.ne (by decide : (3 : Fin 5) ≠ 4)
  have h₁ := copy_eval d width counter tmp v p hwc hwt htc hvp ht
  let d₁ := afterCopy d width counter v p
  have h₂ := counted_eval d₁ counter src tmp v p hcs htc.symm hst hvp bits rest
    (d.stacks width) (by simp [d₁,afterCopy,StackRoutines.copyStacks,hcs.symm,hsrc])
    (by simp [d₁,afterCopy,StackRoutines.copyStacks,hc]) hlen
  let d₂ := afterCounted d₁ counter src tmp v p bits rest
  have h₃ := transfer_eval d₂ tmp dst v p htd hvp
  have hfinal : afterTransfer d₂ tmp dst v p = afterTake d src dst v p bits rest := by
    apply state_ext
    · simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,StackRoutines.readRegs_reset]
    · funext j
      by_cases hd : j = dst
      · subst j
        simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
          StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
          StackRoutines.copyStacks,ht,htd.symm,hcd.symm,htc,hsd.symm]
      · by_cases hjt : j = tmp
        · subst j
          simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
            StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
            StackRoutines.copyStacks,hd,hst.symm,ht]
        · by_cases hjs : j = src
          · subst j
            simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
              StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
              StackRoutines.copyStacks,hd,hjt]
          · by_cases hjc : j = counter
            · subst j
              simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
                StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
                StackRoutines.copyStacks,hd,hjt,hjs,hc]
            · simp [d₂,d₁,afterTransfer,afterCounted,afterCopy,afterTake,
                StackRoutines.transferStacks,ArrayPrograms.countedTransferStacks,
                StackRoutines.copyStacks,hd,hjt,hjs,hjc]
  have hlen₂ : (d₂.stacks tmp).length = bits.length := by
    simp [d₂,d₁,afterCounted,afterCopy,ArrayPrograms.countedTransferStacks,
      StackRoutines.copyStacks,ht,htc]
  have h := Eval.seq h₁ (Eval.seq h₂ h₃)
  rw [hfinal] at h
  simpa only [hlen,hlen₂,show 7*bits.length+5+(4*bits.length+3+(3*bits.length+3))=
    14*bits.length+11 by omega,takeWord] using h

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
end


