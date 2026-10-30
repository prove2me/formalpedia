-- Prove2me | Definitions.Def_OAIQ081S088
-- name    : OAIQ081S088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:09:40.704328+00:00
-- url     : https://prove2.me/theorems/10baf429-845b-4e45-89c0-5dd132a9c852
-- title:
--   Definitions bundle OAIQ081S088 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 12 definitions, 1 inductive type or structure and 38 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.candidateTest`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.convolutionLeft`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.convolutionRight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.dotAccumulator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.nonconstantInitRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.nonconstantRoundRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.prefixRoundRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.LocalData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.atom`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.Accumulator`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramNonconstant`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefixAlgebra`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_Subexp_BlockSearchProgram`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071` and `OAIQ081S073` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S105`, `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S109`, `OAIQ081S111`, `OAIQ081S113` and `OAIQ081S115`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073

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

namespace Selector

def atom (op : StructuredProgram.Atom 24 24) : Code := .base (.atom op)

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
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

theorem escape_eval_state {r s : ℕ} (p : RecordPrograms.Ports r s) (a : State r s) :
    Eval (escape p) (5 * (a.stacks p.source).length + 3) a (escapedState p a) := by
  have h := escape_eval p a (a.stacks p.source) (a.stacks p.payload)
    (a.regs p.tag) (a.regs p.present) (a.regs p.found)
  rw [RecordPrograms.state_eq_self p a _ _ _ _ _ rfl rfl rfl rfl rfl] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases ht : i = p.tag <;> by_cases hp : i = p.present <;>
      by_cases hf : i = p.found <;> subst_vars <;>
      simp_all [ readRegs, RecordPrograms.state,
        p.found_ne_tag, p.found_ne_present, p.tag_ne_present,
        Ne.symm p.found_ne_tag, Ne.symm p.found_ne_present]
  · rfl

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem wordCallback_contract (alphabet tuple tail depth : List Bool) (guard : Bool) :
    RecordPrograms.CallbackContractWith innerPorts wordCallback (fun _ => false)
      (fun word => 5 * word.length + 12 * tuple.length + 15)
      (innerInvariant alphabet tuple tail depth guard)
      (fun word a b => b.stacks 5 = prependRecord (tuple ++ word) (a.stacks 5)) := by
  intro word rest base hb
  let a := RecordPrograms.state innerPorts base false true false rest word.reverse
  let b := pushedState 5 6 false a
  let c := escapedState wordPorts b
  let d : State 10 9 :=
    ⟨readRegs c.regs 6 7 none, StackRoutines.copyStacks 2 6 c.stacks⟩
  let e := escapedState tuplePorts d
  let f := pushedState 5 6 true e
  have hcopy : c.stacks 7 = [] := by
    simpa [c, b, a, escapedState, pushedState, wordPorts, RecordPrograms.state,
      innerPorts] using hb.2.2.2.2.1
  have h1 := pushConst_eval 5 6 false a
  have h2 := escape_eval_state wordPorts b
  have h3 := copy_eval 2 6 7 6 7 (by decide) (by decide) (by decide) (by decide) c hcopy
  have h4 := escape_eval_state tuplePorts d
  have h5 := pushConst_eval 5 6 true e
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have hf : RecordPrograms.state innerPorts f false true false rest [] = f := by
    apply RecordPrograms.state_eq_self <;>
      simp [f, e, d, c, b, a, wordPorts, tuplePorts,
        RecordPrograms.state, innerPorts, readRegs, StackRoutines.copyStacks]
  refine ⟨5 * word.length + 12 * tuple.length + 15, f, le_rfl, ?_, ?_, ?_⟩
  · rcases hb with ⟨ha, ht, hs, h6, h7, h8, h0, h1, h2, h9⟩
    simp_all [innerInvariant, f, e, d, c, b, a, pushedState, escapedState,
      wordPorts, tuplePorts, RecordPrograms.state, innerPorts, readRegs,
      StackRoutines.copyStacks]
  · rcases hb with ⟨ha, ht, hs, h6, h7, h8, h0, h1, h2, h9⟩
    simp [f, e, d, c, b, a, wordPorts, tuplePorts,
      RecordPrograms.state, innerPorts, StackRoutines.copyStacks,
      ht, h6, prependRecord, frame_eq_escaped, List.append_assoc]
  · rw [hf]
    convert hrun using 1 ;
      simp [ a, b, c, d, wordPorts,
        tuplePorts, RecordPrograms.state, innerPorts, StackRoutines.copyStacks,
        hb.2.1, hb.2.2.2.1] ; omega

theorem tupleCallback_contract (alphabet : Records) (depth : List Bool) (guard : Bool) :
    RecordPrograms.CallbackContractWith outerPorts tupleCallback (fun _ => false)
      (tupleCost alphabet) (outerInvariant alphabet depth guard)
      (fun tuple a b => b.stacks 5 = extendOutput alphabet tuple (a.stacks 5)) := by
  intro tuple rest base hb
  rcases hb with ⟨ha, h3, h4, h6, h7, h8, h9⟩
  let a := RecordPrograms.state outerPorts base false true false rest tuple.reverse
  let b : State 10 9 :=
    ⟨readRegs a.regs 6 7 none, StackRoutines.copyStacks 1 3 a.stacks⟩
  have hcopy := copy_eval 1 3 7 6 7 (by decide) (by decide) (by decide) (by decide) a
    (by simpa [a, RecordPrograms.state, outerPorts] using h7)
  have hb : innerInvariant (ProgramEncoding.encodeRecords alphabet) tuple rest depth guard b := by
    simp [innerInvariant, b, a, StackRoutines.copyStacks, RecordPrograms.state,
      outerPorts, readRegs, ha, h6, h7, h8, h9]
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with innerPorts wordCallback (fun _ => false)
      (fun word => 5 * word.length + 12 * tuple.length + 15)
      (innerInvariant (ProgramEncoding.encodeRecords alphabet) tuple rest depth guard)
      (fun word a b => b.stacks 5 = prependRecord (tuple ++ word) (a.stacks 5))
      (wordCallback_contract _ tuple rest depth guard) alphabet [] b hb
      (b.regs 3) (b.regs 4) (b.regs 5)
  let c := RecordPrograms.state innerPorts next false true false [] []
  have hin : RecordPrograms.state innerPorts b (b.regs 3) (b.regs 4) (b.regs 5)
      (Encoding.encodeList id alphabet ++ []) [] = b := by
    apply RecordPrograms.state_eq_self <;>
      simp [b, a, StackRoutines.copyStacks, RecordPrograms.state, outerPorts,
        innerPorts, ha, h3, h4, ProgramEncoding.encodeRecords]
  have hiter' : Eval (RecordPrograms.iterate innerPorts wordCallback) n b c := by
    have hany : alphabet.any (fun _ => false) = false := by
      induction alphabet <;> simp_all
    simpa only [hin, hany, unread_false] using hiter
  let d : State 10 9 :=
    ⟨readRegs c.regs 6 7 none, StackRoutines.clearStacks 2 c.stacks⟩
  have hclear := clear_eval 2 6 7 c
  have hout := history.fold_of_false (by simp) (fun s => s.stacks 5)
    (fun out word => prependRecord (tuple ++ word) out) (fun _ _ _ h => h)
  have hd : RecordPrograms.state outerPorts d false true false rest [] = d := by
    rcases hnext with ⟨_, _, ht, _, _, _, hr0, hr1, hr2, _⟩
    apply RecordPrograms.state_eq_self <;>
      simp [d, c, RecordPrograms.state, innerPorts, outerPorts, readRegs,
        StackRoutines.clearStacks, ht, hr0, hr1, hr2]
  refine ⟨(7 * (a.stacks 1).length + 5) + (n + (2 * (c.stacks 2).length + 3)),
    d, ?_, ?_, ?_, ?_⟩
  · have hlen : c.stacks 2 = tuple.reverse := by
      simpa [c, RecordPrograms.state, innerPorts] using hnext.2.1
    simp only [hlen, List.length_reverse]
    have ha' : a.stacks 1 = ProgramEncoding.encodeRecords alphabet := by
      simpa [a, RecordPrograms.state, outerPorts] using ha
    rw [ha']
    dsimp [tupleCost]
    omega
  · rcases hnext with ⟨ha', _, _, h6', h7', h8', _, _, _, h9'⟩
    simp [outerInvariant, d, c, RecordPrograms.state, innerPorts,
      StackRoutines.clearStacks, readRegs, ha', h6', h7', h8', h9']
  · simpa [extendOutput, d, c, b, a, StackRoutines.clearStacks,
      StackRoutines.copyStacks, RecordPrograms.state, innerPorts, outerPorts] using hout
  · rw [hd]
    exact hcopy.seq (hiter'.seq hclear)

theorem cartesian_eval (tuples alphabet accum : Records) (depth : List Bool) (guard : Bool)
    (base : State 10 9) (hb : outerInvariant alphabet depth guard base)
    (hrows : base.stacks 0 = ProgramEncoding.encodeRecords tuples)
    (hpayload : base.stacks 2 = [])
    (hout : base.stacks 5 = ProgramEncoding.encodeRecords accum) :
    ∃ n next, n ≤ expansionCost tuples alphabet ∧ outerInvariant alphabet depth guard next ∧
      next.stacks 0 = [] ∧ next.stacks 2 = [] ∧
      next.stacks 5 = ProgramEncoding.encodeRecords (cartesianOutput tuples alphabet ++ accum) ∧
      Eval cartesianCmd n base next := by
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with outerPorts tupleCallback (fun _ => false)
      (tupleCost alphabet) (outerInvariant alphabet depth guard)
      (fun tuple a b => b.stacks 5 = extendOutput alphabet tuple (a.stacks 5))
      (tupleCallback_contract alphabet depth guard) tuples [] base hb
      (base.regs 0) (base.regs 1) (base.regs 2)
  let final := RecordPrograms.state outerPorts next false true false [] []
  have hstart : RecordPrograms.state outerPorts base (base.regs 0) (base.regs 1)
      (base.regs 2) (Encoding.encodeList id tuples ++ []) [] = base := by
    apply RecordPrograms.state_eq_self <;>
      simp_all [outerPorts, ProgramEncoding.encodeRecords]
  have hfold := history.fold_of_false (by simp) (fun s => s.stacks 5)
    (fun out tuple => extendOutput alphabet tuple out) (fun _ _ _ h => h)
  rw [fold_extendOutput, hout, appendEncoded_encodeRecords] at hfold
  refine ⟨n, final, hn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [final, outerInvariant, RecordPrograms.state, outerPorts] using hnext
  · simp [final, RecordPrograms.state, outerPorts]
  · simp [final, RecordPrograms.state, outerPorts]
  · simpa [final, RecordPrograms.state, outerPorts] using hfold
  · have hany : tuples.any (fun _ => false) = false := by
      induction tuples <;> simp_all
    simpa only [cartesianCmd, final, hstart, hany, unread_false] using hiter

theorem initCmd_eval (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : outerInvariant alphabet depth guard a)
    (h0 : a.stacks 0 = []) (h2 : a.stacks 2 = []) (h5 : a.stacks 5 = []) :
    ∃ b, Ready alphabet [[]] depth guard b ∧ Eval initCmd 8 a b := by
  let b := pushedState 0 6 false a
  let c := pushedState 0 6 false b
  let d := pushedState 0 6 true c
  let e := pushedState 5 6 false d
  refine ⟨e, ?_, ?_⟩
  · rcases ha with ⟨ha,h3,h4,h6,h7,h8,h9⟩
    simp [Ready, outerInvariant, e, d, c, b, ha,h0,h2,h3,h4,h5,h6,h7,h8,h9,
      ProgramEncoding.encodeRecords, Encoding.encodeList, Encoding.frame]
  · exact (pushConst_eval 0 6 false a).seq ((pushConst_eval 0 6 false b).seq
      ((pushConst_eval 0 6 true c).seq (pushConst_eval 5 6 false d)))

end SubexponentialSAT.Subexp.TupleProgram

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

/-- An actual measured branch: the kept record is encoded, and an omitted
record is consumed. Both paths leave the callback ready for the next record. -/
theorem emitIfSelected_eval (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    StructuredCalls.Eval emitIfSelected (emitIfSelectedSteps selected bits)
      (filterState v p selected source work output bits.reverse)
      (filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []) := by
  cases selected with
  | false =>
      have hc := StructuredCalls.Eval.call discardRecordProgram
        (discardRecord_trace bits source work output v p false)
      have hi := StructuredCalls.Eval.ite_false (yes := .call emitRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval false false false source work output []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs
  | true =>
      have hc := StructuredCalls.Eval.call emitRecordProgram
        (emitRecord_trace bits source work output v p true)
      have hi := StructuredCalls.Eval.ite_true (no := .call discardRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval true false true source work
          (true :: (Encoding.frame bits ++ output)) []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

theorem emitEveryRecord_eval (bits source work output : List Bool) (v p f : Bool) :
    StructuredCalls.Eval emitEveryRecord (5 * bits.length + 12)
      (filterState v p f source work output bits.reverse)
      (filterState false true false source work
        (true :: (Encoding.frame bits ++ output)) []) := by
  have hset : StructuredProgram.Eval (.atom (.set 2 true)) 1
      (filterState v p f source work output bits.reverse)
      (filterState v p true source work output bits.reverse) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 2 true)
        (filterState v p f source work output bits.reverse)
  have h := (StructuredCalls.Eval.base hset).seq
    (emitIfSelected_eval true bits source work output v p)
  have ht : 1 + emitIfSelectedSteps true bits = 5 * bits.length + 12 := by
    simp only [emitIfSelectedSteps, ite_true, if_true]
    omega
  simpa only [ht, emitEveryRecord, Bool.true_eq, ite_true, if_true] using h

theorem emitEveryRecord_contract :
    RecordPrograms.CallbackContractWith filterPorts emitEveryRecord
      (fun _ => false) (fun bits => 5 * bits.length + 12) (fun _ => True) PrependEffect := by
  intro bits tail base _
  let next : StructuredProgram.State 3 4 :=
    { base with «stacks» :=
        Function.update base.stacks 2 (true :: (Encoding.frame bits ++ base.stacks 2)) }
  refine ⟨5 * bits.length + 12, next, le_rfl, trivial, ?_, ?_⟩
  · simp [PrependEffect, next]
  · rw [recordState_eq, recordState_eq]
    simpa [next] using
      emitEveryRecord_eval bits tail (base.stacks 1) (base.stacks 2) false true false

theorem reverseRecords_eval (records acc : List (List Bool))
    (suffix work : List Bool) (v p f : Bool) :
    ∃ n, n ≤ 3 + RecordPrograms.budget (fun bits => 5 * bits.length + 12) records ∧
      StructuredCalls.Eval reverseRecordsCmd n
        (filterState v p f (Encoding.encodeList id records ++ suffix) work
          (Encoding.encodeList id acc) [])
        (filterState false true false suffix work
          (Encoding.encodeList id (records.reverse ++ acc)) []) := by
  let base := filterState false true false [] work (Encoding.encodeList id acc) []
  obtain ⟨n, next, hn, _, hhistory, hrun⟩ :=
    RecordPrograms.iterate_run_with filterPorts emitEveryRecord
      (fun _ => false) (fun bits => 5 * bits.length + 12) (fun _ => True) PrependEffect
      emitEveryRecord_contract records suffix base trivial v p f
  obtain ⟨hout, hwork⟩ := prependVisits_result hhistory acc rfl
  rw [recordState_eq, recordState_eq, hout, hwork] at hrun
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  refine ⟨n, hn, ?_⟩
  simpa [reverseRecordsCmd, base, filterState, hany] using hrun

/-- The entire record reversal pass takes linearly many actual instructions.
It preserves a trailing input suffix and the separate work stack. -/
theorem reverseRecords_runsIn (records acc : List (List Bool))
    (suffix work : List Bool) (v p f : Bool) :
    RunsIn reverseRecordsProgram (10 * (Encoding.encodeList id records).length)
      ((filterState v p f (Encoding.encodeList id records ++ suffix) work
        (Encoding.encodeList id acc) []).withPC (some reverseRecordsProgram.entry))
      ((filterState false true false suffix work
        (Encoding.encodeList id (records.reverse ++ acc)) []).withPC none) := by
  obtain ⟨n, hn, hrun⟩ := reverseRecords_eval records acc suffix work v p f
  refine ⟨n + 1, ?_, StructuredCalls.compiled_halt_trace hrun 0 2⟩
  rw [reverseRecords_budget] at hn
  have hlength := ProgramEncoding.encodeRecords_length records
  change (Encoding.encodeList id records).length = _ at hlength
  omega

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed word loading and framed stack routines for the search bootstrap. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls

theorem clearCmd_eval (src : Fin 28) (a : Data) :
    Eval (clearCmd src) (2 * (a.stacks src).length + 3) a
      ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩ := by
  exact Subexp.TupleProgram.clear_eval src 0 1 a

theorem pushWord_eval (dst : Fin 28) (bits : List Bool) (a : Data) :
    ∃ rf, Eval (pushWord dst bits) (2 * bits.length) a
      ⟨rf, Function.update a.stacks dst (bits ++ a.stacks dst)⟩ := by
  induction bits generalizing a with
  | nil =>
      refine ⟨a.regs, ?_⟩
      have hs := Function.update_eq_self dst a.stacks
      simpa [pushWord, hs] using Eval.base (StructuredProgram.Eval.skip a)
  | cons b bs ih =>
      obtain ⟨rf, h⟩ := ih a
      have hp := Subexp.TupleProgram.pushConst_eval dst (0 : Fin 22) b
        (⟨rf, Function.update a.stacks dst (bs ++ a.stacks dst)⟩ : Data)
      refine ⟨Function.update rf 0 b, ?_⟩
      simpa [pushWord, Subexp.TupleProgram.pushedState, Nat.mul_add,
        Nat.add_assoc] using h.seq hp

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed control for the universal-block finite search

The commands in this file scan runtime framed lists. Their finite control
depends on the supplied finite predicate program and fixed ports, never on
the block dimension, field size, or list lengths. Predicate specifications
are measured `StructuredCalls.Eval` contracts for actual finite code.
-/

namespace SubexponentialSAT.Subexp.BlockSearchProgram

open BitProgram StructuredCalls

/-- A real short-circuiting universal quantifier over encoded records. -/
theorem allCommand_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn p predicate test cost invariant valid)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (v pr result : Bool) :
    ∃ n next, n ≤ 5 + RecordPrograms.budget (fun bits => cost bits + 2) records ∧
      invariant next ∧ Eval (allCommand p predicate) n
        (RecordPrograms.state p base v pr result (ProgramEncoding.encodeRecords records ++ suffix) [])
        (RecordPrograms.state p next false true (records.all test)
          (RecordPrograms.unread (fun bits => !(test bits)) records suffix) []) := by
  obtain ⟨n, next, hn, hnext, run⟩ := RecordPrograms.iterate_run_on p
    (.seq predicate (negateResult p)) (fun bits => !(test bits)) (fun bits => cost bits + 2)
    invariant valid (negated_contract p predicate test cost invariant valid contract)
    records suffix base hrecords hbase v pr result
  refine ⟨n + 2, next, by omega, hnext, ?_⟩
  have hrun := run.seq
    (negateResult_eval p next false true (records.any (fun bits => !(test bits)))
      (RecordPrograms.unread (fun bits => !(test bits)) records suffix) [])
  rw [not_any_not records test] at hrun
  exact hrun

theorem clear_source_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (base : State r s) (bits : List Bool) (v pr found : Bool) :
    Eval (.call (StackRoutines.clearProgram p.source p.tag p.present)) (2 * bits.length + 3)
      (RecordPrograms.state p base v pr found bits [])
      (RecordPrograms.state p base false false found [] []) := by
  have h := TupleProgram.clear_eval p.source p.tag p.present
    (RecordPrograms.state p base v pr found bits [])
  have he : (⟨readRegs (RecordPrograms.state p base v pr found bits []).regs p.tag p.present none,
      StackRoutines.clearStacks p.source (RecordPrograms.state p base v pr found bits []).stacks⟩ :
        State r s) = RecordPrograms.state p base false false found [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hv : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [readRegs, RecordPrograms.state, Function.update_apply,
          p.tag_ne_present, p.found_ne_tag, p.found_ne_present]
    · funext i
      by_cases hi : i = p.source <;> by_cases hp : i = p.payload <;>
        simp_all [StackRoutines.clearStacks, RecordPrograms.state, Function.update_apply,
          p.source_ne_payload]
  rw [he] at h
  simpa using h

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators
open SubexponentialSAT.QuarticSearch

end SubexponentialSAT.Subexp.BlockSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program for the dynamically long F₃ dot product. Every
coefficient is physically read and every multiply-add uses the static
64-entry bit table. The source arrays are consumed. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def dotAccumulator : List IrreducibleSearch.F → List IrreducibleSearch.F →
    IrreducibleSearch.F → IrreducibleSearch.F
  | a :: as, b :: bs, s => dotAccumulator as bs (s + a * b)
  | _, _, s => s

theorem dotAccumulator_value (as bs : List IrreducibleSearch.F) (s : IrreducibleSearch.F) :
    dotAccumulator as bs s = s + (List.zipWith (· * ·) as bs).sum := by
  induction as generalizing bs s with
  | nil => simp [dotAccumulator]
  | cons a as ih =>
      cases bs with
      | nil => simp [dotAccumulator]
      | cons b bs => simp [dotAccumulator, ih, add_assoc]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDotRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed F₃ dot product, including initialization,
serialization of its output, the final halt, and primitive simulation. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def convolutionLeft {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :=
  List.ofFn (fun i : Fin (j + 1) => IrreducibleSearch.entry a i)
def convolutionRight {d : ℕ} (b : Fin d → IrreducibleSearch.F) (j : ℕ) :=
  List.ofFn (fun i : Fin (j + 1) => IrreducibleSearch.entry b (j - i))

theorem convolution_dot {d : ℕ} (a b : Fin d → IrreducibleSearch.F) (j : ℕ) :
    (List.zipWith (· * ·) (convolutionLeft a j) (convolutionRight b j)).sum =
      IrreducibleSearch.convolution a b j := by
  unfold convolutionLeft convolutionRight
  rw [zipWith_ofFn, List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i =>
    IrreducibleSearch.entry a i * IrreducibleSearch.entry b (j - i)) (j + 1)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-length padded prefixes, with reversal by coefficient rather
than by bit. This is the physical stream preparation needed before a
convolution dot product. A unary count controls one fixed eight-label
program; exhaustion of the coefficient source supplies the zero cell. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

def prefixRoundRegs (regs : Fin 6 → Bool) (as : List IrreducibleSearch.F)
    (bit : Bool) : Fin 6 → Bool :=
  let r := readRegs regs 4 5 (some bit)
  let r := readRegs r 0 2 (coefficientArray as).head?
  readRegs r 1 2 (coefficientArray as).tail.head?

theorem prefix_round (regs : Fin 6 → Bool) (as : List IrreducibleSearch.F)
    (bit : Bool) (count output : List Bool) :
    Trace prefixReverseProgram 7
      (prefixCfg (some 0) regs (coefficientArray as) (bit :: count) output)
      (prefixCfg (some 0) (prefixRoundRegs regs as bit) (coefficientArray as.tail)
        count (coefficientWord (as.headD 0) ++ output)) := by
  have hz : scalarBits (0 : IrreducibleSearch.F) = (false, false) := by decide
  cases as with
  | nil =>
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, prefixReverseProgram, prefixCfg,
        prefixRoundRegs, execInstr, readRegs, coefficientWord_eq, hz,
        Function.update_apply]
      first | done | (funext i; fin_cases i <;> simp)
  | cons a as =>
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, prefixReverseProgram, prefixCfg,
        prefixRoundRegs, execInstr, readRegs, coefficientWord_eq,
        Function.update_apply]
      first | done | (funext i; fin_cases i <;> simp)

theorem prefixReverse_trace (as : List IrreducibleSearch.F)
    (count output : List Bool) (regs : Fin 6 → Bool) :
    ∃ finalRegs, Trace prefixReverseProgram (7 * count.length + 3)
      (prefixCfg (some 0) regs (coefficientArray as) count output)
      (prefixCfg none finalRegs (coefficientArray (as.drop count.length)) []
        (coefficientArray (paddedPrefix count.length as).reverse ++ output)) := by
  induction count generalizing as regs output with
  | nil =>
      simpa [paddedPrefix] using Exists.intro (readRegs regs 4 5 none)
        (prefix_exit regs (coefficientArray as) output)
  | cons bit count ih =>
      obtain ⟨last, ht⟩ := ih as.tail (coefficientWord (as.headD 0) ++ output)
        (prefixRoundRegs regs as bit)
      refine ⟨last, ?_⟩
      have he := (prefix_round regs as bit count output).trans ht
      convert he using 1 <;>
        simp [paddedPrefix, List.reverse_cons, List.append_assoc,
          List.drop_tail] ; omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefixAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact relationship between the paid prefix generator and the streams
used in the complete scalar convolution test. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem paddedPrefix_getElem? (n : ℕ) (as : List IrreducibleSearch.F) (i : ℕ) :
    (paddedPrefix n as)[i]? =
      if i < n then some (as[i]?.getD 0) else none := by
  induction n generalizing as i with
  | zero => simp [paddedPrefix]
  | succ n ih =>
      cases i with
      | zero => cases as <;> simp [paddedPrefix]
      | succ i => simp [paddedPrefix, ih]

theorem paddedPrefix_ofFn {d : ℕ} (a : Fin d → IrreducibleSearch.F) (n : ℕ) :
    paddedPrefix n (List.ofFn a) =
      List.ofFn (fun i : Fin n => IrreducibleSearch.entry a i) := by
  apply List.ext_getElem?
  intro i
  rw [paddedPrefix_getElem?]
  by_cases hn : i < n
  · by_cases hd : i < d
    · simp [ hn, hd, IrreducibleSearch.entry]
    · simp [ hn, hd, IrreducibleSearch.entry]
  · simp [ hn]

theorem paddedPrefix_self (as : List IrreducibleSearch.F) :
    paddedPrefix as.length as = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [paddedPrefix] using congrArg (List.cons a) ih

theorem paddedPrefix_of_length (as : List IrreducibleSearch.F) (n : ℕ)
    (h : as.length = n) : paddedPrefix n as = as := by
  rw [← h, paddedPrefix_self]

theorem paddedPrefix_convolutionLeft {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :
    paddedPrefix (j + 1) (List.ofFn a) = convolutionLeft a j :=
  paddedPrefix_ofFn a (j + 1)

theorem reverse_convolutionLeft {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :
    (convolutionLeft a j).reverse = convolutionRight a j := by
  unfold convolutionLeft convolutionRight
  apply List.ext_getElem (by simp only [List.length_reverse, List.length_ofFn])
  intro i hi hi'
  rw [List.getElem_reverse]
  simp only [List.length_ofFn, List.getElem_ofFn]
  congr 1

theorem paddedPrefix_convolutionRight {d : ℕ} (a : Fin d → IrreducibleSearch.F) (j : ℕ) :
    (paddedPrefix (j + 1) (List.ofFn a)).reverse = convolutionRight a j := by
  rw [paddedPrefix_convolutionLeft, reverse_convolutionLeft]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical split of a concatenated pair of coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

open BitProgram StructuredCalls SubexpSetupStorage IrreducibleSearchProgram

theorem paddedPrefix_append_left (as bs : List IrreducibleSearch.F) :
    paddedPrefix as.length (as ++ bs) = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa [paddedPrefix] using congrArg (List.cons a) ih

end SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramNonconstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control detection of positive-degree coefficients. The constant
coefficient is physically skipped, then every remaining two-bit cell is
read. The result is register 3; no semantic predicate is an instruction. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem scalarBits_nonzero (a : IrreducibleSearch.F) :
    ((scalarBits a).1 || (scalarBits a).2) = decide (a ≠ 0) := by
  fin_cases a <;> decide

def nonconstantRoundRegs (regs : Fin 4 → Bool) (a : IrreducibleSearch.F) : Fin 4 → Bool :=
  let r := readRegs (readRegs regs 0 1 (some (scalarBits a).1)) 2 1 (some (scalarBits a).2)
  let r := Function.update r 0 (decide (a ≠ 0))
  Function.update r 3 (regs 3 || decide (a ≠ 0))

theorem nonconstant_round (regs : Fin 4 → Bool) (a : IrreducibleSearch.F)
    (rest : List Bool) :
    Trace nonconstantProgram 5
      (nonconstantCfg (some 3) regs (coefficientWord a ++ rest))
      (nonconstantCfg (some 3) (nonconstantRoundRegs regs a) rest) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nonconstantProgram, nonconstantCfg,
    nonconstantRoundRegs, execInstr, readRegs, coefficientWord_eq,
    scalarBits_nonzero, Function.update_apply]
  funext i
  fin_cases i ; simp []

theorem nonconstant_loop (as : List IrreducibleSearch.F) (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace nonconstantProgram (5 * as.length + 3)
      (nonconstantCfg (some 3) regs (coefficientArray as))
      (nonconstantCfg none finalRegs []) ∧
      finalRegs 3 = (regs 3 || as.any (fun a => decide (a ≠ 0))) := by
  induction as generalizing regs with
  | nil =>
      refine ⟨readRegs regs 0 1 none, nonconstant_exit regs, ?_⟩
      simp [readRegs]
  | cons a as ih =>
      obtain ⟨last, ht, hv⟩ := ih (nonconstantRoundRegs regs a)
      refine ⟨last, ?_, ?_⟩
      · have he := (nonconstant_round regs a (coefficientArray as)).trans ht
        convert he using 1 <;> simp [coefficientArray_cons] ; omega
      · simpa [nonconstantRoundRegs, Bool.or_assoc] using hv

def nonconstantInitRegs (regs : Fin 4 → Bool) (a : IrreducibleSearch.F) : Fin 4 → Bool :=
  Function.update
    (readRegs (readRegs regs 0 1 (some (scalarBits a).1)) 0 1 (some (scalarBits a).2)) 3 false

theorem nonconstant_init (regs : Fin 4 → Bool) (a : IrreducibleSearch.F)
    (rest : List Bool) :
    Trace nonconstantProgram 3
      (nonconstantCfg (some 0) regs (coefficientWord a ++ rest))
      (nonconstantCfg (some 3) (nonconstantInitRegs regs a) rest) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, nonconstantProgram, nonconstantCfg,
    nonconstantInitRegs, execInstr, readRegs, coefficientWord_eq, Function.update_apply]
  funext i
  fin_cases i ; simp

theorem nonconstant_run (a : IrreducibleSearch.F) (as : List IrreducibleSearch.F)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace nonconstantProgram (5 * as.length + 6)
      (nonconstantCfg (some 0) regs (coefficientArray (a :: as)))
      (nonconstantCfg none finalRegs []) ∧
      finalRegs 3 = as.any (fun x => decide (x ≠ 0)) := by
  obtain ⟨last, ht, hv⟩ := nonconstant_loop as (nonconstantInitRegs regs a)
  refine ⟨last, ?_, ?_⟩
  · have he := (nonconstant_init regs a (coefficientArray as)).trans ht
    simpa only [coefficientArray_cons,
      show 3 + (5 * as.length + 3) = 5 * as.length + 6 by omega] using he
  · simpa [nonconstantInitRegs] using hv

theorem nonconstant_tail {d : ℕ} (a : Fin (d + 1) → IrreducibleSearch.F) :
    IrreducibleSearch.nonconstant a =
      (List.ofFn fun i : Fin d => a i.succ).any (fun x => decide (x ≠ 0)) := by
  simp [IrreducibleSearch.nonconstant, List.finRange_succ,
    List.ofFn_eq_map, Function.comp_def]

theorem nonconstant_vector_run {d : ℕ} (a : Fin (d + 1) → IrreducibleSearch.F)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace nonconstantProgram (5 * d + 6)
      (nonconstantCfg (some 0) regs
        (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) a))
      (nonconstantCfg none finalRegs []) ∧
      finalRegs 3 = IrreducibleSearch.nonconstant a := by
  have he := nonconstant_run (a 0) (List.ofFn fun i : Fin d => a i.succ) regs
  simpa only [List.length_ofFn, ← List.ofFn_succ, coefficientArray_ofFn,
    ← nonconstant_tail] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/


/-! ProductRun -/


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/


/-! MonicAlgebra -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem monicArray_entry {d : ℕ} (c : Fin d → IrreducibleSearch.F) (j : ℕ) :
    ((List.ofFn c ++ [1])[j]?).getD 0 = IrreducibleSearch.candidateEntry c j := by
  by_cases hj : j < d
  · simp [List.getElem?_append, hj, IrreducibleSearch.candidateEntry,
      IrreducibleSearch.entry, show j ≠ d by omega]
  · by_cases he : j = d
    · subst j
      simp [ IrreducibleSearch.candidateEntry, IrreducibleSearch.entry]
    · have hgt : d < j := by omega
      have hz : 0 < j - d := by omega
      have hn : ([1] : List IrreducibleSearch.F)[j-d]? = none :=
        List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)
      simp [List.getElem?_append, hj, he, hn,
        IrreducibleSearch.candidateEntry, IrreducibleSearch.entry]

theorem monicArray_padded {d : ℕ} (c : Fin d → IrreducibleSearch.F) (n : ℕ) :
    paddedPrefix n (List.ofFn c ++ [1]) =
      List.ofFn (fun i : Fin n => IrreducibleSearch.candidateEntry c i) := by
  apply List.ext_getElem?
  intro i
  rw [paddedPrefix_getElem?]
  by_cases hi : i < n
  · simp [ hi, monicArray_entry]
  · simp [ hi]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/


/-! PairProduct -/


/-! Candidate -/


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem pairEncode_injective (d : ℕ) : Function.Injective (pairEncode (d := d)) := by
  intro ab cd h
  apply SubexpTupleRefinement.encodePair_injective (SubexpEnumerationPayload.scalarCode 3)
    (d + 1) (d + 1)
  simpa only [pairEncode, coefficientArray_append, coefficientArray_ofFn] using h

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

/-- A mathematical observer for the proof; every executed test is the concrete
factor-scan callback above. -/
noncomputable def candidateTest (d : ℕ) : List Bool → Bool :=
  Function.extend (encodeTuple (scalarCode 3) : (Fin d → IrreducibleSearch.F) → List Bool)
    IrreducibleSearch.passes (fun _ => false)

theorem candidateTest_encode {d : ℕ} (c : Fin d → IrreducibleSearch.F) :
    candidateTest d (encodeTuple (scalarCode 3) c) = IrreducibleSearch.passes c :=
  (encodeTuple_injective (scalarCode 3) d).extend_apply _ _ _

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem tableWord_factor (d : ℕ) : tableWord ((d + 1) + (d + 1)) =
    ProgramEncoding.encodeRecords (IrreducibleSearchFactorControl.factorRecords d) := by
  unfold tableWord
  rw [IrreducibleSearch.encoded_factorPairs]
  unfold IrreducibleSearchFactorControl.factorRecords
  apply congrArg ProgramEncoding.encodeRecords
  apply List.map_congr_left
  intro ab _
  simp only [IrreducibleSearchFactorControl.pairEncode,
    coefficientArray_append, coefficientArray_ofFn]


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQueryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The per-query denominator is computed in a disjoint 256-stack bank. The
only persistent output is stack 728; the runtime exponent is read from 740. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

abbrev LocalData := State 16 768
abbrev Data := State 40 768

def staged (a : LocalData) : LocalData := copyManyState pairs a

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data (s : ℕ) := State 16 s

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

structure Accumulator where
  output : Word
  outer : Word
  groups : Word
  terms : Word

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end


