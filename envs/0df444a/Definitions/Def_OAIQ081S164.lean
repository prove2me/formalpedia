-- Prove2me | Definitions.Def_OAIQ081S164
-- name    : OAIQ081S164
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:10:49.550142+00:00
-- url     : https://prove2.me/theorems/a31c9683-0309-4f26-8662-2928a9e0c785
-- title:
--   Definitions bundle OAIQ081S164 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.tableInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentBranches.lean), [`SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingCallerProgramPrepare.lean), [`SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingLoaderProgramFinish.lean), [`SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingLoaderProgramParameters.lean), [`SubexponentialSAT_SqrtLog_PackingLoaderProgramReady`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingLoaderProgramReady.lean), [`SubexponentialSAT_Subexp_AssignmentInputProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/AssignmentInputProgram.lean), [`SubexponentialSAT_Subexp_OneHotAlphabetProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/OneHotAlphabetProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S142`, `OAIQ081S145`, `OAIQ081S147`, `OAIQ081S149` and `OAIQ081S150` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S172`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S147
import Definitions.Def_OAIQ081S149
import Definitions.Def_OAIQ081S150

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_OneHotAlphabetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Runtime one-hot alphabet generation

The unary input length r is data. Each loop iteration constructs one r-bit
one-hot word using the checked repeated-copy program and prepends its frame.
The final order is the decreasing order of the hot bit's position.
-/

namespace SubexponentialSAT.Subexp.OneHotAlphabetProgram

open BitProgram StructuredCalls TupleProgram

theorem body_eval (regs : Fin 5 → Bool) (i n : ℕ) (out : List Bool) :
    ∃ rf, Eval body (bodyCost i n) (state regs i n out)
      (state rf (i + 1) n (true :: Encoding.frame (word i n) ++ out)) := by
  let a := state regs i n out
  let b := copied 1 2 a
  let c := pushedState 2 0 true b
  let d := copied 0 3 c
  let e := zeroedThird d
  let f := repeatState (resetThree e.regs) i n (zeros n ++ true :: zeros i) [] out
  let g := pushedState 6 0 false f
  let h := escapedState emitter g
  let j := pushedState 6 0 true h
  let k := pushedState 1 0 false j
  have h1 := copy_eval 1 2 a (by decide) (by decide) (by decide) rfl
  have h2 := pushConst_eval 2 0 true b
  have h3 := copy_eval 0 3 c (by decide) (by decide) (by decide) rfl
  have h4 : Eval zeroThird 1 d e := .base (.atom _ _)
  have he : e = repeatState e.regs i n (true :: zeros i) (unary n) out := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext j
    fin_cases j <;> simp [ d, c, b, a, copied,
      StackRoutines.copyStacks, state ]
  have hr : ∀ j : Fin 3, e.regs (repeatRegisters j) = false := by
    intro j
    fin_cases j <;> simp [e, zeroedThird, d, copied, repeatRegisters, readRegs]
  have h5 := repeatZeros_eval e.regs i n (true :: zeros i) out hr
  rw [← he] at h5
  have h6 := pushConst_eval 6 0 false f
  have h7 := escape_eval_state emitter g
  have h8 := pushConst_eval 6 0 true h
  have h9 := pushConst_eval 1 0 false j
  have hk : k = state k.regs (i + 1) n (true :: Encoding.frame (word i n) ++ out) := by
    apply congrArg (StructuredProgram.State.mk k.regs)
    funext v
    fin_cases v <;> simp [ j, h, g, f, emitter,
      repeatState, word, frame_eq_escaped, List.reverse_append,
      List.replicate_succ, List.append_assoc]
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  change Eval body _ a k at ht
  rw [hk] at ht
  refine ⟨k.regs, ?_⟩
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  simp [bodyCost, a, state, b, copied, c, f, g, emitter, repeatState,
    StackRoutines.copyStacks]
  omega

theorem visits (i n : ℕ) (regs : Fin 5 → Bool) (acc : List (List Bool)) :
    ∃ costs ticks rf,
      UnaryForPrograms.Visits loopPorts body costs ticks
        (state regs i n (ProgramEncoding.encodeRecords acc))
        (state rf (i + n) 0 (ProgramEncoding.encodeRecords (rows i n ++ acc))) ∧
      ticks ≤ 40 * (n + 1) * (i + n + 1) := by
  induction n generalizing i regs acc with
  | zero =>
      refine ⟨[], 2, poppedRegs regs 0, ?_, by nlinarith⟩
      have h := UnaryForPrograms.Visits.done
        (p := loopPorts) (body := body) (state regs i 0 (ProgramEncoding.encodeRecords acc)) rfl
      simpa only [popped_state, Nat.zero_sub, Nat.add_zero, rows, List.nil_append] using h
  | succ n ih =>
      obtain ⟨rf, hb⟩ := body_eval (poppedRegs regs (n + 1)) i n
        (ProgramEncoding.encodeRecords acc)
      have hbits : true :: Encoding.frame (word i n) ++ ProgramEncoding.encodeRecords acc =
          ProgramEncoding.encodeRecords (word i n :: acc) := rfl
      rw [hbits] at hb
      obtain ⟨costs, ticks, rg, ht, hbound⟩ := ih (i + 1) rf (word i n :: acc)
      have hp : UnaryForPrograms.popped loopPorts
          (state regs i (n + 1) (ProgramEncoding.encodeRecords acc)) =
          state (poppedRegs regs (n + 1)) i n (ProgramEncoding.encodeRecords acc) := by
        rw [popped_state, Nat.add_sub_cancel]
      rw [← hp] at hb
      have hc : (state rf (i + 1) n (ProgramEncoding.encodeRecords (word i n :: acc))).stacks
          loopPorts.counter = (UnaryForPrograms.popped loopPorts
            (state regs i (n + 1) (ProgramEncoding.encodeRecords acc))).stacks loopPorts.counter := by
        rw [hp]
        rfl
      have h := UnaryForPrograms.Visits.step (p := loopPorts) (body := body)
        (by simp [state, loopPorts]) hb hc ht
      refine ⟨bodyCost i n :: costs, bodyCost i n + ticks + 2, rg, ?_, ?_⟩
      · simpa only [rows, List.append_assoc, List.singleton_append, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using h
      · dsimp [bodyCost]
        nlinarith

theorem command_eval (regs : Fin 5 → Bool) (n : ℕ) :
    ∃ ticks, ticks ≤ 60 * (n + 1) ^ 2 ∧
      Eval command ticks (inputState regs n) (outputState n) := by
  let a := inputState regs n
  let b := pushedState 5 0 false a
  let c := pushedState 6 0 false b
  have hc : c = state c.regs 0 n (ProgramEncoding.encodeRecords []) := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext j
    fin_cases j <;> rfl
  obtain ⟨costs, ticks, rf, hv, ht⟩ := visits 0 n c.regs []
  simp only [Nat.zero_add, List.append_nil] at hv
  have hr := hv.eval
  rw [← hc] at hr
  let d := state rf n 0 (ProgramEncoding.encodeRecords (rows 0 n))
  let e : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 1 d.stacks⟩
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 5 e.stacks⟩
  have h1 := pushConst_eval 5 0 false a
  have h2 := pushConst_eval 6 0 false b
  have h4 := TupleProgram.clear_eval 1 0 1 d
  have h5 := TupleProgram.clear_eval 5 0 1 e
  have h6 := Eval.base (CandidateScoreProgram.resetList_eval (List.finRange 5) f)
  have hreset : (⟨CandidateScoreProgram.resetValues (List.finRange 5) f.regs, f.stacks⟩ : Data) =
      outputState n := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      simp [CandidateScoreProgram.resetValues_apply]
    · funext j
      fin_cases j <;> simp [f, e, d, state, StackRoutines.clearStacks ]
  rw [hreset] at h6
  have h := h1.seq (h2.seq (hr.seq (h4.seq (h5.seq h6))))
  change Eval command _ a (outputState n) at h
  refine ⟨_, ?_, h⟩
  have hd : (d.stacks 1).length = n := by simp [d, state]
  have he : (e.stacks 5).length = 1 := by simp [e, d, state, StackRoutines.clearStacks]
  simp only [hd, he, List.length_finRange]
  nlinarith

theorem program_runsIn (regs : Fin 5 → Bool) (n : ℕ) :
    RunsIn program (60 * (n + 1) ^ 2 + 1)
      ((inputState regs n).withPC (some program.entry)) ((outputState n).withPC none) := by
  obtain ⟨ticks, ht, he⟩ := command_eval regs n
  exact ⟨ticks + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 6⟩

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram


noncomputable def tableInput (a : FactorAssignmentProgram.Data) (factor : ℕ) :=
  projectState FactorTableProgram.callerRegisters id (identified a factor)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

theorem colorAlphabet_eval (a : Data) (n : ℕ) (hc : Clean a)
    (h1 : a.stacks 1 = unary n) :
    Writes colorAlphabet a 7 (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 n))
      (60 * (n + 1) ^ 2 + 1) := by
  let pre := project (register (r := 5) (by decide)) (stack (s := 7) (by decide))
    (prepareState 31 work [(1, 12)] a)
  have hp : pre = OneHotAlphabetProgram.inputState pre.regs n := by
    apply congrArg (StructuredProgram.State.mk pre.regs)
    funext i
    have h := prepare_one_local (r := 5) (s := 7) (by decide) (by decide) a hc 1 0 i
    change pre.stacks i = _
    change pre.stacks i = _ at h
    rw [h]
    fin_cases i <;> simp [ h1]
  obtain ⟨ticks, htime, ht⟩ := OneHotAlphabetProgram.program_runsIn pre.regs n
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval OneHotAlphabetProgram.program
    (by decide) (by decide) [(1, 12)] 6 7 a (OneHotAlphabetProgram.outputState n)
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, hs, hb, ?_⟩
  intro B ha hout _
  have ho : Within (OneHotAlphabetProgram.outputState n) B := by
    intro j; fin_cases j <;> simp [OneHotAlphabetProgram.outputState, hout]
  have h := callCost_le (r := 5) (s := 7) (by decide) (by decide)
    [(1, 12)] 6 7 a _ ticks B (by decide) ha ho
  exact h.trans (Nat.add_le_add_right htime _)

theorem seedSize_eval (a : Data) (delta D E : ℕ) (hc : Clean a)
    (h4 : a.stacks 4 = unary D) (h6 : a.stacks 6 = unary (delta + 1))
    (h5 : a.stacks 5 = unary E) :
    Writes seedSize a 47 (unary (seedCount delta D E))
      ((delta + 1) * (7 * D + 7) + 3 + (7 * E + 5)) := by
  obtain ⟨ticks, b, hb, hs, hc', htime⟩ := repeat_eval a 4 6 47 D (delta + 1) hc h4 h6
    (by decide) (by decide) (by simp) (by decide)
  have hcopy := copy_eval 5 47 31 b (by decide) (by decide) (by decide) hc'.2
  let c := copyState 5 47 b
  have hout : c.stacks = Function.update a.stacks 47 (unary (seedCount delta D E)) := by
    funext j
    by_cases hj : j = 47
    · subst j
      simp [c, copyState_stack, hs, h5, seedCount, unary]
    · simp [c, copyState_stack, hs, hj]
  refine ⟨_, c, hb.seq hcopy, hout,
    clean_of_update a c 47 _ hc (by decide) (by decide) hout, ?_⟩
  intro B ha hresult hB
  have hproduct : (unary ((delta + 1) * D)).length ≤ B := by
    simp only [List.length_replicate, seedCount] at hresult ⊢
    omega
  have ht := htime B ha hproduct hB
  simp only [hs, Function.update_of_ne (show (5 : Fin 48) ≠ 47 by decide), h5,
    List.length_replicate]
  omega

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Install the packing scorer's depth and binary parameter bank after the
native alphabet/assignment producer has finished using its low workspace. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage SubexponentialSAT.Subexp
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem finish_eval (outside : Store) (r Q n f : ℕ) (pairs : List Bool) :
    ∃ rf, Eval finish (finishBudget outside)
      (framed outside (AssignmentInitProgram.outputState (context r Q n f pairs)))
      (framed outside (readyLocal rf r Q n f pairs
        (outside 56) (outside 57) (outside 58) (outside 59))) := by
  let a := framed outside (AssignmentInitProgram.outputState (context r Q n f pairs))
  let b := TupleProgram.pushedState 34 0 true (TupleProgram.pushedState 34 0 true a)
  let e := copyManyState parameterCopies b
  have h1 : Eval addDepth 4 a b :=
    (TupleProgram.pushConst_eval 34 0 true a).seq
      (TupleProgram.pushConst_eval 34 0 true (TupleProgram.pushedState 34 0 true a))
  have h31 : b.stacks 31=[] := by
    simp [b,a,framed_stack,AssignmentInitProgram.outputState,
      AssignmentInitProgram.state]
  have h2 := copyMany_eval 31 parameterCopies b (by
    intro p hp; simp [parameterCopies] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide) h31
  have he : e=framed outside (readyLocal e.regs r Q n f pairs
      (outside 56) (outside 57) (outside 58) (outside 59)) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [readyLocal]
    · funext i
      fin_cases i <;> simp [e,b,a,parameterCopies,copyManyState,copyState,StackRoutines.copyStacks,
        TupleProgram.pushedState,framed_stack,readyLocal,AssignmentInitProgram.outputState,
        AssignmentInitProgram.state,context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
  have hcost : 4+copyManyCost parameterCopies b=finishBudget outside := by
    simp [finishBudget,parameterCopies,copyManyCost,copyState,StackRoutines.copyStacks,
      b,a,TupleProgram.pushedState,framed_stack]
    omega
  have h := h1.seq h2
  change Eval finish _ a e at h
  rw [hcost,he] at h
  exact ⟨e.regs,h⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of the actual binary radius and coordinate parameters. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem parameters_eval (outside : Store) (regs : Fin 16 → Bool)
    (n f : ℕ) (pairs : List Bool) :
    ∃ t rf, t ≤ parameterBudget outside ∧ Eval parameters t
      (framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState regs 0 0 0 n f pairs))
      (framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState rf
        (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
        (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) 0 n f pairs)) := by
  let a := framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState regs 0 0 0 n f pairs)
  obtain ⟨t1,r1,he1,ht1⟩ := unaryCommand_eval radiusPorts a
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [a,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
  let b := framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState r1
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) 0 0 n f pairs)
  have hb : (⟨r1,Function.update a.stacks (radiusPorts 1)
      (List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (a.stacks (radiusPorts 0))) true)⟩ : Data)=b := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [b,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
    · funext i
      fin_cases i <;> simp [a,b,framed_stack,radiusPorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
  rw [hb] at he1
  obtain ⟨t2,r2,he2,ht2⟩ := unaryCommand_eval coordinatePorts b
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
    (by simp [b,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState])
  let e := framed outside (SubexponentialSAT.Subexp.AssignmentInputProgram.inputState r2
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) 0 n f pairs)
  have he : (⟨r2,Function.update b.stacks (coordinatePorts 1)
      (List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (b.stacks (coordinatePorts 0))) true)⟩ : Data)=e := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [e,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
    · funext i
      fin_cases i <;> simp [b,e,framed_stack,coordinatePorts,SubexponentialSAT.Subexp.AssignmentInputProgram.inputState]
  rw [he] at he2
  refine ⟨t1+t2,r2,?_,he1.seq he2⟩
  simpa [parameterBudget,a,b,framed_stack,radiusPorts,coordinatePorts,
    SubexponentialSAT.Subexp.AssignmentInputProgram.inputState] using Nat.add_le_add ht1 ht2

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact selector memory and environment from the physically generated
alphabet, retaining all ambient head addresses before factor addresses. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem readyLocal_low (regs : Fin 16 → Bool) (r Q n f : ℕ)
    (pairs nb sb mb rb : List Bool) (i : Fin 48) (hi : i.val < 20) :
    (readyLocal regs r Q n f pairs nb sb mb rb).stacks i =
      (AssignmentInitProgram.outputState (context r Q n f pairs)).stacks i := by
  have hs : i≠20 ∧ i≠21 ∧ i≠22 ∧ i≠23 ∧ i≠34 := by
    constructor <;> try (intro h; subst i; norm_num at hi)
    constructor <;> try (intro h; subst i; norm_num at hi)
    constructor <;> try (intro h; subst i; norm_num at hi)
    constructor <;> (intro h; subst i; norm_num at hi)
  simp [readyLocal,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2]

theorem ready_high (regs : Fin 16 → Bool) {r Q : ℕ}
    (a : Word r Q) (tail : List (Word r Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes r Q)
    (n f : ℕ) (raw : List PairScoreProgram.PlanPair) (nb sb mb rb : List Bool) :
    SequentialProgram.HighState
      (PackingProgram.Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail) (n+f) raw)
        nb sb mb rb)
      (readyLocal regs r Q n f (PairScoreProgram.pairRecords raw) nb sb mb rb).stacks := by
  intro i hi
  fin_cases i <;> first
    | (norm_num at hi; done)
    | simp [readyLocal,PackingProgram.Assembly.environment,ScoreBuilderRawInput.environment,
        ScoreBuilderProgram.environment,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
        context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount,
        AssignmentInputProgram.unary,AssignmentSeedRange.seedRecords,
        PairPreparationProgram.seedBytes,SelectionTableProgram.unary,AssignmentInitProgram.unary,
        ←hrows,Nat.add_comm]
      <;> rfl

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stage the actual selected words and owner plans for the native layout
suffix. The incidence dimension is converted from its actual binary master. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem prepareSuffix_eval (outside : Store) (regs : Fin 16 → Bool)
    (p : LayoutProgram.NativeFrontend.Params) (hdelta : p.Δ=1)
    (h52 : outside 52=[])
    (hD : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=p.D)
    (hwidth : outside 53=p.width)
    (halphabet : outside 54=ProgramEncoding.encodeRecords p.alphabet)
    (hplans : outside 61=p.planStream) (hwords : outside 62=p.rows.flatten) :
    ∃ t rf, t ≤ prepareBudget outside ∧ Eval prepareSuffix t
      (framed outside (⟨regs,fun _=>[]⟩ : Small))
      (framed outside (LayoutProgram.NativeFrontend.plansState p rf)) := by
  let a := framed outside (⟨regs,fun _=>[]⟩ : Small)
  obtain ⟨tu,ru,hu,htu⟩ := unaryCommand_eval dimensionPorts a
    (by simp [a,dimensionPorts,framed_stack])
    (by simp [a,dimensionPorts,framed_stack])
    (by simp [a,dimensionPorts,framed_stack])
    (by simp [a,dimensionPorts,framed_stack])
  let b : Local := ⟨ru,Function.update a.stacks 42 (List.replicate p.D true)⟩
  have hub : Eval (unaryCommand dimensionPorts) tu a b := by
    simpa [b,dimensionPorts,a,framed_stack,hD] using hu
  let c := TupleProgram.pushedState 44 0 false (TupleProgram.pushedState 43 0 true b)
  have hl : Eval prepareLiterals 4 b c :=
    (TupleProgram.pushConst_eval 43 0 true b).seq
      (TupleProgram.pushConst_eval 44 0 false (TupleProgram.pushedState 43 0 true b))
  have hc52 : c.stacks 52=[] := by
    simp [c,b,a,framed_stack,h52]
  have hp := copyMany_eval 52 prepareCopies c (by
    intro q hq; simp [prepareCopies] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> decide) hc52
  let e := copyManyState prepareCopies c
  have he : e=framed outside (LayoutProgram.NativeFrontend.plansState p e.regs) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext
    · simp [LayoutProgram.NativeFrontend.plansState]
    · funext i
      fin_cases i <;> simp [e,c,b,a,prepareCopies,copyManyState,copyState,StackRoutines.copyStacks,
        TupleProgram.pushedState,framed_stack,LayoutProgram.NativeFrontend.plansState,
        LayoutProgram.NativeFrontend.Params.input,LayoutProgram.NativeFrontend.Params.base,
        PackingFrontend.Params.input,PackingProgram.inputState,SubexpPlanAlphabetBase.scopeBytes,
        Encoding.encodeList,hdelta,hwidth,halphabet,hplans,hwords]
  have hcost : copyManyCost prepareCopies c =
      7*((outside 61).length+(outside 62).length+(outside 53).length+(outside 54).length)+20 := by
    simp [prepareCopies,copyManyCost,copyState,StackRoutines.copyStacks,c,b,a,
      TupleProgram.pushedState,framed_stack]
    omega
  have hall := hub.seq (hl.seq hp)
  change Eval prepareSuffix (tu+(4+copyManyCost prepareCopies c)) a e at hall
  rw [he] at hall
  refine ⟨tu+(4+copyManyCost prepareCopies c),e.regs,?_,hall⟩
  rw [hcost]
  have htu' : tu ≤ LeafParametersProgram.Serialization.unaryCopyBound (outside 58)+1 := by
    simpa [dimensionPorts,a,framed_stack] using htu
  dsimp [prepareBudget]
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


