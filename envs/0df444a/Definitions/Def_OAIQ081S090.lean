-- Prove2me | Definitions.Def_OAIQ081S090
-- name    : OAIQ081S090
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:09:15.440665+00:00
-- url     : https://prove2.me/theorems/39ddadf7-d7eb-44e0-b343-3278bf723082
-- title:
--   Definitions bundle OAIQ081S090 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 11 definitions and 17 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.metadataRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.numeratorBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Guard.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.emit`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.reverseCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram.filterCall`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankRun`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingBucketSelect`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingExtractionState`, `SubexponentialSAT_Subexp_PackingFrameCount`, `SubexponentialSAT_Subexp_PackingFrameSkip`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingOutputSemantics`, `SubexponentialSAT_Subexp_PackingUnaryMin`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S067`, `OAIQ081S070`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S074` and `OAIQ081S075` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108` and `OAIQ081S113`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S074
import Definitions.Def_OAIQ081S075

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

namespace Guard

abbrev Data := State 13 11

end Guard

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
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

theorem body_eval (regs : Fin 8 → Bool) (bits source count : List Bool) :
    ∃ regs', Eval body (8 * bits.length + 10)
      (state regs (Encoding.frame bits ++ source) [] count)
      (ready regs' source (true :: count)) := by
  obtain ⟨d1, t1, hs1⟩ := readFrame_eval (0 : Fin 3) 1 (by decide)
    (state regs (Encoding.frame bits ++ source) [] count) bits source rfl rfl
  have hd1 : d1 = state d1.regs source bits.reverse count := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs1]
    funext i
    fin_cases i <;> simp []
  rw [hd1] at t1
  let r2 := readRegs d1.regs 0 1 none
  have t2 : Eval clearPayload (2 * bits.length + 3)
      (state d1.regs source bits.reverse count) (state r2 source [] count) := by
    have hc := TupleProgram.clear_eval (1 : Fin 3) (0 : Fin 8) 1
      (state d1.regs source bits.reverse count)
    have hs : (⟨r2, StackRoutines.clearStacks 1
        (state d1.regs source bits.reverse count).stacks⟩ : StructuredProgram.State 8 3) =
        state r2 source [] count := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      first | done | (funext i; fin_cases i <;> rfl)
    change Eval clearPayload (2 * bits.reverse.length + 3)
      (state d1.regs source bits.reverse count)
      (⟨r2, StackRoutines.clearStacks 1
        (state d1.regs source bits.reverse count).stacks⟩ : StructuredProgram.State 8 3) at hc
    rw [hs] at hc
    simpa only [List.length_reverse] using hc
  let r3 := Function.update r2 (0 : Fin 8) true
  have t3 : Eval increment 2 (state r2 source [] count) (state r3 source [] (true :: count)) := by
    have hp := TupleProgram.pushConst_eval (2 : Fin 3) (0 : Fin 8) true
      (state r2 source [] count)
    have hs : TupleProgram.pushedState 2 0 true (state r2 source [] count) =
        state r3 source [] (true :: count) := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      first | done | (funext i; fin_cases i <;> rfl)
    rw [hs] at hp
    exact hp
  have t4 := peek_eval r3 source (true :: count)
  refine ⟨r3, ?_⟩
  convert t1.seq (t2.seq (t3.seq t4)) using 1 ; simp [] ; omega

theorem loop_eval (xs : List (List Bool)) (regs : Fin 8 → Bool) (count : List Bool) :
    ∃ regs', Eval loop (budget xs)
      (ready regs (words xs) count)
      (state regs' [] [] (List.replicate xs.length true ++ count)) := by
  induction xs generalizing regs count with
  | nil =>
    refine ⟨(ready regs [] count).regs, ?_⟩
    simpa [loop, budget, words, ready, state] using
      (Eval.while_false (body := body) (ready_nil regs count))
  | cons bits xs ih =>
    let r0 := (ready regs (words (bits :: xs)) count).regs
    obtain ⟨r1, t1⟩ := body_eval r0 bits (words xs) count
    have ht1 : Eval body (8 * bits.length + 10)
        (ready regs (words (bits :: xs)) count)
        (ready r1 (words xs) (true :: count)) := by
      simpa only [ready, words, r0] using t1
    obtain ⟨rf, t2⟩ := ih r1 (true :: count)
    have ht := Eval.while_true (ready_cons regs bits (words xs) count) ht1 t2
    have hcount : List.replicate xs.length true ++ true :: count =
        List.replicate (bits :: xs).length true ++ count := by
      rw [List.length_cons, List.replicate_add]
      simp [List.append_assoc]
    refine ⟨rf, ?_⟩
    convert ht using 1
    · simp only [budget, List.map_cons, List.sum_cons]
      omega
    · rfl
    · exact congrArg (state rf [] []) hcount.symm

/-- The counter consumes actual frames and emits one true bit per frame. -/
theorem program_trace (xs : List (List Bool)) (regs : Fin 8 → Bool) (count : List Bool) :
    ∃ n ≤ 11 * (words xs).length + 3, ∃ regs',
      Trace program n
        ((state regs (words xs) [] count).withPC (some program.entry))
        ((state regs' [] [] (List.replicate xs.length true ++ count)).withPC none) := by
  obtain ⟨rf, ht⟩ := loop_eval xs regs count
  refine ⟨1 + budget xs + 1, by have := budget_le xs; omega, rf, ?_⟩
  exact compiled_halt_trace ((peek_eval regs (words xs) count).seq ht) 0 2

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

/-- Count words are compared by actual simultaneous pops. Both inputs are
cleared, and the result is a canonical true-unary minimum. -/
theorem program_trace (left right output : List Bool) (regs : Fin 8 → Bool) :
    ∃ n ≤ 9 * (left.length + right.length) + 12, ∃ regs',
      Trace program n ((state regs left right output).withPC (some program.entry))
        ((state regs' [] []
          (List.replicate (min left.length right.length) true ++ output)).withPC none) := by
  obtain ⟨n, hn, rf, ls, rs, ht, hl, hr⟩ := core_trace left right output regs
  let result := List.replicate (min left.length right.length) true ++ output
  let r1 := readRegs rf 0 1 none
  let r2 := readRegs r1 0 1 none
  have h0 : Eval (.call core) n (state regs left right output) (state rf ls rs result) :=
    .call _ ht
  have h1 : Eval (.call (StackRoutines.clearProgram 0 0 1)) (2 * ls.length + 3)
      (state rf ls rs result) (state r1 [] rs result) := by
    have hc := TupleProgram.clear_eval (0 : Fin 3) (0 : Fin 8) 1 (state rf ls rs result)
    have hs : (⟨r1, StackRoutines.clearStacks 0 (state rf ls rs result).stacks⟩ :
        StructuredProgram.State 8 3) = state r1 [] rs result := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      first | done | (funext i; fin_cases i <;> rfl)
    change Eval (.call (StackRoutines.clearProgram 0 0 1)) (2 * ls.length + 3)
      (state rf ls rs result)
      (⟨r1, StackRoutines.clearStacks 0 (state rf ls rs result).stacks⟩ :
        StructuredProgram.State 8 3) at hc
    rw [hs] at hc
    exact hc
  have h2 : Eval (.call (StackRoutines.clearProgram 1 0 1)) (2 * rs.length + 3)
      (state r1 [] rs result) (state r2 [] [] result) := by
    have hc := TupleProgram.clear_eval (1 : Fin 3) (0 : Fin 8) 1 (state r1 [] rs result)
    have hs : (⟨r2, StackRoutines.clearStacks 1 (state r1 [] rs result).stacks⟩ :
        StructuredProgram.State 8 3) = state r2 [] [] result := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      first | done | (funext i; fin_cases i <;> rfl)
    change Eval (.call (StackRoutines.clearProgram 1 0 1)) (2 * rs.length + 3)
      (state r1 [] rs result)
      (⟨r2, StackRoutines.clearStacks 1 (state r1 [] rs result).stacks⟩ :
        StructuredProgram.State 8 3) at hc
    rw [hs] at hc
    exact hc
  refine ⟨n + (2 * ls.length + 3 + (2 * rs.length + 3)) + 1, ?_, r2, ?_⟩
  · have hm := Nat.min_le_left left.length right.length
    omega
  · exact compiled_halt_trace (h0.seq (h1.seq h2)) 0 2

end SubexponentialSAT.Subexp.PackingUnaryMin

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

theorem countCall_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (rows query bucket saved keys minimum table result : List Bool) :
    ∃ n ≤ 11 * (words xs).length + 3, ∃ regs',
      Eval countCall n
        (state regs rows query bucket saved keys (words xs) minimum table [] result)
        (state regs' rows query bucket saved keys [] minimum table
          (List.replicate xs.length true) result) := by
  obtain ⟨n, hn, rf, ht⟩ := PackingFrameCount.program_trace xs regs []
  have he := eval_call_lifted PackingFrameCount.program id countPorts
    (state regs rows query bucket saved keys (words xs) minimum table [] result)
    Function.injective_id countPorts_injective ht
  rw [embed_count, embed_count] at he
  exact ⟨n, hn, rf, by simpa only [List.append_nil] using he⟩

theorem minimumCall_eval (m n : ℕ) (regs : Fin 8 → Bool)
    (rows query bucket saved keys scan table : List Bool) :
    ∃ steps ≤ 9 * (m + n) + 12, ∃ regs',
      Eval minimumCall steps
        (state regs rows query bucket saved keys scan (List.replicate m true)
          table (List.replicate n true) [])
        (state regs' rows query bucket saved keys scan [] table []
          (List.replicate (min m n) true)) := by
  obtain ⟨steps, ht, rf, hrun⟩ := PackingUnaryMin.program_trace
    (List.replicate m true) (List.replicate n true) [] regs
  have he := eval_call_lifted PackingUnaryMin.program id minimumPorts
    (state regs rows query bucket saved keys scan (List.replicate m true)
      table (List.replicate n true) [])
    Function.injective_id minimumPorts_injective hrun
  rw [embed_minimum, embed_minimum] at he
  exact ⟨steps, by simpa only [List.length_replicate] using ht, rf,
    by simpa only [List.length_replicate, List.append_nil] using he⟩

end SubexponentialSAT.Subexp.PackingBucketCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameSkip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual framed-pre skip call with arbitrary surrounding packing data. -/

namespace SubexponentialSAT.Subexp.PackingFrameSkip

open BitProgram StructuredCalls MatrixProgramSupport

variable {s : ℕ}

theorem command_eval (count source : Fin s) (hcs : count ≠ source)
    (a : Data s) (pre : List (List Bool)) (rest : List Bool)
    (hc : (a.stacks count).length = pre.length)
    (hs : a.stacks source = words pre ++ rest) :
    Eval (command count source) (BlockZeroProgram.skipCost pre) a
      (finalState count source a pre rest) := by
  let x : StructuredProgram.State 3 2 :=
    ⟨![a.regs 0, a.regs 1, a.regs 2], ![a.stacks count, words pre ++ rest]⟩
  let y : StructuredProgram.State 3 2 :=
    ⟨![false, false, a.regs 2 || !pre.isEmpty], ![[], rest]⟩
  have hw := frames_eq_words pre
  have hx : embedState registers (stackPorts count source) a x = a := by
    apply SelectorMapProgram.embed_eq _ _ registers_injective (stacks_injective count source hcs)
    · intro i
      fin_cases i <;> rfl
    · intro i
      fin_cases i
      · rfl
      · exact hs
    · intros; rfl
    · intros; rfl
  have hy : embedState registers (stackPorts count source) a y =
      finalState count source a pre rest := by
    apply SelectorMapProgram.embed_eq _ _ registers_injective (stacks_injective count source hcs)
    · intro i
      fin_cases i <;> simp [y, finalState, registers]
    · intro i
      fin_cases i <;> simp [y, finalState, stackPorts, hcs]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [registers] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [registers] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [registers] using h.symm⟩
      simp [finalState, h0, h1, h2]
    · intro j hj
      have hcj : j ≠ count := fun h => hj ⟨0, by simpa [stackPorts] using h.symm⟩
      have hsj : j ≠ source := fun h => hj ⟨1, by simpa [stackPorts] using h.symm⟩
      simp [finalState, hcj, hsj]
  have ht : Trace BlockZeroProgram.skipProgram (BlockZeroProgram.skipCost pre)
      (x.withPC (some BlockZeroProgram.skipProgram.entry)) (y.withPC none) := by
    simpa only [x, y, BlockZeroProgram.skipCfg, hw, StructuredProgram.State.withPC] using
      BlockZeroProgram.skipProgram_trace pre rest (a.stacks count) hc
        (a.regs 0) (a.regs 1) (a.regs 2)
  have he := eval_call_lifted BlockZeroProgram.skipProgram registers (stackPorts count source)
    a registers_injective (stacks_injective count source hcs) ht
  simpa only [hx, hy, command] using he

end SubexponentialSAT.Subexp.PackingFrameSkip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read one block's vertex from an actual serialized type bucket. -/

namespace SubexponentialSAT.Subexp.PackingBucketSelect

open BitProgram StructuredCalls MatrixProgramSupport

/-- The runtime unary block index is consumed by a real frame-skipping loop;
the residual bucket tail is physically cleared. -/
theorem command_eval (key vertex : List Bool) (pre rest : List (List Bool))
    (regs : Fin 8 → Bool) :
    ∃ n ≤ 20 * ((Encoding.frame key ++ words (pre ++ vertex :: rest)).length + 1),
      ∃ rf, Eval command n
        (state regs (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
          (List.replicate pre.length true) [] [])
        (state rf [] key [] vertex []) := by
  let payload := words (pre ++ vertex :: rest)
  let suffix := Encoding.frame vertex ++ words rest
  obtain ⟨a, ha, hsa⟩ := readWord_eval (0 : Fin 5) 1 4
    (by decide) (by decide) (by decide)
    (state regs (Encoding.frame key ++ payload) [] (List.replicate pre.length true) [] [])
    key payload rfl rfl rfl
  have hea : a = state a.regs payload key (List.replicate pre.length true) [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext i
    fin_cases i <;> simp [state]
  rw [hea] at ha
  let a' := state a.regs payload key (List.replicate pre.length true) [] []
  have hs : a'.stacks 0 = words pre ++ suffix := by
    simp [a', state, payload, suffix, words_append, words]
  have hb := PackingFrameSkip.command_eval (2 : Fin 5) 0 (by decide) a' pre suffix
    (by simp [a', state]) hs
  let b := PackingFrameSkip.finalState 2 0 a' pre suffix
  have heb : b = state b.regs suffix key [] [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    funext i
    fin_cases i <;> simp [b, a', state, PackingFrameSkip.finalState]
  change Eval (PackingFrameSkip.command 2 0) (BlockZeroProgram.skipCost pre) a' b at hb
  rw [heb] at hb
  obtain ⟨c, hc, hsc⟩ := readWord_eval (0 : Fin 5) 3 4
    (by decide) (by decide) (by decide)
    (state b.regs suffix key [] [] []) vertex (words rest) rfl rfl rfl
  have hec : c = state c.regs (words rest) key [] vertex [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsc]
    funext i
    fin_cases i <;> simp [state]
  rw [hec] at hc
  let rf := readRegs c.regs 0 1 none
  have hd : Eval (.call (StackRoutines.clearProgram 0 0 1))
      (2 * (words rest).length + 3)
      (state c.regs (words rest) key [] vertex []) (state rf [] key [] vertex []) := by
    have h := TupleProgram.clear_eval (0 : Fin 5) (0 : Fin 8) 1
      (state c.regs (words rest) key [] vertex [])
    have he : (⟨rf, StackRoutines.clearStacks 0
        (state c.regs (words rest) key [] vertex []).stacks⟩ : Data 5) =
        state rf [] key [] vertex [] := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      first | done | (funext i; fin_cases i <;> rfl)
    change Eval (.call (StackRoutines.clearProgram 0 0 1)) (2 * (words rest).length + 3)
      (state c.regs (words rest) key [] vertex [])
      (⟨rf, StackRoutines.clearStacks 0
        (state c.regs (words rest) key [] vertex []).stacks⟩ : Data 5) at h
    rw [he] at h
    exact h
  refine ⟨(9 * key.length + 7) + (BlockZeroProgram.skipCost pre +
    ((9 * vertex.length + 7) + (2 * (words rest).length + 3))), ?_, rf, ?_⟩
  · have h := PackingFrameSkip.cost_le pre
    simp only [words_append, words, List.length_append, Encoding.length_frame]
    omega
  · exact ha.seq (hb.seq (hc.seq hd))

theorem program_trace (key vertex : List Bool) (pre rest : List (List Bool))
    (regs : Fin 8 → Bool) :
    ∃ n ≤ 21 * ((Encoding.frame key ++ words (pre ++ vertex :: rest)).length + 1),
      ∃ rf, Trace program n
        ((state regs (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
          (List.replicate pre.length true) [] []).withPC (some program.entry))
        ((state rf [] key [] vertex []).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval key vertex pre rest regs
  exact ⟨n + 1, by omega, rf, compiled_halt_trace he 0 3⟩

end SubexponentialSAT.Subexp.PackingBucketSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical ports for block-major extraction and its bucket reader. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem selectCall_eval (key vertex : List Bool) (pre rest : List (List Bool))
    (regs : Fin 8 → Bool) (c : Context) :
    ∃ n ≤ 21 * ((Encoding.frame key ++ words (pre ++ vertex :: rest)).length + 1),
      ∃ rf, Eval selectCall n
        (state regs c (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
          (List.replicate pre.length true) [] [] [] [] [])
        (state rf c [] key [] vertex [] [] [] []) := by
  obtain ⟨n, hn, rf, ht⟩ := PackingBucketSelect.program_trace key vertex pre rest regs
  have he := eval_call_lifted PackingBucketSelect.program id selectPorts
    (state regs c (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
      (List.replicate pre.length true) [] [] [] [] [])
    Function.injective_id selectPorts_injective ht
  rw [embed_select, embed_select] at he
  exact ⟨n, hn, rf, he⟩

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

theorem parser_state (regs : Fin 8 → Bool) (c : Context)
    (tag present found : Bool) (keys payload : List Bool) :
    RecordPrograms.state ports (ready regs c) tag present found keys payload =
    ready (parserRegs regs tag present found) { c with keys := keys, payload := payload } := by
  apply MatrixProgramSupport.data_ext <;> try rfl
  funext j
  fin_cases j <;> simp [ready, state, RecordPrograms.state, ports]

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

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

omit [DecidableEq V] in
theorem typedEntries_valid (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) :
    ∀ e ∈ typedEntries P encodeVertex encodeType, P.blockCount ≤ e.2.length := by
  intro e he
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp he
  simpa using P.blockCount_le_bucket u

omit [DecidableEq V] in
theorem coverVertices_typed (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) :
    coverVertices (typedEntries P encodeVertex encodeType) P.blockCount 0 =
      (PackingReorder.packedVertices P).map encodeVertex := by
  unfold coverVertices
  rw [← List.range_eq_range', ← List.map_coe_finRange]
  simp only [List.flatMap_map, typedEntries, List.map_map,
    PackingReorder.packedVertices, List.map_flatMap]
  apply congrArg (fun f => (List.finRange P.blockCount).flatMap f)
  funext i
  apply List.map_congr_left
  intro u _
  exact entryVertex_typed P encodeVertex encodeType i u

omit [DecidableEq V] in
theorem typed_extraction_storage (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (c : Context) :
    (advanceMany (typedEntries P encodeVertex encodeType) P.blockCount 0 c).storage =
      (vertexPrefix ((PackingReorder.packedVertices P).map encodeVertex)).reverse ++ c.storage := by
  rw [advanceMany_storage, coverVertices_typed]

omit [DecidableEq V] in
/-- Exact address bytes emitted by complete-block extraction, retaining the
initial table and allowing a nonzero initial storage address. -/
theorem typed_extraction_addresses (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (advanceMany (typedEntries P encodeVertex encodeType) P.blockCount 0 c).addresses =
      SelectorProgram.rawRecords
        (PackingAddressSemantics.addressRows
          ((PackingReorder.packedVertices P).map encodeVertex) a).reverse ++ c.addresses := by
  rw [advanceMany_addresses _ _ _ _ a ha, coverVertices_typed]

end SubexponentialSAT.Subexp.PackingExtraction

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

theorem clearVertex_eval (regs : Fin 8 → Bool)
    (covered source rank address storage metadata addresses vertex : List Bool) :
    Eval clearVertex (2*vertex.length+3)
      (data regs [] [] covered source [] rank address storage metadata addresses vertex)
      (data (readRegs regs 0 1 none) [] [] covered source [] rank address storage metadata addresses []) := by
  let a := data regs [] [] covered source [] rank address storage metadata addresses vertex
  have h := TupleProgram.clear_eval (15 : Fin 18) (0 : Fin 8) 1 a
  have he : (⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks 15 a.stacks⟩ : Data) =
      data (readRegs regs 0 1 none) [] [] covered source [] rank address storage metadata addresses [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [a,data,StackRoutines.clearStacks]
  rw [he] at h
  exact h

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

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem metadataRecords_leftovers (P : PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) :
    PackingLeftovers.metadataRecords 0 (P.leftovers.map code) =
      P.leftovers.map (PackingMetadata.row P (vertexBytes code) encodeType) := by
  rw [metadataRecords_eq_addressRows]
  rw [List.map_map]
  change (PackingAddressSemantics.addressRows (P.leftovers.map (vertexBytes code)) 0).map _ = _
  rw [PackingAddressSemantics.addressRows_map_graph P.leftovers (vertexBytes code)
    P.leftovers_nodup, List.map_map]
  apply List.map_congr_left
  intro v hv
  have hn : P.lookup v = none := (P.lookup_none_iff v).mpr ((P.mem_leftovers v).mp hv)
  simp [ PackingMetadata.row, PackingMetadata.value, hn,
    PackingLeftoverEmitter.metadataPayload, GlobalBasisMetadata.Metadata.encode,
    PackingMetadata.unary]

end SubexponentialSAT.Subexp.PackingOutputSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev emit : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks)

local infixr:60 " ;; " => Cmd.seq

abbrev callback : Cmd 8 16 :=
  copyIndex ;; lookup false ;; copyIndex ;; lookup true ;; equality ;; markDifferent ;; emit

abbrev reverseCall : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStacks)

abbrev command : Cmd 8 16 :=
  initializeList 13 ;; RecordPrograms.iterate ports callback ;; initializeList 14 ;; reverseCall

abbrev program : Program 8 16 (size command + 1) := compiled command 8 14

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

open BitProgram StructuredCalls StackRoutines
open MismatchPlanProgram (indexRecords )

abbrev filterCall : Cmd 10 17 := .call (ProgramLinking.liftProgram
  MismatchPlanProgram.program filterRegs filterStacks)

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod


namespace Native

def numeratorBudget {r Q : ℕ} (A R W P : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  ∑ node : Fin Q, LayoutProgram.Numerator.budget A R W P node u y


def tableBudget {r Q : ℕ} (A R W P t d : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  Q * (callbackBudget (numeratorBudget A R W P u y) (integerBits R W P) t d +
    6 * (d * SubexpLiftRing.baseWidth 3 t) + 16) + 14

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete packed source dispatch from actual metadata. All possible
branches execute native commands and return an exact typed compiler source. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking IntegerRingLiftProgram RowSelectionProgram

variable {r Q d D : ℕ}

def metadataRecords (P : PackingData (Fin D) (UniversalType r Q 1)) :=
  PackingMetadata.records P (fun v=>List.replicate v.val true) CollisionProgram.encodeType

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev Data := State 16 768

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end


