-- Prove2me | Definitions.Def_OAIQ081S124
-- name    : OAIQ081S124
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:37:06.423839+00:00
-- url     : https://prove2.me/theorems/b1c07cf2-f025-4436-b55a-c8d1bb6c6776
-- title:
--   Definitions bundle OAIQ081S124 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 19 definitions and 7 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.inverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.storage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanup`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.budget`, `OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.Code`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.buckets`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.bucketsCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.extraction`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.extractionCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.inverse`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.inverseCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.leftovers`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.leftoversCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.queriesCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.vertices`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.verticesCall`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPackLabels.lean), [`SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceBank.lean), [`SubexponentialSAT_Subexp_AssignmentSeedRange`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/AssignmentSeedRange.lean), [`SubexponentialSAT_Subexp_BasisTransposePlanProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/BasisTransposePlanProgram.lean), [`SubexponentialSAT_Subexp_PackingBucketExecution`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PackingBucketExecution.lean), [`SubexponentialSAT_Subexp_PackingBucketFold`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PackingBucketFold.lean), [`SubexponentialSAT_Subexp_PackingEntryEmitter`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PackingEntryEmitter.lean), [`SubexponentialSAT_Subexp_PackingProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PackingProgram.lean), [`SubexponentialSAT_Subexp_PackingProgramAuxiliary`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PackingProgramAuxiliary.lean), [`SubexponentialSAT_Subexp_SelectorMapProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/SelectorMapProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102` and `OAIQ081S106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S147` and `OAIQ081S148`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106

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

set_option maxHeartbeats 1600000 in
theorem callback_eval (records : List (List Bool × List Bool)) (query : List Bool)
    (regs : Fin 8 → Bool) (cursor acc : List Bool) :
    ∃ n ≤ callbackCost records query, ∃ regs',
      (∀ j : Fin 3, regs' (Fin.natAdd 5 j) = regs (Fin.natAdd 5 j)) ∧
      Eval callback n
        (state regs [] [] query.reverse [] [] [] cursor (SelectorProgram.rawRecords records) acc)
        (state regs' [] [] [] [] [] [] cursor (SelectorProgram.rawRecords records)
          (TupleProgram.prependRecord (selected records query) acc)) := by
  let a := state regs [] [] query.reverse [] [] [] cursor (SelectorProgram.rawRecords records) acc
  let copied := state (readRegs regs 0 1 none) (SelectorProgram.rawRecords records)
    [] query.reverse [] [] [] cursor (SelectorProgram.rawRecords records) acc
  have hcopy : Eval (.call (StackRoutines.copyProgram 7 0 4 (0 : Fin 8) 1))
      (7 * (SelectorProgram.rawRecords records).length + 5) a copied := by
    have hc : (⟨readRegs a.regs 0 1 none,
        StackRoutines.copyStacks 7 0 a.stacks⟩ : Data) = copied := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        fin_cases j <;> simp [a, state, StackRoutines.copyStacks]
    have h := TupleProgram.copy_eval (7 : Fin 9) 0 4 (0 : Fin 8) 1
      (by decide) (by decide) (by decide) (by decide) a (by rfl)
    rw [hc] at h
    exact h
  obtain ⟨ns, hns, localRegs, tail, htail, hselect⟩ :=
    selector_eval records query (readRegs regs 0 1 none) cursor
      (SelectorProgram.rawRecords records) acc
  let c := state (mergeRegs (readRegs regs 0 1 none) localRegs) tail
    (selected records query).reverse query.reverse [] [] [] cursor
      (SelectorProgram.rawRecords records) acc
  let d : Data := ⟨readRegs c.regs 0 1 none, StackRoutines.clearStacks 0 c.stacks⟩
  let e : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 2 d.stacks⟩
  let f := TupleProgram.pushedState 8 0 false e
  let g := TupleProgram.escapedState emitPorts f
  let h := TupleProgram.pushedState 8 0 true g
  have h1 := TupleProgram.clear_eval (0 : Fin 9) (0 : Fin 8) 1 c
  have h2 := TupleProgram.clear_eval (2 : Fin 9) (0 : Fin 8) 1 d
  have h3 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) false e
  have h4 := TupleProgram.escape_eval_state emitPorts f
  have h5 := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) true g
  have hrun := hcopy.seq (hselect.seq (h1.seq (h2.seq (h3.seq (h4.seq h5)))))
  have hh : h = state h.regs [] [] [] [] [] [] cursor (SelectorProgram.rawRecords records)
      (TupleProgram.prependRecord (selected records query) acc) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [ g, f, e, d, c, state, emitPorts, StackRoutines.clearStacks, TupleProgram.prependRecord,
          TupleProgram.frame_eq_escaped, List.append_assoc]
  refine ⟨(7 * (SelectorProgram.rawRecords records).length + 5) +
      (ns + ((2 * tail.length + 3) + ((2 * query.length + 3) +
        (2 + ((5 * (selected records query).length + 3) + 2))))), ?_, h.regs, ?_, ?_⟩
  · dsimp [callbackCost]
    omega
  · intro j
    fin_cases j <;>
      simp [h, g, f, e, d, c, state, emitPorts, mergeRegs, readRegs ]
  · rw [← hh]
    convert hrun using 1 ;
      simp [ c, d, e, f, state, emitPorts,
        StackRoutines.clearStacks ]

theorem callback_contract (records : List (List Bool × List Bool)) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records) (invariant records)
      (fun query a b => b.stacks 8 =
        TupleProgram.prependRecord (selected records query) (a.stacks 8)) := by
  intro query tail base hb
  let a := RecordPrograms.state ports base false true false tail query.reverse
  have ha : a = state a.regs [] [] query.reverse [] [] [] tail
      (SelectorProgram.rawRecords records) (base.stacks 8) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      rcases hb with ⟨h0, h1, h3, h4, h5, h7⟩
      fin_cases j <;> simp [ ports, h0, h1, h3, h4, h5, h7]
  obtain ⟨n, hn, regs', hr, he⟩ := callback_eval records query a.regs tail (base.stacks 8)
  let b := state regs' [] [] [] [] [] [] tail (SelectorProgram.rawRecords records)
    (TupleProgram.prependRecord (selected records query) (base.stacks 8))
  have hb' : RecordPrograms.state ports b false true false tail [] = b := by
    apply RecordPrograms.state_eq_self
    · simpa [b, state, a, ports, RecordPrograms.state] using hr 0
    · simpa [b, state, a, ports, RecordPrograms.state] using hr 1
    · simpa [b, state, a, ports, RecordPrograms.state] using hr 2
    · rfl
    · rfl
  refine ⟨n, b, hn, ?_, ?_, ?_⟩
  · simp [invariant, b, state]
  · rfl
  · rw [hb']
    simpa only [a, ← ha, b] using he

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured execution of the physical all-key packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

set_option maxHeartbeats 1600000 in
theorem callback_eval (records : List BucketProgram.Record) (query tail acc : List Bool)
    (m : ℕ) (hm : m ≤ records.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ callbackCost records query, ∃ rf,
      Eval callback n
        (state regs [] query.reverse [] (BucketProgram.encodeRecords records.reverse)
          tail [] (List.replicate m true) acc [] [])
        (state (finishRegs rf) [] [] [] (BucketProgram.encodeRecords records.reverse)
          tail [] (List.replicate (min m (BucketProgram.selected records query).length) true)
          (afterBucket records query acc) [] []) := by
  let items := BucketProgram.selected records query
  let bytes := words items
  let saved := BucketProgram.encodeRecords records.reverse
  let k := min m items.length
  let record := bucketPayload records query
  let recordBits := true :: Encoding.frame record
  obtain ⟨d1, h1, hs1⟩ := MatrixProgramSupport.copy_eval (6 : Fin 15) 0 12
    (by decide) (by decide) (by decide)
    (state regs [] query.reverse [] saved tail [] (List.replicate m true) acc [] []) rfl
  have hd1 : d1 = state d1.regs saved query.reverse [] saved tail []
      (List.replicate m true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs1]
    funext j
    fin_cases j <;> simp [state, StackRoutines.copyStacks]
  rw [hd1] at h1
  obtain ⟨n2, hn2, r2, h2⟩ := bucketCall_eval records query d1.regs
    saved tail [] (List.replicate m true) acc [] []
  change Eval bucketCall n2
    (state d1.regs saved query.reverse [] saved tail [] (List.replicate m true) acc [] [])
    (state r2 [] query.reverse bytes saved tail [] (List.replicate m true) acc [] []) at h2
  obtain ⟨d3, h3, hs3⟩ := MatrixProgramSupport.copy_eval (5 : Fin 15) 9 12
    (by decide) (by decide) (by decide)
    (state r2 [] query.reverse bytes saved tail [] (List.replicate m true) acc [] []) rfl
  have hd3 : d3 = state d3.regs [] query.reverse bytes saved tail bytes
      (List.replicate m true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs3]
    funext j
    fin_cases j <;> simp [state, StackRoutines.copyStacks]
  rw [hd3] at h3
  obtain ⟨n4, hn4, r4, h4⟩ := countCall_eval items d3.regs
    [] query.reverse bytes saved tail (List.replicate m true) acc []
  obtain ⟨n5, hn5, r5, h5⟩ := minimumCall_eval m items.length r4
    [] query.reverse bytes saved tail [] acc
  obtain ⟨d6, h6, hs6⟩ := move_eval (14 : Fin 15) 10 12
    (by decide) (by decide) (by decide)
    (state r5 [] query.reverse bytes saved tail [] [] acc [] (List.replicate k true)) rfl rfl
  have hd6 : d6 = state d6.regs [] query.reverse bytes saved tail []
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs6]
    funext j
    fin_cases j <;> simp [state]
  rw [hd6] at h6
  obtain ⟨d7, h7, hs7⟩ := transfer_eval (2 : Fin 15) 9 (by decide)
    (state d6.regs [] query.reverse bytes saved tail [] (List.replicate k true) acc [] [])
  have hd7 : d7 = state d7.regs [] [] bytes saved tail query
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs7]
    funext j
    fin_cases j <;> simp [state, StackRoutines.transferStacks]
  rw [hd7] at h7
  obtain ⟨d8, h8, hs8⟩ := emitFrame_eval (9 : Fin 15) 5 12
    (by decide) (by decide) (by decide)
    (state d7.regs [] [] bytes saved tail query (List.replicate k true) acc [] []) rfl
  have hd8 : d8 = state d8.regs [] [] record saved tail []
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs8]
    funext j
    fin_cases j <;> simp [state, record, bucketPayload, bytes, items]
  rw [hd8] at h8
  obtain ⟨d9, h9, hs9⟩ := emitFrame_eval (5 : Fin 15) 9 12
    (by decide) (by decide) (by decide)
    (state d8.regs [] [] record saved tail [] (List.replicate k true) acc [] []) rfl
  have hd9 : d9 = state d9.regs [] [] [] saved tail (Encoding.frame record)
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs9]
    funext j
    fin_cases j <;> simp [state]
  rw [hd9] at h9
  let r10 := Function.update d9.regs (0 : Fin 8) true
  have h10 : Eval (TupleProgram.pushConst 9 0 true) 2
      (state d9.regs [] [] [] saved tail (Encoding.frame record) (List.replicate k true) acc [] [])
      (state r10 [] [] [] saved tail recordBits (List.replicate k true) acc [] []) := by
    have ht := TupleProgram.pushConst_eval (9 : Fin 15) (0 : Fin 8) true
      (state d9.regs [] [] [] saved tail (Encoding.frame record) (List.replicate k true) acc [] [])
    have hf : TupleProgram.pushedState 9 0 true
        (state d9.regs [] [] [] saved tail (Encoding.frame record) (List.replicate k true) acc [] []) =
        state r10 [] [] [] saved tail recordBits (List.replicate k true) acc [] [] := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext j
      fin_cases j <;> rfl
    rw [hf] at ht
    exact ht
  obtain ⟨d11, h11, hs11⟩ := transfer_eval (9 : Fin 15) 11 (by decide)
    (state r10 [] [] [] saved tail recordBits (List.replicate k true) acc [] [])
  have hd11 : d11 = state d11.regs [] [] [] saved tail []
      (List.replicate k true) (recordBits.reverse ++ acc) [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs11]
    funext j
    fin_cases j <;> simp [state, StackRoutines.transferStacks]
  rw [hd11] at h11
  have h12 : Eval (sequence [.base (.atom (.set 5 false)),
      .base (.atom (.set 6 true)), .base (.atom (.set 7 false))]) 3
      (state d11.regs [] [] [] saved tail [] (List.replicate k true) (recordBits.reverse ++ acc) [] [])
      (state (finishRegs d11.regs) [] [] [] saved tail []
        (List.replicate k true) (recordBits.reverse ++ acc) [] []) := by
    exact (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq
      ((Eval.base (.atom _ _)).seq (Eval.base (.skip _))))
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq
    (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq h12))))))))))
  let total := (7 * saved.length + 5) + (n2 + ((7 * bytes.length + 5) +
    (n4 + (n5 + ((6 * k + 6) + ((3 * query.length + 3) + ((8 * query.length + 8) +
      ((8 * record.length + 8) + (2 + ((3 * recordBits.length + 3) + 3))))))))))
  refine ⟨total, ?_, d11.regs, ?_⟩
  · have hlen := BucketProgram.record_count_le_length records
    have hnlen := (selected_length_le records query).trans hlen
    have hblen := selected_words_length_le records query
    have hb := BucketProgram.loopBudget_le records.reverse query
    rw [encodeRecords_length_reverse, List.length_reverse] at hb
    have hmul := Nat.mul_le_mul_right (9 * query.length + 20) hlen
    have hscan : n2 ≤ 9 * (BucketProgram.encodeRecords records).length +
        (BucketProgram.encodeRecords records).length * (9 * query.length + 20) + 3 := by
      omega
    have hbound := callback_arithmetic (BucketProgram.encodeRecords records).length
      query.length m items.length bytes.length n2 (hm.trans hlen) hnlen hblen hscan
    have hrecord : record.length = 2 * query.length + 1 + bytes.length := by
      simp [record, bucketPayload, bytes, items, Encoding.length_frame]
    have hrecordBits : recordBits.length = 2 * record.length + 2 := by
      simp only [recordBits, List.length_cons, Encoding.length_frame]
    dsimp only [callbackCost, total, k]
    simp only [show saved.length = (BucketProgram.encodeRecords records).length from
      encodeRecords_length_reverse records, hrecordBits, hrecord]
    dsimp only [bytes, items] at hn4 hn5 hbound ⊢
    omega
  · simpa [callback, sequence, total, state, saved, k, recordBits, record,
      afterBucket, bytes, items, List.length_replicate, Encoding.length_frame] using he

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual all-type scan and minimum fold, preserving the supplied type order. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

theorem callback_contract (records : List BucketProgram.Record) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records) (invariant records) (effect records) := by
  intro query tail base hb
  obtain ⟨n, hn, rf, he⟩ := callback_eval records query tail (base.stacks 11)
    (base.stacks 10).length hb.2 (parserRegs base.regs false true false)
  let next := state (finishRegs rf) [] [] [] (BucketProgram.encodeRecords records.reverse)
    tail [] (List.replicate (min (base.stacks 10).length
      (BucketProgram.selected records query).length) true)
    (afterBucket records query (base.stacks 11)) [] []
  have hinput : RecordPrograms.state ports base false true false tail query.reverse =
      state (parserRegs base.regs false true false) [] query.reverse []
        (BucketProgram.encodeRecords records.reverse) tail []
        (List.replicate (base.stacks 10).length true) (base.stacks 11) [] [] := by
    calc
      _ = RecordPrograms.state ports
          (state base.regs [] (base.stacks 2) [] (BucketProgram.encodeRecords records.reverse)
            (base.stacks 7) [] (List.replicate (base.stacks 10).length true)
            (base.stacks 11) [] []) false true false tail query.reverse :=
        congrArg (fun a => RecordPrograms.state ports a false true false tail query.reverse) hb.1
      _ = _ := parser_state ..
  have houtput : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self <;> simp [next, ports, state, finishRegs]
  refine ⟨n, next, hn, ?_, ?_, ?_⟩
  · exact invariant_state records (finishRegs rf) [] tail _ _
      ((min_le_left _ _).trans hb.2)
  · simp [effect, next, state]
  · rw [hinput, houtput]
    exact he

/-- The real iterator calls the filter, frame counter and unary minimum routine
for every key. The output table has precisely the original key order. -/
theorem program_trace (records : List BucketProgram.Record) (keys : List (List Bool))
    (initial : ℕ) (hinitial : initial ≤ records.length) (suffix : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ budget records keys, ∃ rf,
      Trace program n
        ((inputState records keys initial suffix regs).withPC (some program.entry))
        ((outputState records keys initial suffix rf).withPC none) := by
  let a := inputState records keys initial suffix regs
  have ha : invariant records a := invariant_state records regs [] _ [] initial hinitial
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false) (callbackCost records)
      (invariant records) (effect records) (callback_contract records)
      keys suffix a ha (a.regs 5) (a.regs 6) (a.regs 7)
  have hstart : RecordPrograms.state ports a (a.regs 5) (a.regs 6) (a.regs 7)
      (Encoding.encodeList id keys ++ suffix) [] = a := by
    apply RecordPrograms.state_eq_self <;> simp [ports, a, inputState, state,
      ProgramEncoding.encodeRecords]
  have hminimum : (next.stacks 10).length = minimum records keys initial := by
    have h := history.fold_of_false (fun _ _ => rfl) (fun d => (d.stacks 10).length)
      (fun m key => min m (BucketProgram.selected records key).length)
      (fun _ _ _ h => h.1)
    simpa [minimum, a, inputState, state] using h
  have htable : next.stacks 11 = (recordPrefix records keys).reverse := by
    have h := history.fold_of_false (fun _ _ => rfl) (fun d => d.stacks 11)
      (fun acc key => afterBucket records key acc) (fun _ _ _ h => h.2)
    rw [fold_afterBucket] at h
    simpa [a, inputState, state] using h
  let b := state (parserRegs next.regs false true false) [] [] []
    (BucketProgram.encodeRecords records.reverse) suffix []
    (List.replicate (minimum records keys initial) true) (recordPrefix records keys).reverse [] []
  have hend : RecordPrograms.state ports next false true false suffix [] = b := by
    calc
      _ = RecordPrograms.state ports
          (state next.regs [] (next.stacks 2) [] (BucketProgram.encodeRecords records.reverse)
            (next.stacks 7) [] (List.replicate (next.stacks 10).length true)
            (next.stacks 11) [] []) false true false suffix [] :=
        congrArg (fun d => RecordPrograms.state ports d false true false suffix []) hnext.1
      _ = b := by rw [parser_state, hminimum, htable]
  have hiter' : Eval (RecordPrograms.iterate ports callback) n a b := by
    have hany : keys.any (fun _ => false) = false := by simp
    simpa only [hstart, hany, TupleProgram.unread_false, hend] using hiter
  let c := TupleProgram.pushedState (11 : Fin 15) (0 : Fin 8) false b
  have hpush := TupleProgram.pushConst_eval (11 : Fin 15) (0 : Fin 8) false b
  obtain ⟨d, htransfer, hd⟩ := transfer_eval (11 : Fin 15) 5 (by decide) c
  have houtput : d = outputState records keys initial suffix d.regs := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hd]
    funext i
    fin_cases i <;>
      simp [outputState, b, c, state,
        StackRoutines.transferStacks, List.reverse_cons, encodeTable_eq_prefix]
  have hlength : (c.stacks 11).length =
      (ProgramEncoding.encodeRecords (table records keys)).length := by
    simp [c, b, state, encodeTable_eq_prefix]
  have hrun := compiled_halt_trace (hiter'.seq (hpush.seq htransfer)) (7 : Fin 15) 5
  refine ⟨n + (2 + (3 * (c.stacks 11).length + 3)) + 1, ?_, d.regs, ?_⟩
  · rw [hlength]
    dsimp [budget]
    omega
  · rw [houtput] at hrun
    simpa only [command, program, a] using hrun

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramAuxiliary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Independent fixed bucket and inverse-address stages. -/
namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

abbrev bucketsCall : Cmd 16 48 := lowCall PackingBucketTable.program (by decide) (by decide)
abbrev queriesCall : Cmd 16 48 := lowCall SubexpVertexIndexProgram.program (by decide) (by decide)
abbrev inverseCall : Cmd 16 48 := lowCall SelectorMapProgram.program (by decide) (by decide)

abbrev buckets : Cmd 16 48 := .seq (PackingPlumbing.command bucketsSetup)
  (.seq bucketsCall (PackingPlumbing.command bucketsSave))
abbrev inverse : Cmd 16 48 := .seq (PackingPlumbing.command queriesSetup)
  (.seq queriesCall (.seq (PackingPlumbing.command queriesSave)
    (.seq inverseCall (PackingPlumbing.command inverseSave))))


end SubexponentialSAT.Subexp.PackingProgram

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

theorem command_eval_exact
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (commandCost vertex typeBytes block address)
      (state regs vertex typeBytes block address storage metadata addresses)
      (state rf [] [] block (true::address) (storageOutput vertex storage)
        (metadataOutput vertex typeBytes block metadata)
        (addressOutput vertex address addresses)) := by
  let a0 := workState regs vertex typeBytes block address storage metadata addresses [] [] []
  obtain ⟨d1,h1,s1⟩ := copy_eval (0 : Fin 10) 8 7 (by decide) (by decide) (by decide) a0 rfl
  let a1 := workState d1.regs
    vertex typeBytes block address storage metadata addresses [] vertex []
  have e1 : d1 = a1 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s1]
    funext j
    fin_cases j <;> simp [a0,workState,StackRoutines.copyStacks]
  rw [e1] at h1
  obtain ⟨d2,h2,s2⟩ := emitFrame_eval (8 : Fin 10) 9 7 (by decide) (by decide) (by decide) a1 rfl
  let a2 := workState d2.regs
    vertex typeBytes block address storage metadata addresses [] [] (Encoding.frame vertex)
  have e2 : d2 = a2 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s2]
    funext j
    fin_cases j <;> simp [a1,workState]
  rw [e2] at h2
  have h3 := TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) true a2
  let a3 := workState (Function.update a2.regs 0 true)
    vertex typeBytes block address storage metadata addresses [] [] (true :: (Encoding.frame vertex))
  have e3 : TupleProgram.pushedState 9 0 true a2 = a3 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a2,workState]
  rw [e3] at h3
  obtain ⟨d4,h4,s4⟩ := transfer_eval (9 : Fin 10) 4 (by decide) a3
  let a4 := workState d4.regs
    vertex typeBytes block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] []
  have e4 : d4 = a4 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s4]
    funext j
    fin_cases j <;> simp [a3,workState,StackRoutines.transferStacks]
  rw [e4] at h4
  obtain ⟨d5,h5,s5⟩ := emitFrame_eval (1 : Fin 10) 8 7 (by decide) (by decide) (by decide) a4 rfl
  let a5 := workState d5.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (Encoding.frame typeBytes) []
  have e5 : d5 = a5 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s5]
    funext j
    fin_cases j <;> simp [a4,workState]
  rw [e5] at h5
  obtain ⟨d6,h6,s6⟩ := copy_eval (2 : Fin 10) 9 7 (by decide) (by decide) (by decide) a5 rfl
  let a6 := workState d6.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (Encoding.frame typeBytes) block
  have e6 : d6 = a6 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s6]
    funext j
    fin_cases j <;> simp [a5,workState,StackRoutines.copyStacks]
  rw [e6] at h6
  obtain ⟨d7,h7,s7⟩ := emitFrame_eval (9 : Fin 10) 8 7 (by decide) (by decide) (by decide) a6 rfl
  let a7 := workState d7.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (Encoding.frame block ++ (Encoding.frame typeBytes)) []
  have e7 : d7 = a7 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s7]
    funext j
    fin_cases j <;> simp [a6,workState]
  rw [e7] at h7
  have h8 := TupleProgram.pushConst_eval (8 : Fin 10) (0 : Fin 8) true a7
  let a8 := workState (Function.update a7.regs 0 true)
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) []
  have e8 : TupleProgram.pushedState 8 0 true a7 = a8 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a7,workState]
  rw [e8] at h8
  obtain ⟨d9,h9,s9⟩ := emitFrame_eval (8 : Fin 10) 5 7 (by decide) (by decide) (by decide) a8 rfl
  let a9 := workState d9.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata) addresses [] [] []
  have e9 : d9 = a9 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s9]
    funext j
    fin_cases j <;> simp [a8,workState]
  rw [e9] at h9
  obtain ⟨d10,h10,s10⟩ := copy_eval (0 : Fin 10) 9 7 (by decide) (by decide) (by decide) a9 rfl
  let a10 := workState d10.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata) addresses [] [] vertex
  have e10 : d10 = a10 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s10]
    funext j
    fin_cases j <;> simp [a9,workState,StackRoutines.copyStacks]
  rw [e10] at h10
  obtain ⟨d11,h11,s11⟩ := emitFrame_eval (9 : Fin 10) 5 7 (by decide) (by decide) (by decide) a10 rfl
  let a11 := workState d11.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) addresses [] [] []
  have e11 : d11 = a11 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s11]
    funext j
    fin_cases j <;> simp [a10,workState]
  rw [e11] at h11
  obtain ⟨d12,h12,s12⟩ := copy_eval (3 : Fin 10) 8 7 (by decide) (by decide) (by decide) a11 rfl
  let a12 := workState d12.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) addresses [] address []
  have e12 : d12 = a12 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s12]
    funext j
    fin_cases j <;> simp [a11,workState,StackRoutines.copyStacks]
  rw [e12] at h12
  obtain ⟨d13,h13,s13⟩ := emitFrame_eval (8 : Fin 10) 6 7 (by decide) (by decide) (by decide) a12 rfl
  let a13 := workState d13.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) (Encoding.frame address ++ addresses) [] [] []
  have e13 : d13 = a13 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s13]
    funext j
    fin_cases j <;> simp [a12,workState]
  rw [e13] at h13
  obtain ⟨d14,h14,s14⟩ := emitFrame_eval (0 : Fin 10) 6 7 (by decide) (by decide) (by decide) a13 rfl
  let a14 := workState d14.regs
    [] [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e14 : d14 = a14 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s14]
    funext j
    fin_cases j <;> simp [a13,workState]
  rw [e14] at h14
  have h15 := TupleProgram.pushConst_eval (3 : Fin 10) (0 : Fin 8) true a14
  let a15 := workState (Function.update a14.regs 0 true)
    [] [] block (true :: address) ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e15 : TupleProgram.pushedState 3 0 true a14 = a15 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a14,workState]
  rw [e15] at h15
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq ((.base (.skip a15)))))))))))))))))
  have hcost : (7*(a0.stacks 0).length+5)+((8*(a1.stacks 8).length+8)+(2+((3*(a3.stacks 9).length+3)+((8*(a4.stacks 1).length+8)+((7*(a5.stacks 2).length+5)+((8*(a6.stacks 9).length+8)+(2+((8*(a8.stacks 8).length+8)+((7*(a9.stacks 0).length+5)+((8*(a10.stacks 9).length+8)+((7*(a11.stacks 3).length+5)+((8*(a12.stacks 8).length+8)+((8*(a13.stacks 0).length+8)+(2+(0))))))))))))))) =
      commandCost vertex typeBytes block address := by
    simp [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,workState,commandCost,Encoding.length_frame]
    ring
  rw [hcost] at hrun
  exact ⟨a15.regs,hrun⟩

theorem program_trace
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (commandCost vertex typeBytes block address+1)
      ((state regs vertex typeBytes block address storage metadata addresses).withPC (some program.entry))
      ((state rf [] [] block (true::address) (storageOutput vertex storage)
        (metadataOutput vertex typeBytes block metadata)
        (addressOutput vertex address addresses)).withPC none) := by
  obtain ⟨rf,h⟩ := command_eval_exact vertex typeBytes block address storage metadata addresses regs
  exact ⟨rf,compiled_halt_trace h 0 4⟩

end SubexponentialSAT.Subexp.PackingEntryEmitter


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

def budget (n : ℕ) : ℕ := DimensionProgram.loopCost 0 n +
  10 * (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)).length + 2 * n + 13

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed physical packing controller. Every alphabet, bucket, selected
vertex, leftover, and inverse-address query is produced by actual programs. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

abbrev extractionCall : Cmd 16 48 := lowCall PackingExtraction.program (by decide) (by decide)
abbrev verticesCall : Cmd 16 48 := lowCall AssignmentSeedRange.program (by decide) (by decide)
abbrev leftoversCall : Cmd 16 48 := lowCall PackingLeftovers.program (by decide) (by decide)
abbrev extraction : Cmd 16 48 := .seq extractionCall (PackingPlumbing.command extractionSave)
abbrev vertices : Cmd 16 48 := .seq (PackingPlumbing.command verticesSetup)
  (.seq verticesCall (PackingPlumbing.command verticesSave))
abbrev leftovers : Cmd 16 48 := .seq leftoversCall (PackingPlumbing.command leftoversSave)

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPackLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Spec

variable {U : Type*} [DecidableEq U]

def storage (s : Spec U) : List Bool :=
  ProgramEncoding.encodeRecords ((PackingReorder.storageVertices s.packing).map s.encodeVertex)

def inverse (s : Spec U) : List Bool :=
  ProgramEncoding.encodeRecords ((PackingReorder.readPlan s.packing).map PackingMetadata.unary)

end Spec

variable {U : Type*} [DecidableEq U]


abbrev command : Cmd 16 48 :=
  .seq PackingProgram.buckets (.seq PackingProgram.extraction
    (.seq PackingProgram.vertices (.seq PackingProgram.leftovers
      (.seq PackingProgram.inverse (.base .skip)))))
def program := compiled command 26 32

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical transpose read-plan generation

Two unary countdowns visit columns and rows in decreasing order. Each visit
constructs the unary physical index by repeated copying and emits one actual
framed record. Prepending these visits produces the increasing transpose
read order directly. All counters are runtime stacks and the code is fixed.
-/

namespace SubexponentialSAT.Subexp.BasisTransposePlanProgram

open BitProgram StructuredCalls

abbrev Code := Cmd 3 7

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Code := Cmd 16 320

def cleanup : Code := Staging.sequence 0 1 319 cleanupOps

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end


