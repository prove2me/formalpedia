-- Prove2me | Definitions.Def_OAIQ081S074
-- name    : OAIQ081S074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:58:47.421889+00:00
-- url     : https://prove2.me/theorems/692f5216-7c1c-4405-aa67-9539e5c49545
-- title:
--   Definitions bundle OAIQ081S074 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 85 declarations of OpenAI's Lean: 52 definitions and 33 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.projectInner`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.dimProgram`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.dimensions`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.emitCurrent`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.enumerate`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.increment`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.loop`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.countCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketSelect.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketSelect.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketSelect.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.afterBucket`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.recordPrefix`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingCoveredQuery.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingCoveredQuery.core`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingCoveredQuery.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingEntryEmitter.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingEntryEmitter.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingEntryEmitter.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingEntryEmitter.workState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.blockCommand`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.body`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.coverRows`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.emitCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.loop`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.selectCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.body`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.increment`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.loop`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameSkip.finalState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverEmitter.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverEmitter.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftovers.callback` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_SubexpVertexIndexProgram`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_DimensionProgram`, `SubexponentialSAT_Subexp_MatrixProgramSupport`, `SubexponentialSAT_Subexp_PackingAddressSemantics`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingBucketExecution`, `SubexponentialSAT_Subexp_PackingBucketFold`, `SubexponentialSAT_Subexp_PackingBucketSelect`, `SubexponentialSAT_Subexp_PackingBucketSemantics`, `SubexponentialSAT_Subexp_PackingEntryEmitter`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionCallback`, `SubexponentialSAT_Subexp_PackingExtractionEmit`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingExtractionState`, `SubexponentialSAT_Subexp_PackingFrameCount`, `SubexponentialSAT_Subexp_PackingFrameSkip`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingOutputSemantics`, `SubexponentialSAT_Subexp_PackingReorder`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S021`, `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S051`, `OAIQ081S053`, `OAIQ081S056`, `OAIQ081S057` and `OAIQ081S060` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S089`, `OAIQ081S090` and `OAIQ081S091`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S021
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S056
import Definitions.Def_OAIQ081S057
import Definitions.Def_OAIQ081S060

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control selection of serialized coefficient records

The inner record body is `frame key ++ frame coefficient`. All execution
claims below are traces of fixed Boolean-register/stack instruction tables.
-/

namespace SubexponentialSAT.SubexpRecordScan

open BitProgram StructuredProgram StructuredCalls

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    StructuredCalls.embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [StructuredCalls.embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [StructuredCalls.embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [StructuredCalls.embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [StructuredCalls.embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

/-- Actual parser execution on arbitrary surrounding register/stack data. -/
theorem parseFrame_eval (d : Data) (src dst : Fin 6) (hsd : src ≠ dst)
    (bits rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    StructuredCalls.Eval (.call (parseFrame src dst)) (6 * bits.length + 4)
      d (afterFrame d src dst bits rest) := by
  let a : StructuredProgram.State 2 2 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : StructuredProgram.State 2 2 :=
    ⟨ParserProgram.pair false true,
      ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : StructuredCalls.embedState lowRegs (twoPorts src dst) d a = d := by
    apply embedState_eq _ _ lowRegs_injective (twoPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState lowRegs (twoPorts src dst) d b =
      afterFrame d src dst bits rest := by
    apply embedState_eq _ _ lowRegs_injective (twoPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame, lowRegs, readRegs, b, ParserProgram.pair]
    · intro i; fin_cases i <;>
        simp [afterFrame, twoPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [lowRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [lowRegs] using h.symm⟩
      simp [afterFrame, readRegs, h0, h1]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [twoPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [twoPorts] using h.symm⟩
      simp [afterFrame, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := StructuredCalls.eval_call_lifted ParserProgram.frameProgram lowRegs
    (twoPorts src dst) d lowRegs_injective (twoPorts_injective src dst hsd) ht
  simpa only [ha, hb, parseFrame] using h

theorem clear_eval (d : Data) (src : Fin 6) :
    StructuredCalls.Eval (.call (StackRoutines.clearProgram src (0 : Fin 5) 1))
      (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [afterClear, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

theorem skipPayload_eval (d : Data) (bits rest : List Bool)
    (hin : d.stacks 0 = Encoding.frame bits ++ rest) :
    StructuredCalls.Eval (.call skipPayload) (5 * bits.length + 4)
      d (afterSkip d rest) := by
  let a : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs (d.regs 0) (d.regs 1) (d.regs 4),
      fun _ => Encoding.frame bits ++ rest⟩
  let b : StructuredProgram.State 3 1 :=
    ⟨ExecCNFRecords.regs false true (d.regs 4), fun _ => rest⟩
  have ha : StructuredCalls.embedState skipRegs onlyInput d a = d := by
    apply embedState_eq _ _ skipRegs_injective onlyInput_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i; exact hin
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState skipRegs onlyInput d b = afterSkip d rest := by
    apply embedState_eq _ _ skipRegs_injective onlyInput_injective
    · intro i; fin_cases i <;>
        simp [afterSkip, skipRegs, ExecCNFRecords.ports, ExecCNFRecords.regs, readRegs, b]
    · intro i; fin_cases i; simp [afterSkip, onlyInput, b]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [skipRegs, ExecCNFRecords.ports] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [skipRegs, ExecCNFRecords.ports] using h.symm⟩
      simp [afterSkip, readRegs, h0, h1]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [onlyInput] using h.symm⟩
      simp [afterSkip, h0]
  have ht : Trace rawSkip (5 * bits.length + 4)
      (a.withPC (some rawSkip.entry)) (b.withPC none) :=
    ExecCNFRecords.frame_trace bits rest (d.regs 0) (d.regs 1) (d.regs 4)
  have h := StructuredCalls.eval_call_lifted rawSkip skipRegs onlyInput d
    skipRegs_injective onlyInput_injective ht
  simpa only [ha, hb, skipPayload] using h

theorem copyPayload_eval (d : Data) (bits rest : List Bool)
    (hin : d.stacks 0 = Encoding.frame bits ++ rest) (htmp : d.stacks 4 = []) :
    StructuredCalls.Eval (.call copyPayload) (13 * bits.length + 11)
      d (afterPayload d bits rest) := by
  let a : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ExecCNFRecords.ports (Encoding.frame bits ++ rest) (d.stacks 5) []⟩
  let b : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair false false,
      ExecCNFRecords.ports rest (Encoding.frame bits ++ d.stacks 5) []⟩
  have ha : StructuredCalls.embedState lowRegs payloadPorts d a = d := by
    apply embedState_eq _ _ lowRegs_injective payloadPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
      · exact htmp
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState lowRegs payloadPorts d b =
      afterPayload d bits rest := by
    apply embedState_eq _ _ lowRegs_injective payloadPorts_injective
    · intro i; fin_cases i <;> simp [afterPayload, lowRegs, readRegs, b, ParserProgram.pair]
    · intro i; fin_cases i <;>
        simp [afterPayload, payloadPorts, ExecCNFRecords.ports, b, htmp]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [lowRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [lowRegs] using h.symm⟩
      simp [afterPayload, readRegs, h0, h1]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [payloadPorts, ExecCNFRecords.ports] using h.symm⟩
      have h5 : j ≠ 5 := fun h => hj ⟨1, by simpa [payloadPorts, ExecCNFRecords.ports] using h.symm⟩
      simp [afterPayload, h0, h5]
  have ht : Trace rawCopy (13 * bits.length + 11)
      (a.withPC (some rawCopy.entry)) (b.withPC none) :=
    ExecCNFRecords.copy_frame_trace bits rest (d.stacks 5) (d.regs 0) (d.regs 1)
  have h := StructuredCalls.eval_call_lifted rawCopy lowRegs payloadPorts d
    lowRegs_injective payloadPorts_injective ht
  simpa only [ha, hb, copyPayload] using h

theorem selectPayload_eval (d : Data) (bits rest : List Bool)
    (hin : d.stacks 0 = Encoding.frame bits ++ rest) (htmp : d.stacks 4 = []) :
    ∃ n ≤ 13 * bits.length + 12,
      StructuredCalls.Eval selectPayload n d (selectedState d bits rest) := by
  cases h : d.regs 4 with
  | false =>
    refine ⟨5 * bits.length + 4 + 1, by omega, ?_⟩
    simpa only [selectPayload, selectedState, h, Bool.false_eq_true, ite_false] using
      StructuredCalls.Eval.ite_false h (skipPayload_eval d bits rest hin)
  | true =>
    refine ⟨13 * bits.length + 11 + 1, by omega, ?_⟩
    simpa only [selectPayload, selectedState, h, ite_true, if_true] using
      StructuredCalls.Eval.ite_true h (copyPayload_eval d bits rest hin htmp)

/-- Actual bit-string comparison, with preserved surrounding ports and
bounded leftover lengths for the following cleanup loops. -/
theorem compareKeys_eval (regs : Fin 5 → Bool)
    (input left query right tmp output : List Bool) :
    ∃ n ≤ 9 * (left.length + 1), ∃ regs' left' right',
      StructuredCalls.Eval (.call compareKeys) n
        (recordState regs input left query right tmp output)
        (recordState regs' input left' query right' tmp output) ∧
      regs' 4 = decide (left = right) ∧
      left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded regs left right
  let frame := recordState regs input left query right tmp output
  let a : StructuredProgram.State 5 2 := ⟨regs, ExecClauseCost.bitStacks left right⟩
  let b : StructuredProgram.State 5 2 := ⟨c.regs, c.stacks⟩
  have ha : StructuredCalls.embedState id (twoPorts 1 3) frame a = frame := by
    apply embedState_eq _ _ Function.injective_id (twoPorts_injective 1 3 (by decide))
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : StructuredCalls.embedState id (twoPorts 1 3) frame b =
      recordState c.regs input (c.stacks 0) query (c.stacks 1) tmp output := by
    apply embedState_eq _ _ Function.injective_id (twoPorts_injective 1 3 (by decide))
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intro j hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨0, by simpa [twoPorts] using h.symm⟩
      have h3 : j ≠ 3 := fun h => hj ⟨1, by simpa [twoPorts] using h.symm⟩
      simp [ storage, frame, h1, h3]
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [hcfg]
    exact ht
  have h := StructuredCalls.eval_call_lifted ExecClauseCost.bitEqualityProgram id
    (twoPorts 1 3) frame Function.injective_id (twoPorts_injective 1 3 (by decide)) ht'
  refine ⟨n, hn, c.regs, c.stacks 0, c.stacks 1, ?_, hout, hleft, hright⟩
  simpa only [ha, hb, compareKeys] using h

/-- One record is consumed; the query is restored; all three scratch ports
are empty; and the complete coefficient frame is selected exactly on key
equality. The Boolean result remains in register 4. -/
theorem oneRecord_eval (regs : Fin 5 → Bool)
    (key query payload tail output : List Bool) :
    ∃ n ≤ recordCost key query payload, ∃ regs',
      StructuredCalls.Eval oneRecord n
        (recordState regs (Encoding.frame key ++ (Encoding.frame payload ++ tail))
          [] query.reverse [] [] output)
        (recordState regs' tail [] query.reverse [] []
          (if key = query then Encoding.frame payload ++ output else output)) ∧
      regs' 4 = decide (key = query) := by
  let source := Encoding.frame payload ++ tail
  let r₁ := readRegs regs 0 1 (some false)
  let r₂ := readRegs r₁ 0 1 none
  have hp : StructuredCalls.Eval (.call (parseFrame 0 1)) (6 * key.length + 4)
      (recordState regs (Encoding.frame key ++ source) [] query.reverse [] [] output)
      (recordState r₁ source key.reverse query.reverse [] [] output) := by
    have h := parseFrame_eval
      (recordState regs (Encoding.frame key ++ source) [] query.reverse [] [] output)
      0 1 (by decide) key source rfl
    simpa [afterFrame, recordState, r₁] using h
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1)) (7 * query.length + 5)
      (recordState r₁ source key.reverse query.reverse [] [] output)
      (recordState r₂ source key.reverse query.reverse query.reverse [] output) := by
    have h := copy_eval
      (recordState r₁ source key.reverse query.reverse [] [] output)
      2 3 4 (by decide) (by decide) (by decide) rfl
    simpa [afterCopy, StackRoutines.copyStacks, recordState, r₂] using h
  obtain ⟨nc, hnc, rr, left, right, hcompare, hanswer, hleft, hright⟩ :=
    compareKeys_eval r₂ source key.reverse query.reverse query.reverse [] output
  simp only [List.length_reverse] at hnc hleft hright
  have hans : rr 4 = decide (key = query) := by
    simpa only [List.reverse_inj] using hanswer
  let r₃ := readRegs rr 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have hclear₁ : StructuredCalls.Eval
      (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1)) (2 * left.length + 3)
      (recordState rr source left query.reverse right [] output)
      (recordState r₃ source [] query.reverse right [] output) := by
    have h := clear_eval (recordState rr source left query.reverse right [] output) 1
    simpa [afterClear, StackRoutines.clearStacks, recordState, r₃] using h
  have hclear₃ : StructuredCalls.Eval
      (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1)) (2 * right.length + 3)
      (recordState r₃ source [] query.reverse right [] output)
      (recordState r₄ source [] query.reverse [] [] output) := by
    have h := clear_eval (recordState r₃ source [] query.reverse right [] output) 3
    simpa [afterClear, StackRoutines.clearStacks, recordState, r₄] using h
  let ready := recordState r₄ source [] query.reverse [] [] output
  have hflag : ready.regs 4 = decide (key = query) := by
    simpa [ready, recordState, r₄, r₃, readRegs, SqrtLog.LayoutOwnerFiberProgram.status] using hans
  obtain ⟨ns, hns, hselect⟩ := selectPayload_eval ready payload tail rfl rfl
  have hend : selectedState ready payload tail =
      recordState (selectedState ready payload tail).regs tail [] query.reverse [] []
        (if key = query then Encoding.frame payload ++ output else output) := by
    apply state_ext
    · rfl
    · by_cases heq : key = query
      · have htrue : ready.regs 4 = true := by simpa [heq] using hflag
        simp only [selectedState, htrue, ite_true, if_true]
        simp [afterPayload, ready, heq]
      · have hfalse : ready.regs 4 = false := by simpa [heq] using hflag
        simp only [selectedState, hfalse, Bool.false_eq_true, ite_false]
        simp [afterSkip, ready, heq]
  have hfinal : (selectedState ready payload tail).regs 4 = decide (key = query) := by
    unfold selectedState
    split <;> simpa [afterPayload, afterSkip, readRegs] using hflag
  rw [hend] at hselect
  refine ⟨(6 * key.length + 4) + ((7 * query.length + 5) +
    (nc + ((2 * left.length + 3) + ((2 * right.length + 3) + ns)))), ?_,
    (selectedState ready payload tail).regs, ?_, hfinal⟩
  · unfold recordCost
    omega
  · exact StructuredCalls.Eval.seq hp
      (StructuredCalls.Eval.seq hcopy
        (StructuredCalls.Eval.seq hcompare
          (StructuredCalls.Eval.seq hclear₁ (StructuredCalls.Eval.seq hclear₃ hselect))))

end SubexponentialSAT.SubexpRecordScan

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

theorem data_ext {a b : Data s} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

theorem move_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (he : d.stacks dst = []) (ht : d.stacks tmp = []) :
    ∃ e, Eval (move src dst tmp) (6 * (d.stacks src).length + 6) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst (d.stacks src) := by
  obtain ⟨a, ha, hsa⟩ := transfer_eval src tmp hst d
  obtain ⟨b, hb, hsb⟩ := transfer_eval tmp dst htd a
  have hat : a.stacks tmp = (d.stacks src).reverse := by
    rw [hsa]
    simp [StackRoutines.transferStacks, ht]
  have hatlen : (a.stacks tmp).length = (d.stacks src).length := by
    rw [hat, List.length_reverse]
  refine ⟨b, ?_, ?_⟩
  · have hc := Eval.seq ha hb
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · rw [hsb, hsa]
    funext j
    by_cases hjd : j = dst
    · subst j
      simp [StackRoutines.transferStacks, he, ht, Ne.symm hsd, Ne.symm htd]
    · by_cases hjs : j = src
      · subst j
        simp [StackRoutines.transferStacks, ht, hsd, hst, Ne.symm htd]
      · by_cases hjt : j = tmp
        · subst j
          simp [StackRoutines.transferStacks, he, ht, Ne.symm hsd,
            Ne.symm hst, htd, Ne.symm htd]
        · simp [StackRoutines.transferStacks, hjd, hjs, hjt]

end SubexponentialSAT.Subexp.MatrixProgramSupport

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

theorem mem_storageVertices (P : PackingData V U) (v : V) :
    v ∈ storageVertices P := by
  cases hv : P.lookup v with
  | none =>
      apply List.mem_append_right
      exact (P.mem_leftovers v).mpr ((P.lookup_none_iff v).mp hv)
  | some z =>
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨z.1, by simp, ?_⟩
      exact List.mem_map.mpr ⟨z.2, P.types.complete _, P.lookup_sound v z hv⟩

omit [DecidableEq V] in
theorem packedVertices_length (P : PackingData V U) :
    (packedVertices P).length = P.blockCount * P.types.values.length := by
  simp [packedVertices, List.length_flatMap]

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

theorem mem_packedVertices_iff (P : PackingData V U) (v : V) :
    v ∈ PackingReorder.packedVertices P ↔ ∃ z, P.lookup v = some z := by
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hv
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hi
    refine ⟨(i, u), ?_⟩
    rw [← hu]
    exact P.lookup_at i u
  · rintro ⟨z, hz⟩
    apply List.mem_flatMap.mpr
    refine ⟨z.1, by simp, ?_⟩
    exact List.mem_map.mpr ⟨z.2, P.types.complete _, P.lookup_sound v z hz⟩

end SubexponentialSAT.Subexp.PackingMetadata

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

abbrev emitCurrent : Cmd 5 5 :=
  .seq (pushConst 3 2 false)
    (.seq (.call (StackRoutines.copyProgram 1 2 4 2 3))
      (.seq (escape emitPorts) (pushConst 3 2 true)))

abbrev increment : Cmd 5 5 := pushConst 1 2 true
abbrev loop : Cmd 5 5 := .while 1 (.seq emitCurrent (.seq increment readCounter))
abbrev enumerate : Cmd 5 5 := .seq readCounter loop

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpVertexIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed generator for exactly the vertex indices below unary D. -/
namespace SubexponentialSAT.SubexpVertexIndexProgram

open BitProgram StructuredCalls

abbrev command : Cmd 5 5 := .seq (Subexp.TupleProgram.pushConst 3 2 false)
  Subexp.DimensionProgram.enumerate

abbrev program : Program 5 5 (size command+1) := compiled command 0 3

end SubexponentialSAT.SubexpVertexIndexProgram

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

def state (regs : Fin 8 → Bool)
    (source output query work3 work4 result cursor table acc : List Bool) : Data :=
  ⟨regs, ![source, output, query, work3, work4, result, cursor, table, acc]⟩

def invariant (records : List (List Bool × List Bool)) (a : Data) : Prop :=
  a.stacks 0 = [] ∧ a.stacks 1 = [] ∧ a.stacks 3 = [] ∧
    a.stacks 4 = [] ∧ a.stacks 5 = [] ∧ a.stacks 7 = SelectorProgram.rawRecords records

def inputStateWith (regs : Fin 8 → Bool) (records : List (List Bool × List Bool))
    (queries : List (List Bool)) : Data :=
  state regs [] [] [] [] [] [] (ProgramEncoding.encodeRecords queries)
    (SelectorProgram.rawRecords records) []

def outputState (records : List (List Bool × List Bool)) (queries : List (List Bool))
    (regs : Fin 8 → Bool) : Data :=
  state regs [] [] [] [] [] [] [] (SelectorProgram.rawRecords records)
    (ProgramEncoding.encodeRecords (mappedRecords records queries))

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingAddressSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The emitted storage-address table is the graph of the actual packed
coordinate order. Its lookups produce the existing reordering read plan. -/

namespace SubexponentialSAT.Subexp.PackingAddressSemantics

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem packedVertices_nodup (P : PackingData V U) :
    (PackingReorder.packedVertices P).Nodup := by
  have hp : ((List.finRange P.blockCount).product P.types.values).Nodup :=
    (List.nodup_finRange P.blockCount).product P.types.nodup
  have hm := hp.map P.completeBlocks.embed.injective
  simpa only [List.product, List.map_flatMap, List.map_map, Function.comp_def,
    PackingData.completeBlocks_apply, PackingReorder.packedVertices] using hm

theorem packed_disjoint_leftovers (P : PackingData V U) :
    List.Disjoint (PackingReorder.packedVertices P) P.leftovers := by
  apply List.disjoint_left.mpr
  intro v hp hl
  obtain ⟨z, hz⟩ := (PackingMetadata.mem_packedVertices_iff P v).mp hp
  exact ((P.mem_leftovers v).mp hl) ⟨z, (P.lookup_some_iff v z).mp hz⟩

theorem storageVertices_nodup (P : PackingData V U) :
    (PackingReorder.storageVertices P).Nodup :=
  List.Nodup.append (packedVertices_nodup P) P.leftovers_nodup (packed_disjoint_leftovers P)

end SubexponentialSAT.Subexp.PackingAddressSemantics

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

abbrev increment : Cmd 8 3 := TupleProgram.pushConst 2 0 true
abbrev body : Cmd 8 3 := .seq (readFrame 0 1 (by decide))
  (.seq clearPayload (.seq increment peek))
abbrev loop : Cmd 8 3 := .while 1 body
abbrev command : Cmd 8 3 := .seq peek loop
def program := compiled command 0 2

end SubexponentialSAT.Subexp.PackingFrameCount

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

abbrev countCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram PackingFrameCount.program id countPorts)

theorem embed_bucket (regs : Fin 8 → Bool) (localRegs : Fin 5 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool)
    (rows' query' bucket' : List Bool) :
    embedState bucketRegs bucketPorts
      (state regs rows query bucket saved keys scan minimum table count result)
      (SubexpRecordScan.recordState localRegs rows' [] query' [] [] bucket') =
    state (merged regs localRegs) rows' query' bucket' saved keys scan minimum table count result := by
  apply SelectorMapProgram.embed_eq _ _ bucketRegs_injective bucketPorts_injective
  · intro i
    fin_cases i <;> simp [bucketRegs, merged, state ]
  · intro i
    fin_cases i <;>
      simp [bucketPorts, state, SubexpRecordScan.storage]
  · intro j hj
    fin_cases j <;> simp_all [bucketRegs, merged, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
        exact False.elim (hj 4 rfl)
  · intro j hj
    fin_cases j <;> simp_all [bucketPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
        exact False.elim (hj 4 rfl) | exact False.elim (hj 5 rfl)

theorem embed_count (regs localRegs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool)
    (scan' count' : List Bool) :
    embedState id countPorts
      (state regs rows query bucket saved keys scan minimum table count result)
      (PackingFrameCount.state localRegs scan' [] count') =
    state localRegs rows query bucket saved keys scan' minimum table count' result := by
  apply SelectorMapProgram.embed_eq _ _ Function.injective_id countPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> simp [countPorts, state ]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    fin_cases j <;> simp_all [countPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl)

theorem embed_minimum (regs localRegs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool)
    (minimum' count' result' : List Bool) :
    embedState id minimumPorts
      (state regs rows query bucket saved keys scan minimum table count result)
      (PackingUnaryMin.state localRegs minimum' count' result') =
    state localRegs rows query bucket saved keys scan minimum' table count' result' := by
  apply SelectorMapProgram.embed_eq _ _ Function.injective_id minimumPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> simp [minimumPorts, state, PackingUnaryMin.state]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    fin_cases j <;> simp_all [minimumPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl)

end SubexponentialSAT.Subexp.PackingBucketCalls

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

def afterBucket (records : List BucketProgram.Record) (query acc : List Bool) : List Bool :=
  (true :: Encoding.frame (bucketPayload records query)).reverse ++ acc

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

theorem parser_state (regs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result newKeys newQuery : List Bool)
    (tag present found : Bool) :
    RecordPrograms.state ports
      (state regs rows query bucket saved keys scan minimum table count result)
      tag present found newKeys newQuery =
    state (parserRegs regs tag present found) rows newQuery bucket saved newKeys scan
      minimum table count result := by
  apply MatrixProgramSupport.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [RecordPrograms.state, ports, state]

def effect (records : List BucketProgram.Record) (query : List Bool) (a b : Data) : Prop :=
  (b.stacks 10).length = min (a.stacks 10).length (BucketProgram.selected records query).length ∧
  b.stacks 11 = afterBucket records query (a.stacks 11)

def recordPrefix (records : List BucketProgram.Record) (keys : List (List Bool)) : List Bool :=
  (table records keys).flatMap (fun bits => true :: Encoding.frame bits)

theorem encodeTable_eq_prefix (records : List BucketProgram.Record) (keys : List (List Bool)) :
    ProgramEncoding.encodeRecords (table records keys) = recordPrefix records keys ++ [false] := by
  exact SelectorMapProgram.encodeRecords_eq_prefix (table records keys)

theorem fold_afterBucket (records : List BucketProgram.Record) (keys : List (List Bool))
    (acc : List Bool) :
    keys.foldl (fun out key => afterBucket records key out) acc =
      (recordPrefix records keys).reverse ++ acc := by
  induction keys generalizing acc with
  | nil => rfl
  | cons key keys ih =>
    rw [List.foldl_cons, ih]
    simp [recordPrefix, table, afterBucket, List.reverse_append, List.append_assoc]

def outputState (records : List BucketProgram.Record) (keys : List (List Bool))
    (initial : ℕ) (suffix : List Bool) (regs : Fin 8 → Bool) : Data :=
  state regs [] [] (ProgramEncoding.encodeRecords (table records keys))
    (BucketProgram.encodeRecords records.reverse) suffix []
    (List.replicate (minimum records keys initial) true) [] [] []

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical bucket/minimum output is the existing computable packing. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open ConstructivePacking MatrixProgramSupport

variable {V U : Type*} [DecidableEq U]

theorem table_eq_typed (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) :
    table (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (P.types.values.map encodeType) =
      P.types.values.map (fun u => Encoding.frame (encodeType u) ++
        words ((P.bucket u).map encodeVertex)) := by
  simp only [table, List.map_map]
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply, bucketPayload,
    BucketProgram.constructive_bucket_output P encodeType encodeVertex hinj]

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

def workState (regs : Fin 8 → Bool)
    (vertex typeBytes block address storage metadata addresses scratch temp frame : List Bool) : Data :=
  ⟨regs, ![vertex,typeBytes,block,address,storage,metadata,addresses,scratch,temp,frame]⟩

/-- Persistent ports 0--6; work ports 7--9 start and finish empty. -/
def state (regs : Fin 8 → Bool)
    (vertex typeBytes block address storage metadata addresses : List Bool) : Data :=
  workState regs vertex typeBytes block address storage metadata addresses [] [] []

def command : Code := sequence [
  MatrixProgramSupport.copy 0 8 7,
  emitFrame 8 9 7 (by decide),
  TupleProgram.pushConst 9 0 true,
  transfer 9 4,
  emitFrame 1 8 7 (by decide),
  MatrixProgramSupport.copy 2 9 7,
  emitFrame 9 8 7 (by decide),
  TupleProgram.pushConst 8 0 true,
  emitFrame 8 5 7 (by decide),
  MatrixProgramSupport.copy 0 9 7,
  emitFrame 9 5 7 (by decide),
  MatrixProgramSupport.copy 3 8 7,
  emitFrame 8 6 7 (by decide),
  emitFrame 0 6 7 (by decide),
  TupleProgram.pushConst 3 0 true]

abbrev program : Program 8 10 (size command+1) := compiled command 0 4

end SubexponentialSAT.Subexp.PackingEntryEmitter


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

def finalState (count source : Fin s) (a : Data s)
    (pre : List (List Bool)) (rest : List Bool) : Data s :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2
      (a.regs 2 || !pre.isEmpty),
    Function.update (Function.update a.stacks count []) source rest⟩

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

def state (regs : Fin 8 → Bool) (source key count vertex scratch : List Bool) : Data 5 :=
  ⟨regs, ![source, key, count, vertex, scratch]⟩

abbrev command : Cmd 8 5 :=
  .seq (readWord 0 1 4 (by decide))
    (.seq (PackingFrameSkip.command 2 0)
      (.seq (readWord 0 3 4 (by decide))
        (.call (StackRoutines.clearProgram 0 0 1))))

def program := compiled command 0 3

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

abbrev selectCall : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram PackingBucketSelect.program id selectPorts)

theorem embed_select (regs localRegs : Fin 8 → Bool) (c : Context)
    (source key count vertex scratch temp workA workB : List Bool)
    (source' key' count' vertex' scratch' : List Bool) :
    embedState id selectPorts (state regs c source key count vertex scratch temp workA workB)
      (PackingBucketSelect.state localRegs source' key' count' vertex' scratch') =
    state localRegs c source' key' count' vertex' scratch' temp workA workB := by
  apply SelectorMapProgram.embed_eq _ _ Function.injective_id selectPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> simp [state, PackingBucketSelect.state, selectPorts]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    fin_cases j <;> simp_all [selectPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
        exact False.elim (hj 4 rfl)

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the actual covered-entry emitter into the extraction controller. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

abbrev emitCall : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram PackingEntryEmitter.program id emitPorts)

end SubexponentialSAT.Subexp.PackingExtraction

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

abbrev callback : Cmd 8 19 :=
  .seq (transfer 8 0)
    (.seq (MatrixProgramSupport.copy 10 2 9)
      (.seq selectCall
        (.seq emitCall
          (.seq (.base (.atom (.set 5 false)))
            (.seq (.base (.atom (.set 6 true))) (.base (.atom (.set 7 false))))))))

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

abbrev blockCommand : Cmd 8 19 := RecordPrograms.iterate ports callback

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

abbrev body : Cmd 8 19 :=
  .seq (MatrixProgramSupport.copy 15 7 9)
    (.seq blockCommand (.seq (TupleProgram.pushConst 10 0 true) (.seq popRemaining refresh)))
abbrev loop : Cmd 8 19 := .while 4 body
abbrev command : Cmd 8 19 := .seq refresh loop
def program := compiled command 15 12

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

def coverRows (entries : List Entry) (n start : ℕ) : List (List Bool × List Bool) :=
  (List.range' start n).flatMap fun i => blockRows i entries (PackingMetadata.unary i)

theorem advanceMany_metadata (entries : List Entry) (n i : ℕ) (c : Context)
    (hblock : c.block = PackingMetadata.unary i) :
    (advanceMany entries n i c).metadata =
      SelectorProgram.rawRecords (coverRows entries n i).reverse ++ c.metadata := by
  induction n generalizing i c with
  | zero => simp [advanceMany, coverRows, SelectorProgram.rawRecords]
  | succ n ih =>
    have hb : (advanced i entries c).block = PackingMetadata.unary (i + 1) := by
      rw [(advanced_static i entries c).1, hblock]
      simp [PackingMetadata.unary, List.replicate_succ]
    rw [advanceMany, ih _ _ hb]
    have hm : (advanced i entries c).metadata = (emitEntries i entries c).metadata := rfl
    rw [hm, emitEntries_metadata, hblock]
    simp [coverRows, List.range'_succ, List.reverse_append, SelectorProgram.rawRecords,
      List.flatMap_append, List.append_assoc]

theorem emitEntries_address_unary (i : ℕ) (entries : List Entry) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (emitEntries i entries c).address = PackingMetadata.unary (a + entries.length) := by
  rw [emitEntries_address, ha]
  change List.replicate entries.length true ++ List.replicate a true =
    List.replicate (a + entries.length) true
  rw [← List.replicate_add, Nat.add_comm entries.length a]

/-- The address table is prepended in the same order as the storage stream. -/
theorem emitEntries_addresses (i : ℕ) (entries : List Entry) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (emitEntries i entries c).addresses =
      SelectorProgram.rawRecords
        (PackingAddressSemantics.addressRows (entries.map (entryVertex i)) a).reverse ++
          c.addresses := by
  induction entries generalizing c a with
  | nil => simp [emitEntries, SelectorProgram.rawRecords]
  | cons e es ih =>
    have hd : (emitted c e.1 (entryVertex i e)).address =
        PackingMetadata.unary (a + 1) := by
      simp [emitted, ha, PackingMetadata.unary, List.replicate_succ]
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).addresses = _
    rw [ih _ _ hd]
    simp [PackingAddressSemantics.addressRows_cons, List.reverse_cons,
      SelectorProgram.rawRecords, List.flatMap_append, emitted,
      PackingEntryEmitter.addressOutput, ha, PackingMetadata.unary, List.append_assoc]

theorem advanceMany_addresses (entries : List Entry) (n i : ℕ) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (advanceMany entries n i c).addresses =
      SelectorProgram.rawRecords
        (PackingAddressSemantics.addressRows (coverVertices entries n i) a).reverse ++
          c.addresses := by
  induction n generalizing i c a with
  | zero => simp [advanceMany, coverVertices, SelectorProgram.rawRecords]
  | succ n ih =>
    have hd : (advanced i entries c).address =
        PackingMetadata.unary (a + entries.length) :=
      emitEntries_address_unary i entries c a ha
    rw [advanceMany, ih _ _ _ hd]
    have hs : (advanced i entries c).addresses = (emitEntries i entries c).addresses := rfl
    rw [hs, emitEntries_addresses i entries c a ha, coverVertices_succ]
    simp [PackingAddressSemantics.addressRows_append, List.reverse_append,
      SelectorProgram.rawRecords, List.flatMap_append, List.append_assoc]

theorem advanceMany_address_unary (entries : List Entry) (n i : ℕ) (c : Context) (a : ℕ)
    (ha : c.address = PackingMetadata.unary a) :
    (advanceMany entries n i c).address = PackingMetadata.unary (a + n * entries.length) := by
  induction n generalizing i c a with
  | zero => simpa [advanceMany] using ha
  | succ n ih =>
    have hd : (advanced i entries c).address = PackingMetadata.unary (a + entries.length) :=
      emitEntries_address_unary i entries c a ha
    rw [advanceMany, ih _ _ _ hd]
    congr 1
    ring

theorem advanceMany_static (entries : List Entry) (n i : ℕ) (c : Context)
    (hb : c.block = PackingMetadata.unary i)
    (hr : c.remaining = PackingMetadata.unary n) :
    (advanceMany entries n i c).block = PackingMetadata.unary (i + n) ∧
    (advanceMany entries n i c).remaining = [] ∧
    (advanceMany entries n i c).buckets = c.buckets := by
  induction n generalizing i c with
  | zero =>
    simpa only [advanceMany, Nat.add_zero, PackingMetadata.unary,
      List.replicate_zero] using
      And.intro hb (And.intro hr (rfl : c.buckets = c.buckets))
  | succ n ih =>
    obtain ⟨hb', ht', hr'⟩ := advanced_static i entries c
    have hb'' : (advanced i entries c).block = PackingMetadata.unary (i + 1) := by
      rw [hb', hb]
      simp [PackingMetadata.unary, List.replicate_succ]
    have hr'' : (advanced i entries c).remaining = PackingMetadata.unary n := by
      rw [hr', hr]
      simp [PackingMetadata.unary, List.replicate_succ]
    obtain ⟨hblock, hremaining, hbuckets⟩ := ih (i + 1) (advanced i entries c) hb'' hr''
    refine ⟨?_, hremaining, hbuckets.trans ht'⟩
    simpa only [advanceMany, Nat.add_assoc, Nat.add_comm 1 n] using hblock

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

omit [DecidableEq V] in
theorem entryVertex_typed (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (i : Fin P.blockCount) (u : U) :
    entryVertex i.val (encodeType u, (P.bucket u).map encodeVertex) =
      encodeVertex (P.vertexAt i u) := by
  have hi : i.val < (P.bucket u).length := i.isLt.trans_le (P.blockCount_le_bucket u)
  rw [entryVertex, List.getD_eq_getElem _ [] (by simpa using hi)]
  simp [PackingData.vertexAt]

end SubexponentialSAT.Subexp.PackingExtraction

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

def dimProgram := compiled DimensionProgram.enumerate 0 3
abbrev dimensions : Cmd 5 6 := .call (ProgramLinking.liftProgram dimProgram id dimStacks)

end SubexponentialSAT.Subexp.AssignmentSeedRange

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

def command : Code := sequence [
  MatrixProgramSupport.copy 0 7 6, emitFrame 7 8 6 (by decide),
  TupleProgram.pushConst 8 0 true, transfer 8 3,
  MatrixProgramSupport.copy 1 7 6, emitFrame 7 8 6 (by decide),
  TupleProgram.pushConst 8 0 false, emitFrame 8 4 6 (by decide),
  MatrixProgramSupport.copy 0 7 6, emitFrame 7 4 6 (by decide),
  MatrixProgramSupport.copy 2 7 6, emitFrame 7 5 6 (by decide),
  emitFrame 0 5 6 (by decide),
  TupleProgram.pushConst 1 0 true, TupleProgram.pushConst 2 0 true]

abbrev program : Program 8 9 (size command+1) := compiled command 0 3

end SubexponentialSAT.Subexp.PackingLeftoverEmitter

namespace SubexponentialSAT.Subexp.PackingCoveredQuery

open BitProgram StructuredCalls

abbrev core : Cmd 5 6 := .seq (SelectorProgram.atom (.set 4 false))
  (.seq SelectorProgram.peek SelectorProgram.scan)

abbrev command : Cmd 5 6 := .seq core
  (.seq (.call (StackRoutines.clearProgram 0 0 1))
    (.seq (.call (StackRoutines.clearProgram 2 0 1))
      (.call (StackRoutines.clearProgram 5 0 1))))

def program := compiled command 0 5

end SubexponentialSAT.Subexp.PackingCoveredQuery


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

def queryCall : Code := .call
  (ProgramLinking.liftProgram PackingCoveredQuery.program queryRegs queryStacks)

def emitCall : Code := .call
  (ProgramLinking.liftProgram PackingLeftoverEmitter.program id emitterStacks)

def callback : Code := .seq (transfer 8 15)
  (.seq (MatrixProgramSupport.copy 6 0 9)
    (.seq (MatrixProgramSupport.copy 15 2 9)
      (.seq queryCall (.seq (.ite 4 clearVertex emitCall) resetParser))))

def command : Code := RecordPrograms.iterate ports callback
def program := compiled command 7 12

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

theorem metadataRecords_eq_addressRows (vertices : List ℕ) (start : ℕ) :
    PackingLeftovers.metadataRecords start vertices =
      (PackingAddressSemantics.addressRows (vertices.map PackingLeftovers.unary) start).map
        (fun p => (p.1, PackingLeftoverEmitter.metadataPayload p.2)) := by
  induction vertices generalizing start with
  | nil => rfl
  | cons v vertices ih =>
    simp only [PackingLeftovers.metadataRecords, List.map_cons,
      PackingAddressSemantics.addressRows_cons, ih]

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def vertexBytes (code : V → ℕ) (v : V) : List Bool := PackingMetadata.unary (code v)

omit [DecidableEq V] in
theorem vertexBytes_injective (code : V → ℕ) (hc : Function.Injective code) :
    Function.Injective (vertexBytes code) := PackingMetadata.unary_injective.comp hc

end SubexponentialSAT.Subexp.PackingOutputSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)

def equalityProgram := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def projectInner (s : OuterStore) : Store := s ∘ innerPort

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end


