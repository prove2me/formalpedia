-- Prove2me | Definitions.Def_OAIQ081S157
-- name    : OAIQ081S157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:59:06.609959+00:00
-- url     : https://prove2.me/theorems/36fa3c49-b289-42af-9451-1c8cb53c155e
-- title:
--   Definitions bundle OAIQ081S157 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 21 definitions, 1 inductive type or structure and 11 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.denominatorUnit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.difference`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.inverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.negative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.nodeCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ofInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.represent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.saved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.start`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.sourceWorkspace`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uniformBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeSourceBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.stagedSourceBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.entryLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.power`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.numeric`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankCost`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceCache`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceConfiguration`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceParameters`, `SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramPacked`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStagedPacked`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_PackingInverseStage`, `SubexponentialSAT_Subexp_PackingLeftoverStage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S139`, `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S143` and `OAIQ081S144` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S166`, `OAIQ081S168`, `OAIQ081S169`, `OAIQ081S170`, `OAIQ081S171` and `OAIQ081S172`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_difference`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_inverse` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_difference`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache.native_inverse` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S141
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S144

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

def unsignedSaved (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (R : ℕ) (a : List Bool) : Saved :=
  ⟨Hwords.flatten,List.replicate (R*width.length) false,width,power,List.replicate R true,a⟩


end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

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

theorem dimensions_eval (regs : Fin 5 → Bool) (n : ℕ) :
    ∃ rf, Eval dimensions (DimensionProgram.loopCost 0 n + 1)
      (state regs 0 (unary n) [false] [])
      (state rf n [] (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) []) := by
  let a : State 5 5 := ⟨regs, ![unary n, [], [], [false], []]⟩
  have ha : DimensionProgram.Ready 0 (unary n) [] a := by
    simp [DimensionProgram.Ready, a, ProgramEncoding.encodeRecords, Encoding.encodeList]
  obtain ⟨b, hb, _, ht⟩ := DimensionProgram.enumerate_eval 0 (unary n) [] a ha
  simp only [List.length_replicate, Nat.zero_add, List.append_nil] at hb ht
  let d := state regs 0 (unary n) [false] []
  have he : embedState id dimStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id dimStacks_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hf : embedState id dimStacks d b =
      state b.regs n [] (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id dimStacks_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i
      fin_cases i
      · exact hb.1.symm
      · exact hb.2.1.symm
      · exact hb.2.2.1.symm
      · exact hb.2.2.2.1.symm
      · exact hb.2.2.2.2.symm
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim |
        exact (hi ⟨1, rfl⟩).elim | exact (hi ⟨2, rfl⟩).elim |
        exact (hi ⟨3, rfl⟩).elim
  have h := eval_call_lifted dimProgram id dimStacks d Function.injective_id
    dimStacks_injective (compiled_halt_trace ht 0 3)
  exact ⟨b.regs, by simpa only [dimensions, he, hf] using h⟩

theorem reverse_eval (regs : Fin 5 → Bool) (n : ℕ) (records : List (List Bool)) :
    ∃ ticks, ticks ≤ 10 * (ProgramEncoding.encodeRecords records).length ∧
      Eval reverse ticks
        (state regs n [] (ProgramEncoding.encodeRecords records) [false])
        (state (reversedRegs regs) n [] [] (ProgramEncoding.encodeRecords records.reverse)) := by
  let a := state regs n [] (ProgramEncoding.encodeRecords records) [false]
  let x := SubexpNormalizeProgram.filterState (regs 0) (regs 1) (regs 2)
    (ProgramEncoding.encodeRecords records) [] [false] []
  let y := SubexpNormalizeProgram.filterState false true false [] []
    (ProgramEncoding.encodeRecords records.reverse) []
  have hx : embedState reverseRegisters reverseStacks a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hy : embedState reverseRegisters reverseStacks a y =
      state (reversedRegs regs) n [] [] (ProgramEncoding.encodeRecords records.reverse) := by
    apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim |
        exact (hi ⟨1, rfl⟩).elim | exact (hi ⟨2, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim |
        exact (hi ⟨1, rfl⟩).elim | exact (hi ⟨2, rfl⟩).elim
  obtain ⟨ticks, hbound, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn
    records [] [] [] (regs 0) (regs 1) (regs 2)
  simp only [List.append_nil] at ht
  have h := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks a reverseRegisters_injective reverseStacks_injective
    (a := x) (b := y) ht
  exact ⟨ticks, hbound, by simpa only [reverse, hx, hy] using h⟩

theorem command_eval (regs : Fin 5 → Bool) (n : ℕ) :
    ∃ ticks, ticks ≤ budget n ∧ Eval command ticks (inputState regs n) (outputState n) := by
  let a := inputState regs n
  let b := pushedState 3 0 false a
  have hb : b = state b.regs 0 (unary n) [false] [] := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨rf, hd⟩ := dimensions_eval b.regs n
  rw [← hb] at hd
  let c := state rf n [] (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) []
  let d := pushedState 5 0 false c
  have he : d = state d.regs n []
      (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) [false] := by
    apply congrArg (StructuredProgram.State.mk d.regs)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨ticks, hbound, hr⟩ := reverse_eval d.regs n (DimensionProgram.earlierRows 0 n)
  rw [← he] at hr
  have hrecords : (DimensionProgram.earlierRows 0 n).reverse = (List.range n).map unary := by
    simp [earlierRows_eq, List.map_reverse, ← List.range_eq_range']
  rw [hrecords] at hr
  let e := state (reversedRegs d.regs) n [] [] (seedRecords n)
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 1 e.stacks⟩
  have h1 := pushConst_eval 3 0 false a
  have h3 := pushConst_eval 5 0 false c
  have h5 := TupleProgram.clear_eval 1 0 1 e
  have h6 := Eval.base (CandidateScoreProgram.resetList_eval (List.finRange 5) f)
  have hout : (⟨CandidateScoreProgram.resetValues (List.finRange 5) f.regs, f.stacks⟩ : Data) =
      outputState n := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; simp [CandidateScoreProgram.resetValues_apply ]
    · funext i; fin_cases i <;> simp [f, e, state, StackRoutines.clearStacks]
  rw [hout] at h6
  have h := h1.seq (hd.seq (h3.seq (hr.seq (h5.seq h6))))
  change Eval command _ a (outputState n) at h
  refine ⟨_, ?_, h⟩
  have he1 : (e.stacks 1).length = n := by simp [e, state]
  simp only [he1, List.length_finRange]
  dsimp [budget]
  omega

theorem program_runsIn (regs : Fin 5 → Bool) (n : ℕ) :
    RunsIn program (budget n + 1)
      ((inputState regs n).withPC (some program.entry)) ((outputState n).withPC none) := by
  obtain ⟨ticks, ht, he⟩ := command_eval regs n
  exact ⟨ticks + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 5⟩

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingInverseStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The inverse read plan is constructed by actual generated vertex queries
and actual scans of the emitted address table. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

theorem inverse_eval (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ)
    (hD : input.dimension = List.replicate D true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ inverseBudget records D, ∃ rf,
      Eval inverse steps
        (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs)
        (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage
          (ProgramEncoding.encodeRecords (inverseRows records D)) rf) := by
  let a := outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs
  let b := PackingPlumbing.run queriesSetup a
  have hv : PackingPlumbing.Valid queriesSetup a := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, queriesSetup, a, outputState, inputState]
  have h0 : (project (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b).stacks 0 =
      SubexpVertexIndexProgram.unary D := by
    simp [project, stackPorts, b, PackingPlumbing.run, queriesSetup, PackingPlumbing.Op.next,
      a, outputState, inputState, StackRoutines.copyStacks, hD]
  have hempty : ∀ i : Fin 5, i ≠ 0 →
      (project (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b).stacks i = [] := by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    all_goals
      simp [project, stackPorts, b, PackingPlumbing.run, queriesSetup, PackingPlumbing.Op.next,
        a, outputState, inputState, StackRoutines.copyStacks]
  obtain ⟨q, hq, hready⟩ := SubexpVertexIndexProgram.program_trace D
    (project (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b)
    h0 (hempty 1 (by decide)) (hempty 2 (by decide))
    (hempty 3 (by decide)) (hempty 4 (by decide))
  let qstate : State 5 5 :=
    ⟨q.regs, ![[], List.replicate D true, [], ProgramEncoding.encodeRecords (inverseQueries D), []]⟩
  have hqe : q = qstate := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rcases hready with ⟨h0, h1, h2, h3, h4⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  rw [hqe] at hq
  let c := install (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b qstate
  have hquery : Eval queriesCall (6 * D ^ 2 + 10 * D + 5) b c :=
    lowCall_eval _ _ _ b qstate hq
  have hc : c.stacks = fun i =>
      if i = 1 then List.replicate D true else if i = 3 then ProgramEncoding.encodeRecords (inverseQueries D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i :=
    query_call_stacks input blocks leftovers metadata storage records D regs q.regs
  have hw : PackingPlumbing.Valid queriesSave c := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, queriesSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hc, outputState, inputState,
      StackRoutines.transferStacks, StackRoutines.clearStacks]
  let d := PackingPlumbing.run queriesSave c
  have hd : d.stacks = fun i =>
      if i = 6 then ProgramEncoding.encodeRecords (inverseQueries D)
      else if i = 7 then SelectorProgram.rawRecords records
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i :=
    query_save_stacks input blocks leftovers metadata storage records D regs c hc
  have hp : project (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d =
      SelectorMapProgram.inputStateWith
        (project (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d).regs records (inverseQueries D) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, hd, outputState, inputState
]
  obtain ⟨ns, hns, rs, hst⟩ := SelectorMapProgram.program_trace_from records (inverseQueries D)
    (project (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d).regs
  let e := install (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d
    (SelectorMapProgram.outputState records (inverseQueries D) rs)
  have hselect : Eval inverseCall ns d e := by
    apply lowCall_eval
    rw [hp]
    exact hst
  have hes : e.stacks = fun i =>
      if i = 7 then SelectorProgram.rawRecords records
      else if i = 8 then ProgramEncoding.encodeRecords (inverseRows records D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i :=
    inverse_call_stacks input blocks leftovers metadata storage records D regs d rs hd
  have hx : PackingPlumbing.Valid inverseSave e := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, inverseSave, PackingPlumbing.move]
  let f := PackingPlumbing.run inverseSave e
  have hf : f = outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage
      (ProgramEncoding.encodeRecords (inverseRows records D)) f.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [f, PackingPlumbing.run, inverseSave, PackingPlumbing.move, PackingPlumbing.Op.next,
        hes, outputState, inputState, StackRoutines.transferStacks, StackRoutines.clearStacks]
  have hc1 : PackingPlumbing.cost queriesSetup a = 7 * D + 5 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, queriesSetup, a, outputState, inputState, hD]
  have hc2 : PackingPlumbing.cost queriesSave c =
      6 * (ProgramEncoding.encodeRecords (inverseQueries D)).length + 2 * D +
      7 * (SelectorProgram.rawRecords records).length + 14 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, queriesSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hc, outputState, inputState,
      StackRoutines.transferStacks, StackRoutines.clearStacks] ; omega
  have hc3 : PackingPlumbing.cost inverseSave e =
      6 * (ProgramEncoding.encodeRecords (inverseRows records D)).length +
      2 * (SelectorProgram.rawRecords records).length + 9 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, inverseSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hes, outputState, inputState,
      StackRoutines.transferStacks] ; omega
  have he := (PackingPlumbing.eval queriesSetup a hv).seq
    (hquery.seq ((PackingPlumbing.eval queriesSave c hw).seq
      (hselect.seq (PackingPlumbing.eval inverseSave e hx))))
  refine ⟨PackingPlumbing.cost queriesSetup a + ((6 * D ^ 2 + 10 * D + 5) +
    (PackingPlumbing.cost queriesSave c + (ns + PackingPlumbing.cost inverseSave e))), ?_, f.regs, ?_⟩
  · rw [hc1, hc2, hc3]
    unfold inverseBudget
    omega
  · change Eval inverse _ a f at he
    rw [hf] at he
    exact he

end SubexponentialSAT.Subexp.PackingProgram

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

theorem leftovers_save_stacks (input : Input) (n : ℕ)
    (records : PackingLeftovers.Records) (result : PackingLeftovers.Snapshot)
    (regs : Fin 16 → Bool) (b : Data)
    (hb : b.stacks = fun i =>
      if i = 6 then SelectorProgram.rawRecords records
      else if i = 10 then PackingLeftovers.unary result.rank
      else if i = 11 then PackingLeftovers.unary result.address
      else if i = 12 then result.storage
      else if i = 13 then result.metadata
      else if i = 14 then result.addresses
      else if i = 30 then List.replicate n true
      else (inputState input regs).stacks i) :
    (PackingPlumbing.run leftoversSave b).stacks =
      (outputState input (List.replicate n true) (List.replicate result.rank true)
        result.metadata result.addresses (result.storage.reverse ++ [false]) [] regs).stacks := by
  funext i
  by_cases hi : i ∈ ([6, 10, 11, 12, 13, 14, 31, 32, 33, 34, 35, 39] : List (Fin 48))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [PackingPlumbing.run, leftoversSave, PackingPlumbing.move,
        PackingPlumbing.Op.next, hb, inputState, outputState,
        StackRoutines.transferStacks, StackRoutines.clearStacks, TupleProgram.pushedState]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rcases hi with ⟨h6, h10, h11, h12, h13, h14, h31, h32, h33, h34, h35, h39⟩
    simp [PackingPlumbing.run, leftoversSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hb, inputState, outputState, h6, h10, h11, h12, h13, h14,
      h31, h32, h33, h34, h35, h39, StackRoutines.transferStacks, StackRoutines.clearStacks,
      TupleProgram.pushedState]

theorem leftovers_eval (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (records : PackingLeftovers.Records)
    (hm : c.metadata = SelectorProgram.rawRecords records)
    (ha : c.address = List.replicate c.address.length true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ leftoversBudget records D c, ∃ rf,
      Eval leftovers steps (verticesOutputState input n D c regs)
        (outputState input (List.replicate n true)
          (List.replicate (leftoverResult records D c).rank true)
          (leftoverResult records D c).metadata (leftoverResult records D c).addresses
          ((leftoverResult records D c).storage.reverse ++ [false]) [] rf) := by
  let a := verticesOutputState input n D c regs
  let initial := PackingOutputSemantics.snapshotOf c
  let result := leftoverResult records D c
  have hp : project (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a =
      PackingLeftovers.state
        (project (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a).regs
        (SelectorProgram.rawRecords records)
        (ProgramEncoding.encodeRecords ((List.range D).map PackingLeftovers.unary) ++ [])
        (PackingLeftovers.unary initial.rank) (PackingLeftovers.unary initial.address)
        initial.storage initial.metadata initial.addresses := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, a, verticesOutputState, extractionOutputState,
        inputState, AssignmentSeedRange.seedRecords,
 initial, PackingOutputSemantics.snapshotOf, hm] ; exact ha
  obtain ⟨nl, rl, hnl, hlt⟩ := PackingLeftovers.program_trace records (List.range D) initial
    (project (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a).regs []
  dsimp only [initial] at hnl
  let b := install (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a
    (PackingLeftovers.state rl (SelectorProgram.rawRecords records) []
      (PackingLeftovers.unary result.rank) (PackingLeftovers.unary result.address)
      result.storage result.metadata result.addresses)
  have hcall : Eval leftoversCall nl a b := by
    apply lowCall_eval
    rw [hp]
    exact hlt
  have hbstacks : b.stacks = fun i =>
      if i = 6 then SelectorProgram.rawRecords records
      else if i = 10 then PackingLeftovers.unary result.rank
      else if i = 11 then PackingLeftovers.unary result.address
      else if i = 12 then result.storage
      else if i = 13 then result.metadata
      else if i = 14 then result.addresses
      else if i = 30 then List.replicate n true
      else (inputState input regs).stacks i :=
    leftovers_call_stacks input n D c records result regs rl
  have hv : PackingPlumbing.Valid leftoversSave b := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, leftoversSave,
      PackingPlumbing.move]
  let d := PackingPlumbing.run leftoversSave b
  have hd : d = outputState input (List.replicate n true)
      (List.replicate result.rank true) result.metadata result.addresses
      (result.storage.reverse ++ [false]) [] d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    exact leftovers_save_stacks input n records result regs b hbstacks
  have hcost : PackingPlumbing.cost leftoversSave b =
      6 * result.rank + 6 * result.metadata.length + 6 * result.addresses.length +
      3 * result.storage.length + 2 * (SelectorProgram.rawRecords records).length +
      2 * result.address + 32 :=
    leftovers_save_cost input n records result regs b hbstacks
  have hrun := hcall.seq (PackingPlumbing.eval leftoversSave b hv)
  refine ⟨nl + PackingPlumbing.cost leftoversSave b, ?_, d.regs, ?_⟩
  · rw [hcost]
    unfold leftoversBudget
    dsimp only [result]
    omega
  · change Eval leftovers _ a d at hrun
    rw [hd] at hrun
    exact hrun

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

abbrev Data := State 10 64

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native interpolation-cache values implement the exact node units used
by the universal source semantics. No field inverse is assumed in O. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open InterpolationCacheProgram

variable {d Q : ℕ}

def native (t : ℕ) (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne : Coeff t d) : NodeCache (Coeff t d) Q where
  node i := RingNodeProgram.nodeCode t d (i.val+1)
  inverse i := inverseValue t a M cache minusOne (RingNodeProgram.nodeCode t d (i.val+1))
  difference i j := differenceValue t a M cache minusOne
    (RingNodeProgram.nodeCode t d (i.val+1)) (RingNodeProgram.nodeCode t d (j.val+1))

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceConfiguration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete numerical and cache inputs to the source bank. The state predicate
contains byte representations only; it contains no program-service premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

structure Parameters (r Q d : ℕ) where
  t : ℕ
  ht : 0 < t
  hd : 0 < d
  model : RingModel.Data d
  modulus : SubexpPreparedQuartic.Modulus 3 t
  cache : RingProgram.ScalarCache 3 t
  hz : BinaryArithmetic.toNat cache.zero.val < 3^t
  R : ℕ
  hwords : List (List Bool)
  width : List Bool
  power : WordPair
  aWord : List Bool
  hlen : hwords.length=R
  hwidths : ∀ x∈hwords,x.length=width.length
  hvalues : hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length)
  hp : pairValue power=(2:ℤ)^(R-1)
  hpt : LayoutProgramScalar.wordTotal power=2^(R-1)
  hwidth : Q+1 ≤ width.length
  hAQ : aWord.length ≤ Q
  hQ : 1 ≤ Q
  hfield : Q < 3^d
  minusOne : ModelCode t d
  hminus : (RingProgram.modelRing t ht hd model modulus cache).decode minusOne= -1
  invDenom : ModelCode t d
  denom : (model.O t)ˣ
  hdenom : (denom : model.O t)=(LayoutNumerator.denominator R : model.O t)
  hinv : (RingProgram.modelRing t ht hd model modulus cache).decode invDenom=(↑(denom⁻¹):model.O t)
  integerWord : ℤ → ModelCode t d
  hinteger : ∀ z,(RingProgram.modelRing t ht hd model modulus cache).decode (integerWord z)=(z:model.O t)
  ringWidth : List Bool
  rowWidth : List Bool
  hringWidth : ringWidth.length=d*SubexpLiftRing.baseWidth 3 t
  hrowWidth : rowWidth.length=Q*ringWidth.length

namespace Parameters
variable {r Q d : ℕ}
noncomputable def ops (p : Parameters r Q d) :=
  RingProgram.modelRing p.t p.ht p.hd p.model p.modulus p.cache

def saved (p : Parameters r Q d) : Numerator.Saved :=
  LayoutProgramScalar.FromCounts.unsignedSaved p.hwords p.width p.power p.R p.aWord

def start (p : Parameters r Q d) : Fin Q := ⟨0,by have := p.hQ; omega⟩

def nodeCache (p : Parameters r Q d) := SourceCache.native (Q:=Q) p.t p.model p.modulus p.cache p.minusOne

def inverse (p : Parameters r Q d) : Fin Q → ModelCode p.t d := p.nodeCache.inverse

def negative (p : Parameters r Q d) (i : Fin Q) : ModelCode p.t d :=
  InterpolationCacheProgram.negativeValue p.t p.model p.modulus p.cache p.minusOne (p.nodeCache.node i)

def difference (p : Parameters r Q d) : Fin Q → Fin Q → ModelCode p.t d := p.nodeCache.difference

noncomputable def rows (p : Parameters r Q d) (u y : UniversalType r Q 1) :=
  LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 p.aWord.length p.R)
    p.denom u 0 p.R (p.model.nodeUnits p.t Q p.ht p.hfield) y
end Parameters

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial resource bounds for the concrete universal source
branch. Typed table entries contribute their actual d*B bit width. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

def sourceWorkspace (p : Parameters r Q d) (S : ℕ) : ℕ :=
  S+Q*(d*SubexpLiftRing.baseWidth 3 p.t)+UniversalRowSourceBound.indicesBound Q

def uniformBudget (p : Parameters r Q d) (S : ℕ) : ℕ :=
  LayoutSourceValuesProgram.Native.polynomialBudget r Q p.aWord.length p.R p.width.length
    (pairLength p.power) p.t d+
  (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
    UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
  14*S+224*sourceWorkspace p S+UniversalRowSourceBound.sourceBound (sourceWorkspace p S)+281

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

abbrev numeric : Cmd 9 77 := liftCommand Prepared.command (Bank.port 0) (Bank.port 42) registers id

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

def Inputs.power (s : Inputs) : WordPair := (LayoutProgram.IntegerCache.denominatorWord s.R,[])
def Inputs.entryLength (s : Inputs) : ℕ := LayoutFiberSumProgram.nativeLength s.R s.width s.power

theorem Inputs.power_value (s : Inputs) : BinaryArithmetic.toNat s.power.1=2^(s.R-1) :=
  LayoutProgram.powerWord_value (s.R-1)
theorem Inputs.power_signed (s : Inputs) : pairValue s.power=(2:ℤ)^(s.R-1) := by
  simp [pairValue,RowSelectionProgram.signedValue,Inputs.power,LayoutProgram.IntegerCache.denominatorWord,
    LayoutProgram.powerWord_value]
theorem Inputs.power_total (s : Inputs) : LayoutProgramScalar.wordTotal s.power=2^(s.R-1) := by
  simpa [LayoutProgramScalar.wordTotal,pairTotal,Inputs.power,BinaryArithmetic.toNat] using s.power_value

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pure packaging of the caches produced by native setup. No execution,
source polynomial, or interpolation table is supplied by this constructor.
The integer encoder below is a semantic witness used in the row proof; the
runtime integer lift remains the already checked native program. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram RowSelectionProgram

namespace Parameters

/-- Coefficientwise representation of a ring element, for semantic proofs. -/
def represent (t : ℕ) (ht : 0 < t) {d : ℕ} (model : RingModel.Data d)
    (x : model.O t) : ModelCode t d :=
  fun i => encodeWord 3 t (model.coordinates t ht x i)

theorem represent_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (x : model.O t) :
    (RingProgram.modelRing t ht hd model M cache).decode (represent t ht model x)=x := by
  rw [RingProgram.modelRing_decode]
  simp only [represent,wordValue_encodeWord]
  exact (model.coordinates t ht).symm_apply_apply x

/-- The inverse word produced by the native denominator loop determines the
unit used by the mathematical row construction. -/
def denominatorUnit (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (R : ℕ) (inv : ModelCode t d)
    (hinv : (RingProgram.modelRing t ht hd model M cache).decode inv *
      (2 : model.O t)^(R-1)=1) : (model.O t)ˣ where
  val := (LayoutNumerator.denominator R : model.O t)
  inv := (RingProgram.modelRing t ht hd model M cache).decode inv
  val_inv := by simpa [LayoutNumerator.denominator,mul_comm] using hinv
  inv_val := by simpa [LayoutNumerator.denominator] using hinv

/-- Only the actual head-input record, generated H-cache invariant, typed ring
caches, and generated inverse equation are needed to form source parameters. -/
def ofInputs (s : LeafHeadSetupProgram.Native.Inputs)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (minusOne inv : ModelCode t d)
    (hm : (RingProgram.modelRing t ht hd model M cache).decode minusOne = -1)
    (hi : (RingProgram.modelRing t ht hd model M cache).decode inv *
      (2 : model.O t)^(s.R-1)=1)
    (hfield : s.Q < 3^d) : Parameters s.r s.Q d where
  t := t
  ht := ht
  hd := hd
  model := model
  modulus := M
  cache := cache
  hz := hz
  R := s.R
  hwords := words
  width := s.width
  power := s.power
  aWord := s.height
  hlen := by simpa [LeafHeadSetupProgram.unary] using hc.1
  hwidths := hc.2.1
  hvalues := by simpa [LeafHeadSetupProgram.unary] using hc.2.2
  hp := s.power_signed
  hpt := s.power_total
  hwidth := s.width_node
  hAQ := s.height_le
  hQ := by have h := s.node.isLt; omega
  hfield := hfield
  minusOne := minusOne
  hminus := hm
  invDenom := inv
  denom := denominatorUnit t ht hd model M cache s.R inv hi
  hdenom := rfl
  hinv := rfl
  integerWord := fun z => represent t ht model (z : model.O t)
  hinteger := fun z => represent_decode t ht hd model M cache (z : model.O t)
  ringWidth := List.replicate (d*baseWidth 3 t) true
  rowWidth := List.replicate (s.Q*(d*baseWidth 3 t)) true
  hringWidth := List.length_replicate
  hrowWidth := by simp only [List.length_replicate]

end Parameters
end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramPacked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Discharge of the source callback by the actual packed-source dispatcher.
All premises below are stored-byte and cache invariants. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def nativeSourceBudget {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  800*(2*S+1)^2+SourceBank.uniformBudget p S+200*S+302

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramStagedPacked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def stagedSourceBudget {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  nativeSourceBudget p S+12*S+12

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end


