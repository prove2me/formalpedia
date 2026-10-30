-- Prove2me | Definitions.Def_OAIQ081S163
-- name    : OAIQ081S163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:07:17.94889+00:00
-- url     : https://prove2.me/theorems/e42f0f56-3f3e-4552-8977-0826bed2d3bb
-- title:
--   Definitions bundle OAIQ081S163 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 2 definitions and 19 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.pairCallResult`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_QueryProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryProgram.lean), [`SubexponentialSAT_SqrtLog_PackingIncidenceProgramRefinement`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingIncidenceProgramRefinement.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyFinalize`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyFinalize.lean), [`SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramAssemblyMerge.lean), [`SubexponentialSAT_SqrtLog_PackingProgramStreamLoop`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramStreamLoop.lean), [`SubexponentialSAT_SqrtLog_PackingProgramStreams`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramStreams.lean), [`SubexponentialSAT_SqrtLog_PackingProgramZip`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingProgramZip.lean), [`SubexponentialSAT_SqrtLog_PerturbationBetaProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PerturbationBetaProgram.lean), [`SubexponentialSAT_Subexp_PairPreparationProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/PairPreparationProgram.lean), [`SubexponentialSAT_Subexp_ScoreBuilderProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/ScoreBuilderProgram.lean), [`SubexponentialSAT_Subexp_SelectorPairProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/SelectorPairProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S143`, `OAIQ081S145`, `OAIQ081S148`, `OAIQ081S149`, `OAIQ081S150` and `OAIQ081S151` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S169`, `OAIQ081S170` and `OAIQ081S171`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S148
import Definitions.Def_OAIQ081S149
import Definitions.Def_OAIQ081S150
import Definitions.Def_OAIQ081S151

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

def pairCallResult (d : State 40 896) : State 40 896 :=
  let sign := parity (d.stacks 835) (parity (d.stacks 834) false)
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 sign,
    Function.update d.stacks 848 [sign]⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorPairProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Selecting and framing both read plans of a vertex pair

The two selector-map calls share a persistent table. Stack 6 initially holds
the left query records and stack 9 the right query records. Stack 11 is an
existing record accumulator. The result prepends one record whose payload is
`frame leftPlanBytes ++ frame rightPlanBytes`.
-/

namespace SubexponentialSAT.Subexp.SelectorPairProgram

open BitProgram StructuredCalls

theorem map_eval (records : List (List Bool × List Bool)) (queries : List (List Bool))
    (regs : Fin 8 → Bool) (right saved acc : List Bool) :
    ∃ n ≤ SelectorMapProgram.budget records queries, ∃ regs',
      Eval (.call mapProgram) n
        (state regs (ProgramEncoding.encodeRecords queries)
          (SelectorProgram.rawRecords records) [] right saved acc)
        (state regs' [] (SelectorProgram.rawRecords records)
          (planBytes records queries) right saved acc) := by
  obtain ⟨n, hn, regs', ht⟩ := SelectorMapProgram.program_trace_from records queries regs
  let a := state regs (ProgramEncoding.encodeRecords queries)
    (SelectorProgram.rawRecords records) [] right saved acc
  let b := state regs' [] (SelectorProgram.rawRecords records)
    (planBytes records queries) right saved acc
  have ha : embedState id stackMap a
      (SelectorMapProgram.inputStateWith regs records queries) = a := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id stackMap_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj; rfl
  have hb : embedState id stackMap a
      (SelectorMapProgram.outputState records queries regs') = b := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id stackMap_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      fin_cases j <;>
        simp_all [stackMap, state, a, b, Fin.exists_fin_succ]
  refine ⟨n, hn, regs', ?_⟩
  have h := eval_call_lifted SelectorMapProgram.program id stackMap a
    Function.injective_id stackMap_injective ht
  simpa only [mapProgram, ha, hb, a, b] using h

/-- Both selections, all moves, and both framing layers are actual fixed
instructions. No preparation operation is hidden in a callback contract. -/
theorem program_trace (records : List (List Bool × List Bool))
    (left right : List (List Bool)) (regs : Fin 8 → Bool) (acc : List Bool) :
    ∃ n ≤ cost records left right, ∃ regs',
      Trace program n
        ((state regs (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
          [] (ProgramEncoding.encodeRecords right) [] acc).withPC (some program.entry))
        ((state regs' [] (SelectorProgram.rawRecords records) [] [] []
          (TupleProgram.prependRecord
            (payload (planBytes records left) (planBytes records right)) acc)).withPC none) := by
  obtain ⟨nl, hnl, r1, h1⟩ := map_eval records left regs
    (ProgramEncoding.encodeRecords right) [] acc
  obtain ⟨r2, h2⟩ := prepareRight_eval r1 (SelectorProgram.rawRecords records)
    (planBytes records left) (ProgramEncoding.encodeRecords right) acc
  obtain ⟨nr, hnr, r3, h3⟩ := map_eval records right r2 [] (planBytes records left).reverse acc
  obtain ⟨r4, h4⟩ := framePair_eval r3 (SelectorProgram.rawRecords records)
    (planBytes records left) (planBytes records right) acc
  have ht := compiled_halt_trace (h1.seq (h2.seq (h3.seq h4))) (6 : Fin 12) 11
  refine ⟨nl + (3 * (planBytes records left).length +
      9 * (ProgramEncoding.encodeRecords right).length + 11 +
        (nr + frameCost (planBytes records left) (planBytes records right))) + 1,
      by dsimp [cost]; omega, r4, ?_⟩
  exact ht

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preparing all selected pair plans once per assignment step

The fixed program preserves the full seed-index records, original pair
records, seed count, and processed counter. It computes the next cutoff,
builds each pair's actual selection table, and emits selected pair records.
The candidate value is not an input to this preparation phase.
-/

namespace SubexponentialSAT.Subexp.PairPreparationProgram

open BitProgram StructuredCalls StackRoutines

theorem selectorCall_eval (a : Data) (records : List (List Bool × List Bool))
    (left right : List (List Bool))
    (hs : ∀ i, a.stacks (selectorStacks i) =
      (SelectorPairProgram.state (fun j => a.regs (selectorRegs j))
        (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
        [] (ProgramEncoding.encodeRecords right) [] (a.stacks 29)).stacks i) :
    ∃ n ≤ SelectorPairProgram.cost records left right, ∃ rf,
      Eval selectorCall n a (selectorAfter a rf records left right) := by
  obtain ⟨n, hn, rf, ht⟩ := SelectorPairProgram.program_trace records left right
    (fun j => a.regs (selectorRegs j)) (a.stacks 29)
  have hin : embedState selectorRegs selectorStacks a
      (SelectorPairProgram.state (fun j => a.regs (selectorRegs j))
        (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
        [] (ProgramEncoding.encodeRecords right) [] (a.stacks 29)) = a := by
    apply SelectorMapProgram.embed_eq _ _ selectorRegs_injective selectorStacks_injective
    · intro i; rfl
    · exact hs
    · intro j hj; rfl
    · intro j hj; rfl
  have hout : embedState selectorRegs selectorStacks a
      (SelectorPairProgram.state rf [] (SelectorProgram.rawRecords records) [] [] []
        (TupleProgram.prependRecord
          (SelectorPairProgram.payload (SelectorPairProgram.planBytes records left)
            (SelectorPairProgram.planBytes records right)) (a.stacks 29))) =
      selectorAfter a rf records left right := by
    apply SelectorMapProgram.embed_eq _ _ selectorRegs_injective selectorStacks_injective
    · intro i
      simp [selectorAfter, prefixRegs, selectorRegs, SelectorPairProgram.state]
    · intro i
      have hi := hs i
      fin_cases i <;> simp_all [selectorAfter, selectorStacks, SelectorPairProgram.state]
    · intro j hj
      have hge : 8 ≤ j.val := by
        by_contra h
        have hlt : j.val < 8 := by omega
        exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
      simp [selectorAfter, prefixRegs, Nat.not_lt.mpr hge]
    · intro j hj
      have h6 : j ≠ 6 := by intro h; subst j; exact hj ⟨6, rfl⟩
      have h9 : j ≠ 9 := by intro h; subst j; exact hj ⟨9, rfl⟩
      have h29 : j ≠ 29 := by intro h; subst j; exact hj ⟨11, rfl⟩
      simp [selectorAfter, h6, h9, h29]
  refine ⟨n, hn, rf, ?_⟩
  have he := eval_call_lifted SelectorPairProgram.program selectorRegs selectorStacks a
    selectorRegs_injective selectorStacks_injective ht
  simpa only [selectorCall, hin, hout] using he

/-- One actual pair-preparation call. Its effect is one framed selected pair
prepended to the existing output list, with the loop and source state framed. -/
theorem callback_eval (ctx : Context) (pair : PlanPair) (acc : List PlanPair)
    (tail : List Bool) :
    ∃ n ≤ callbackCost ctx pair,
      Eval callback n
        (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
          false true false tail (PairScoreProgram.pairBytes pair).reverse)
        (RecordPrograms.state ports
          (baseState ctx (PairScoreProgram.pairRecords
            (selectedPair ctx.seedCount ctx.processedBits.length pair :: acc)))
          false true false tail []) := by
  let l := pair.1.map SelectionTableProgram.unary
  let r := pair.2.map SelectionTableProgram.unary
  let rem := remaining ctx.seedCount ctx.processedBits.length pair
  let table := SelectorProgram.selectionEntries ctx.seedCount rem
  let a0 := RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
    false true false tail (PairScoreProgram.pairBytes pair).reverse
  let a1 := PairPlanPreparation.parsed a0 l r
  let a2 := PairPlanPreparation.unionPrepared a1 l r
  let a3 := copied a2 30 5
  have h0 : Eval PairPlanPreparation.parsePair (PairPlanPreparation.parseCost l r) a0 a1 := by
    apply PairPlanPreparation.parsePair_eval
    · simp only [a0, RecordPrograms.state, ports, Function.update_self]
      rfl
    all_goals simp [a0, RecordPrograms.state, ports, baseState, inputState]
  obtain ⟨n1, hn1, h1⟩ := PairPlanPreparation.buildUnion_eval a1 l r
    (by simp [a1, PairPlanPreparation.parsed])
    (by simp [a1, PairPlanPreparation.parsed])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
  have h2 := copy_eval a2 30 5 (by decide) (by decide) (by decide)
    (by simp [a2, a1, a0, PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  obtain ⟨n3, hn3, rf3, h3⟩ := activeCall_eval a3 (List.range ctx.seedCount)
    (pair.1.reverse ++ pair.2) (true :: ctx.processedBits) (by
      intro i
      fin_cases i <;>
        simp [a3, a2, a1, a0, copied, copyStacks, PairPlanPreparation.unionPrepared,
          PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState,
          activeStacks,
          ActivePlanProgram.indexRecords, seedBytes, l, r,
          SelectionTableProgram.unary, List.map_append, List.map_reverse, activeUnary_eq])
  let a4 := activeAfter a3 rf3 (List.range ctx.seedCount)
    (pair.1.reverse ++ pair.2) (true :: ctx.processedBits)
  let a5 := cleared a4 6
  let a6 := moved a5 11 0
  let a7 := copied a6 32 2
  let a8 := tableReset a7
  have h4 := clear_eval a4 6
  have h5 := move_eval a5 11 0 (by decide) (by decide) (by decide) (by
    simp [a5, a4, a3, a2, a1, a0, cleared, clearStacks, activeAfter, copied, copyStacks,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  have h6 := copy_eval a6 32 2 (by decide) (by decide) (by decide) (by
    simp [a6, a5, a4, a3, a2, a1, a0, moved, cleared, clearStacks, activeAfter,
      copied, copyStacks, PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  have h7 := resetTable_eval a7
  have h8 := tableCall_eval a8 ctx.seedCount rem
    (by intro i; simp [a8, tableReset, tableRegs])
    (by
      intro i
      fin_cases i <;>
        simp [a8, a7, a6, a5, a4, a3, a2, a1, a0, tableReset, moved,
          copied, copyStacks, cleared, clearStacks, activeAfter,
          PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
          RecordPrograms.state, ports, baseState, inputState, tableStacks,
          SelectionTableProgram.inputState, SelectionTableProgram.baseState,
          SelectionTableProgram.state, SelectionTableProgram.ports,
          SelectionTableProgram.indexRecords, SelectionTableProgram.unary,
          ActivePlanProgram.indexRecords, rem, remaining, activeUnary_eq])
  let a9 := tableAfter a8 ctx.seedCount rem
  let a10 := cleared a9 2
  have h9 := clear_eval a9 2
  obtain ⟨n10, hn10, h10⟩ := PairPlanPreparation.reverseQueries_eval a10 l r
    (by simp [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, cleared, clearStacks,
      tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed])
    (by simp [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, cleared, clearStacks,
      tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed])
    (by simp [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0, cleared, clearStacks,
      tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  let a11 := PairPlanPreparation.queriesPrepared a10 l r
  obtain ⟨n11, hn11, rf11, h11⟩ := selectorCall_eval a11 table l.reverse r.reverse (by
    intro i
    fin_cases i <;>
      simp [a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0,
        PairPlanPreparation.queriesPrepared, PairPlanPreparation.unionPrepared,
        PairPlanPreparation.parsed, cleared, clearStacks, tableAfter, tableReset,
        moved, copied, copyStacks, activeAfter, RecordPrograms.state, ports,
        baseState, inputState, selectorStacks, SelectorPairProgram.state, table,
        SelectionTableProgram.tableBytes_eq_rawRecords])
  let a12 := selectorAfter a11 rf11 table l.reverse r.reverse
  let a13 := cleared a12 3
  let a14 := innerReset a13
  have h12 := clear_eval a12 3
  have h13 := resetInner_eval a13
  have hout : a14 = RecordPrograms.state ports
      (baseState ctx (PairScoreProgram.pairRecords
        (selectedPair ctx.seedCount ctx.processedBits.length pair :: acc)))
      false true false tail [] := by
    change callbackFinal ctx pair acc tail rf3 rf11 = _
    exact callbackFinal_eq ctx pair acc tail rf3 rf11
  have hrun := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq
    (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (.base (.skip a14)))))))))))))))
  rw [hout] at hrun
  refine ⟨_, ?_, by simpa only [callback, sequence] using hrun⟩
  dsimp [callbackCost]
  simp [ a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0,
    cleared, clearStacks, selectorAfter, PairPlanPreparation.queriesPrepared,
    tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
    PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
    RecordPrograms.state, ports, baseState, inputState,
    ActivePlanProgram.indexRecords,
    SelectionTableProgram.unary, activeUnary_eq, l, r, table, rem, remaining]
    at hn1 hn3 hn10 hn11 ⊢
  omega

/-- The outer scan is the actual framed-record loop. It invokes the proved
pair preparation exactly once per raw pair. -/
theorem loop_eval (ctx : Context) (pairs acc : List PlanPair) (suffix : List Bool) :
    ∃ n ≤ loopCost ctx pairs,
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords acc))
          (pairs.map PairScoreProgram.pairBytes) suffix)
        (RecordPrograms.state ports
          (baseState ctx (PairScoreProgram.pairRecords
            ((selectedPairs ctx.seedCount ctx.processedBits.length pairs).reverse ++ acc)))
          false true false suffix []) := by
  induction pairs generalizing acc with
  | nil =>
      refine ⟨1, le_rfl, ?_⟩
      simpa [loopCost, selectedPairs, RecordPrograms.afterTag] using
        (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
            false true false suffix []) (by simp))
  | cons pair pairs ih =>
      let tail := Encoding.encodeList id (pairs.map PairScoreProgram.pairBytes) ++ suffix
      let nextAcc := selectedPair ctx.seedCount ctx.processedBits.length pair :: acc
      have hreader : Eval (RecordPrograms.reader ports) (6 * (PairScoreProgram.pairBytes pair).length + 4)
          (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords acc))
            ((pair :: pairs).map PairScoreProgram.pairBytes) suffix)
          (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
            false true false tail (PairScoreProgram.pairBytes pair).reverse) := by
        simpa [RecordPrograms.afterTag, tail] using
          RecordPrograms.reader_eval ports (baseState ctx (PairScoreProgram.pairRecords acc))
            (PairScoreProgram.pairBytes pair) tail [] true true false
      obtain ⟨nc, hnc, hcallback⟩ := callback_eval ctx pair acc tail
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords nextAcc))
            false true false tail [])
          (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords nextAcc))
            (pairs.map PairScoreProgram.pairBytes) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports (baseState ctx (PairScoreProgram.pairRecords nextAcc))
          (pairs.map PairScoreProgram.pairBytes) suffix false true
      obtain ⟨nr, hnr, hrest⟩ := ih nextAcc
      have hbody := hreader.seq (hcallback.seq hbranch)
      have hguard : (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords acc))
          ((pair :: pairs).map PairScoreProgram.pairBytes) suffix).regs ports.tag = true := by
        simp [RecordPrograms.afterTag]
      have hrun := Eval.while_true hguard hbody hrest
      refine ⟨_, ?_, by simpa [RecordPrograms.loop, RecordPrograms.body, selectedPairs, nextAcc,
          List.reverse_cons, List.append_assoc] using hrun⟩
      dsimp [loopCost]
      omega

theorem iterate_eval (ctx : Context) (pairs acc : List PlanPair) (suffix : List Bool)
    (v pr f : Bool) :
    ∃ n ≤ 2 + loopCost ctx pairs,
      Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
          v pr f (PairScoreProgram.pairRecords pairs ++ suffix) [])
        (RecordPrograms.state ports
          (baseState ctx (PairScoreProgram.pairRecords
            ((selectedPairs ctx.seedCount ctx.processedBits.length pairs).reverse ++ acc)))
          false true false suffix []) := by
  obtain ⟨n, hn, hloop⟩ := loop_eval ctx pairs acc suffix
  have hset := RecordPrograms.set_found_eval ports
    (baseState ctx (PairScoreProgram.pairRecords acc)) v pr f false
    (PairScoreProgram.pairRecords pairs ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports
    (baseState ctx (PairScoreProgram.pairRecords acc))
    (pairs.map PairScoreProgram.pairBytes) suffix v pr
  refine ⟨1 + (1 + n), by omega, ?_⟩
  simpa [RecordPrograms.iterate, PairScoreProgram.pairRecords, ProgramEncoding.encodeRecords]
    using hset.seq (hpop.seq hloop)

theorem command_eval (ctx : Context) (regs : Fin 16 → Bool) :
    ∃ n, n + 1 ≤ traceBound ctx ∧ Eval command n (inputState ctx regs) (outputState ctx) := by
  let a0 := inputState ctx regs
  let a1 := copied a0 31 20
  let a2 := copied a1 33 7
  let a3 := TupleProgram.pushedState 7 0 true a2
  let a4 := TupleProgram.pushedState 29 0 false a3
  let a5 : Data := ⟨fun _ => false, a4.stacks⟩
  let selected := selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs
  let a6 := RecordPrograms.state ports
    (baseState ctx (PairScoreProgram.pairRecords selected.reverse)) false true false [] []
  let a7 := cleared a6 7
  let a8 := TupleProgram.pushedState 28 0 false a7
  let a9 := PairPlanPreparation.reversed a8 29 28 (PairScoreProgram.pairRecords selected)
  let a10 := moved a9 28 29
  have h0 := copy_eval a0 31 20 (by decide) (by decide) (by decide)
    (by simp [a0, inputState])
  have h1 := copy_eval a1 33 7 (by decide) (by decide) (by decide)
    (by simp [a1, a0, copied, copyStacks, inputState])
  have h2 := TupleProgram.pushConst_eval (7 : Fin 34) (0 : Fin 16) true a2
  have h3 := TupleProgram.pushConst_eval (29 : Fin 34) (0 : Fin 16) false a3
  have h4 := resetAll_eval a4
  have ha5 : a5 = RecordPrograms.state ports
      (baseState ctx (PairScoreProgram.pairRecords [])) false false false
      (PairScoreProgram.pairRecords ctx.pairs ++ []) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [ ports, baseState]
    · funext j
      fin_cases j <;>
        simp [ a4, a3, a2, a1, a0, copied, copyStacks,
          inputState, ports, baseState, PairScoreProgram.pairRecords,
          ProgramEncoding.encodeRecords, Encoding.encodeList]
  obtain ⟨ni, hni, hi⟩ := iterate_eval ctx ctx.pairs [] [] false false false
  have hi' : Eval (RecordPrograms.iterate ports callback) ni a5 a6 := by
    rw [ha5]
    simpa [a6, selected] using hi
  have h5 := clear_eval a6 7
  have h6 := TupleProgram.pushConst_eval (28 : Fin 34) (0 : Fin 16) false a7
  obtain ⟨nr, hnr, hr⟩ := PairPlanPreparation.reverse_eval a8 29 28 (by decide)
    (selected.map PairScoreProgram.pairBytes).reverse []
    (by simp [a8, a7, a6, cleared, clearStacks,
      RecordPrograms.state, ports, baseState, PairScoreProgram.pairRecords,
      List.map_reverse])
    (by simp [a8, a7, a6, cleared, clearStacks,
      RecordPrograms.state, ports, baseState, inputState,
      ProgramEncoding.encodeRecords, Encoding.encodeList])
    (by simp [a8, a7, a6, cleared, clearStacks,
      RecordPrograms.state, ports, baseState, inputState])
  have hr' : Eval reverseCall nr a8 a9 := by
    simpa [reverseCall, PairPlanPreparation.reverseRecords, tableRegs, reverseStacks,
      PairPlanPreparation.smallRegs, PairPlanPreparation.reversePorts,
      a9, PairScoreProgram.pairRecords] using hr
  have h7 := move_eval a9 28 29 (by decide) (by decide) (by decide)
    (by simp [a9, a8, a7, a6, PairPlanPreparation.reversed,
      cleared, clearStacks, RecordPrograms.state, ports, baseState, inputState])
  have h8 := resetAll_eval a10
  have hout : (⟨fun _ => false, a10.stacks⟩ : Data) = outputState ctx := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;>
      simp [a10, a9, a8, a7, a6, moved, copied, copyStacks, cleared, clearStacks,
        PairPlanPreparation.reversed, RecordPrograms.state,
        ports, baseState, inputState, selected]
  have hrun := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (hi'.seq (h5.seq
    (h6.seq (hr'.seq (h7.seq (h8.seq (.base (.skip _))))))))))))
  rw [hout] at hrun
  refine ⟨_, ?_, by simpa only [command, sequence] using hrun⟩
  simp [ a9, a8, a7, a6, a1, a0,
    PairPlanPreparation.reversed, copied, copyStacks,
    cleared, clearStacks, RecordPrograms.state, ports, baseState, inputState,
    traceBound, selected, PairScoreProgram.pairRecords, List.map_reverse] at hnr ⊢
  omega

/-- Full halted execution of the concrete once-per-step preparation routine.
No selected-plan table is supplied to the machine as a precomputed input. -/
theorem program_runsIn (ctx : Context) (regs : Fin 16 → Bool) :
    RunsIn program (traceBound ctx)
      ((inputState ctx regs).withPC (some program.entry))
      ((outputState ctx).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval ctx regs
  exact ⟨n + 1, hn, by simpa [program] using compiled_halt_trace he 31 29⟩

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual global candidate-score builder

Pair read plans are prepared once for the current processed position. The
candidate loop then executes the local collision enumeration and emits scores
in candidate order. A final fixed routine restores the temporary table ports.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls

theorem preparation_eval (pre : PairPreparationProgram.Context) (d : Data)
    (hinput : ∀ i, (PairPreparationProgram.inputState pre d.regs).stacks i =
      d.stacks (preparationPorts i)) :
    ∃ n ≤ PairPreparationProgram.traceBound pre,
      Eval preparation n d (prepared pre d) := by
  obtain ⟨n, hn, ht⟩ := PairPreparationProgram.program_runsIn pre d.regs
  have hout : (PairPreparationProgram.outputState pre).stacks =
      Function.update (PairPreparationProgram.inputState pre d.regs).stacks 29 (preparedBytes pre) := by
    rfl
  have he := call_lifted_update PairPreparationProgram.program preparationPorts
    preparationPorts_injective d (PairPreparationProgram.inputState pre d.regs)
    (PairPreparationProgram.outputState pre) 29 (preparedBytes pre) rfl hinput hout ht
  exact ⟨n, hn, by
    simpa [preparation, prepared, preparationPorts,
      PairPreparationProgram.outputState] using he⟩

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact conditional-incidence numerators produced by the fixed raw scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing

section Refinement
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

theorem candidateScore_raw_perm (alphabet : List (Word r Q)) (a : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw other : List PlanPair)
    (d : ScoreBuilderProgram.Data) (candidate : List Bool) (hp : raw.Perm other) :
    CandidateScoreProgram.candidateScore (context alphabet a fixed n M raw d) candidate =
    CandidateScoreProgram.candidateScore (context alphabet a fixed n M other d) candidate := by
  apply CandidateScoreRefinement.score_perm
  exact hp.map (PairPreparationProgram.selectedPair M (d.stacks 19).length)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem scoreBytes_eq (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n indices.length raw d) =
      ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) := by
  unfold ScoreBuilderProgram.scoreBytes CandidateScoreProgram.scoreRecords
  apply congrArg ProgramEncoding.encodeRecords
  change (((a::tail).map ReadPlan.encodeWord).map _) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro candidate _
  apply congrArg UnaryCompare.encode
  rw [candidateScore_raw_perm (a::tail) a fixed n indices.length raw _ d _ hraw]
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have h := candidate_incidenceScore ivar factor (a::tail) pairs indices hi a candidate
    fixed n (d.stacks 10) (d.stacks 19) hsize hw
  simpa only [context, ScoreBuilderRawInput.context, hm.processed, incidenceNumerator,
    List.length_cons] using h

end Refinement
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreams
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 theorem emit_ready_eval (regs : Fin 8 → Bool) (wi wh score tail acc output : List Bool) :
    ∃ rf, Eval emit (4*score.length+8)
      (state regs wi wh [] [] score tail acc output)
      (ready rf wi wh tail (CandidateScoreProgram.reverseRecord score acc) output) := by
  let d := state regs wi wh [] [] score tail acc output
  obtain ⟨e, he, he4, he9, hef⟩ := emit_eval d
  have hee : e = ready e.regs wi wh tail (CandidateScoreProgram.reverseRecord score acc) output :=
    state_ready_of_frame regs wi wh score tail acc output e he4 he9 hef
  exact ⟨e.regs,eval_congr_output he hee⟩

 theorem pairCommand_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (tail acc output : List Bool) :
    ∃ t ≤ pairBudget wi wh p, ∃ rf,
      Eval pairCommand t (ready regs wi wh (payload p ++ tail) acc output)
        (ready rf wi wh tail
          (CandidateScoreProgram.reverseRecord (List.replicate (value wi wh p) false) acc) output) := by
  obtain ⟨r₁,h₁⟩ := readFields_eval regs wi wh p tail acc output
  obtain ⟨n,hn,r₂,h₂⟩ := weighted_eval r₁ wi wh p tail acc output
  obtain ⟨r₃,h₃⟩ := clearCounts_eval r₂ wi wh p (List.replicate (value wi wh p) false) tail acc output
  obtain ⟨r₄,h₄⟩ := emit_ready_eval r₃ wi wh (List.replicate (value wi wh p) false) tail acc output
  refine ⟨_, ?_, r₄, h₁.seq (h₂.seq (h₃.seq h₄))⟩
  simp only [List.length_replicate]
  unfold pairBudget
  omega
end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreamLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The real dynamic loop over paired candidate counts. The pair list occurs
only in the input specification; the finite program reads runtime list tags. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 theorem loop_eval (ps : List (ℕ × ℕ)) (regs : Fin 8 → Bool)
    (wi wh acc output : List Bool) (hf : regs 7 = flag ps) :
    ∃ n ≤ loopBudget wi wh ps, ∃ rf,
      Eval loop n (ready regs wi wh (afterSource ps) acc output)
        (ready rf wi wh [] ((resultBody wi wh ps).reverse ++ acc) output) := by
  induction ps generalizing regs acc with
  | nil =>
    exact ⟨1, le_rfl, regs, Eval.while_false hf⟩
  | cons p ps ih =>
    obtain ⟨n, hn, rp, hp⟩ := pairCommand_eval regs wi wh p (pairsBytes ps) acc output
    obtain ⟨rt, ht, hft⟩ := tag_eval rp wi wh ps
      (CandidateScoreProgram.reverseRecord (List.replicate (value wi wh p) false) acc) output
    obtain ⟨m, hm, rf, hr⟩ := ih rt
      (CandidateScoreProgram.reverseRecord (List.replicate (value wi wh p) false) acc) hft
    have h := Eval.while_true hf (hp.seq ht) hr
    refine ⟨n+1+m+1, by unfold loopBudget; omega, rf, ?_⟩
    simpa [loop,afterSource,resultBody,CandidateScoreProgram.reverseRecord,
      List.reverse_append,List.append_assoc] using h

 theorem command_eval (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    ∃ n ≤ streamBudget wi wh ps, ∃ rf,
      Eval command n (ready regs wi wh (pairsBytes ps) [] [])
        (ready rf wi wh [] [] (SubexponentialSAT.ProgramEncoding.encodeRecords (scores wi wh ps))) := by
  obtain ⟨rt, ht, hft⟩ := tag_eval regs wi wh ps [] []
  obtain ⟨n, hn, rl, hl⟩ := loop_eval ps rt wi wh [] [] hft
  simp only [List.append_nil] at hl
  obtain ⟨rf, hf⟩ := finish_eval rl wi wh (resultBody wi wh ps).reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil,resultBody_records] at hf
  refine ⟨1+(n+(3*(resultBody wi wh ps).length+8)), by unfold streamBudget; omega,
    rf, ht.seq (hl.seq hf)⟩

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual pairing and weighting of two candidate-ordered unary score streams.
This is one fixed finite program; no precomputed pair list is an input premise. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem command_eval (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    ∃ n ≤ budget wi wh ps, ∃ e : Data,
      Eval command n (input regs wi wh ps) e ∧
      e.stacks 8 = SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 12 = wi ∧ e.stacks 13 = wh ∧
      (∀ j, j ≠ 8 → j ≠ 12 → j ≠ 13 → e.stacks j = []) := by
  obtain ⟨rz, hz⟩ := SubexponentialSAT.SubexpInputZip.program_trace (rawPairs ps) regs [] [] []
  have hf : SubexponentialSAT.SubexpInputZip.rowWords (rawPairs ps) = firstScores ps := by
    simp [SubexponentialSAT.SubexpInputZip.rowWords,rawPairs,firstScores,List.map_map,Function.comp_def]
  have hh : SubexponentialSAT.SubexpInputZip.inputWords (rawPairs ps) = secondScores ps := by
    simp [SubexponentialSAT.SubexpInputZip.inputWords,rawPairs,secondScores,List.map_map,Function.comp_def]
  rw [hf,hh,rawPairs_bytes] at hz
  simp only [List.append_nil] at hz
  have hzip := eval_call_lifted SubexponentialSAT.SubexpInputZip.program id zipPorts (base regs wi wh)
    Function.injective_id zipPorts_injective hz
  change Eval pair _ (input regs wi wh ps) (middle rz regs wi wh ps) at hzip
  obtain ⟨n, hn, rs, hs⟩ := Streams.command_eval rz wi wh ps
  have hs' : Eval Streams.command n (projectState id scorePorts (middle rz regs wi wh ps))
      (Streams.ready rs wi wh [] [] (SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps))) := by
    rw [middle_projection]
    exact hs
  have hweight := eval_liftCommand_from_state Streams.command 8 10 id scorePorts
    (middle rz regs wi wh ps) Function.injective_id scorePorts_injective hs'
  refine ⟨_, ?_, _, hzip.seq hweight, ?_, ?_, ?_, ?_⟩
  · unfold budget
    simpa only [rawPairs,List.length_map,Nat.add_assoc] using Nat.add_le_add_left (Nat.add_le_add_right hn 1)
      (26*SubexponentialSAT.SubexpInputZip.inputBits (rawPairs ps)+53*(rawPairs ps).length+12)
  · exact embedState_stack id scorePorts _ _ scorePorts_injective 10
  · exact embedState_stack id scorePorts _ _ scorePorts_injective 0
  · exact embedState_stack id scorePorts _ _ scorePorts_injective 2
  · exact final_clean rz regs rs wi wh ps

end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete stream merger into the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem merge_eval (wi wh : List Bool) (ps : List (ℕ × ℕ)) (d : Data)
    (h : MergeInput wi wh ps d) :
    ∃ t ≤ Zip.budget wi wh ps+1, ∃ e : Data,
      Eval merge t d e ∧
      e.stacks 7 = ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 0=[] ∧ e.stacks 12=[] ∧
      (∀ j, j ≠ 0 → j ≠ 7 → j ≠ 12 → e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,b,hb,ho,hi,hh,hf⟩ := Zip.command_eval (d.regs ∘ mergeRegisters) wi wh ps
  have hb' : Eval Zip.command t (projectState mergeRegisters mergePorts d) b := by
    rw [merge_projection wi wh ps d h]
    exact hb
  let e := embedState mergeRegisters mergePorts d b
  have he := eval_liftCommand_from_state Zip.command 0 8 mergeRegisters mergePorts d
    mergeRegisters_injective mergePorts_injective hb'
  have hs (i : Fin 14) : e.stacks (mergePorts i)=b.stacks i :=
    embedState_stack mergeRegisters mergePorts d b mergePorts_injective i
  refine ⟨t+1,Nat.add_le_add_right ht 1,e,he,(hs 8).trans ho,
    (hs 0).trans (hf 0 (by decide) (by decide) (by decide)),
    (hs 1).trans (hf 1 (by decide) (by decide) (by decide)),?_⟩
  intro j hj0 hj7 hj12
  by_cases hm : ∃ i,mergePorts i=j
  · obtain ⟨i,rfl⟩ := hm
    rw [hs,h i,Zip.input_stacks]
    fin_cases i <;> first
      | exact False.elim (hj0 rfl)
      | exact False.elim (hj7 rfl)
      | exact False.elim (hj12 rfl)
      | exact hi
      | exact hh
      | exact hf _ (by decide) (by decide) (by decide)
  · exact embedState_stack_frame mergeRegisters mergePorts d b j hm

theorem finishMerged_eval (wi wh : List Bool) (ps : List (ℕ × ℕ)) (d : Data)
    (h : MergeInput wi wh ps d) :
    ∃ t ≤ Zip.budget wi wh ps+1+
        6*(ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length+6,
      ∃ e : Data, Eval (.seq merge finishMerged) t d e ∧
      e.stacks 0=ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
      e.stacks 12=[] ∧
      (∀ j, j ≠ 0 → j ≠ 12 → e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,b,hb,ho,h0,h12,hf⟩ := merge_eval wi wh ps d h
  have hd1 : d.stacks 1=[] := by
    have hh := h 2
    simpa [mergePorts,Zip.input_stacks] using hh
  have hd7 : d.stacks 7=[] := by
    have hh := h 8
    simpa [mergePorts,Zip.input_stacks] using hh
  have hb1 : b.stacks 1=[] := (hf 1 (by decide) (by decide) (by decide)).trans hd1
  have hm := move_eval b 7 0 1 (by decide) (by decide) (by decide) h0 hb1
  refine ⟨t+(6*(b.stacks 7).length+6),?_,moved b 7 0,hb.seq hm,?_,?_,?_⟩
  · rw [ho]
    omega
  · simpa [moved] using ho
  · simpa [moved] using h12
  · intro j hj0 hj12
    by_cases hj7 : j=7
    · subst j
      simp [moved,hd7]
    · simpa [moved,hj0,hj7] using hf j hj0 hj7 hj12

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyFinalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end native weighting, serialization, and scratch cleanup. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem weightAndMerge_eval (d : Data) (ps : List (ℕ × ℕ)) (h : inputPairScores d ps) :
    ∃ wi wh : List Bool,
      SubexponentialSAT.BinaryArithmetic.toNat wi=(SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 20))^2*
        (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 21))^2 ∧
      SubexponentialSAT.BinaryArithmetic.toNat wh=8*(SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 22))^2*
        (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 23))^2 ∧
      wi.length ≤ 2*(d.stacks 20).length+2*(d.stacks 21).length+3 ∧
      wh.length ≤ 2*(d.stacks 22).length+2*(d.stacks 23).length+6 ∧
      ∃ t ≤ 500*(2*dataLength d+4)^2+1+Zip.budget wi wh ps+
        6*(ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length+
        2*wi.length+2*wh.length+14,
        ∃ e : Data, Eval weightAndMerge t d e ∧
          e.stacks 0=ProgramEncoding.encodeRecords (Streams.scores wi wh ps) ∧
          e.stacks 12=[] ∧
          (∀ j,j≠0→j≠12→e.stacks j=d.stacks j) := by
  have hw : WeightReady d := by
    intro i hi
    fin_cases i <;> try (norm_num at hi)
    all_goals simpa [weightPorts] using h.2.2 _ (by simp)
  obtain ⟨tw,htw,b,hb,hi,hh,hli,hlh,hbf⟩ := weights_eval d hw
  obtain ⟨tm,htm,c,hc,ho,h12,hcf⟩ := finishMerged_eval
    (b.stacks 15) (b.stacks 16) ps b (weights_mergeInput d b ps h hbf)
  have hc15 : c.stacks 15=b.stacks 15 := hcf _ (by decide) (by decide)
  have hc16 : c.stacks 16=b.stacks 16 := hcf _ (by decide) (by decide)
  let c₁ : Data := ⟨readRegs c.regs 0 1 none,Function.update c.stacks 15 []⟩
  let c₂ : Data := ⟨readRegs c₁.regs 0 1 none,Function.update c₁.stacks 16 []⟩
  have hcl1 : Eval (clearWeight 15) (2*(c.stacks 15).length+3) c c₁ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 15 0 1 c.regs c.stacks)
  have hcl2 : Eval (clearWeight 16) (2*(c₁.stacks 16).length+3) c₁ c₂ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 16 0 1 c₁.regs c₁.stacks)
  refine ⟨b.stacks 15,b.stacks 16,hi,hh,hli,hlh,
    tw+(tm+((2*(c.stacks 15).length+3)+(2*(c₁.stacks 16).length+3))),?_,
    c₂,hb.seq (hc.seq (hcl1.seq hcl2)),?_,?_,?_⟩
  · have h16 : c₁.stacks 16=b.stacks 16 := by simpa [c₁] using hc16
    rw [hc15,h16]
    omega
  · simpa [c₂,c₁] using ho
  · simpa [c₂,c₁] using h12
  · intro j hj0 hj12
    by_cases hj15 : j=15
    · subst j
      simp [c₂,c₁,h.2.2 15 (by simp)]
    by_cases hj16 : j=16
    · subst j
      simp [c₂,h.2.2 16 (by simp)]
    · simp only [c₂,c₁,Function.update_of_ne hj15,Function.update_of_ne hj16]
      exact (hcf j hj0 hj12).trans (hbf j hj15 hj16)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

def step : Code := .seq readRow (.seq popChoice (.ite 0 selected skip))

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end


