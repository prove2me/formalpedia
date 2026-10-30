-- Prove2me | Definitions.Def_OAIQ081S150
-- name    : OAIQ081S150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:55:45.613345+00:00
-- url     : https://prove2.me/theorems/275f197a-715a-4b4e-87f1-19cbd29456e0
-- title:
--   Definitions bundle OAIQ081S150 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 23 definitions, 1 inductive type or structure and 29 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.MergeInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.middle`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.CallerInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.finishCoordinate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.highConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.initializeTarget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.readFlag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.scanStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.peekRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.skip`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.iteration`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.repeatState`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.callbackFinal`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_PackingIncidenceProgram`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights`, `SubexponentialSAT_SqrtLog_PackingProgramStreamLoop`, `SubexponentialSAT_SqrtLog_PackingProgramStreams`, `SubexponentialSAT_SqrtLog_PackingProgramZip`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeScan`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyScan`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyShift`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyStaging`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgramPadding`, `SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun`, `SubexponentialSAT_SqrtLog_PerturbationProgramTraversal`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPreparationProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S132`, `OAIQ081S133`, `OAIQ081S134`, `OAIQ081S135` and `OAIQ081S136` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S163`, `OAIQ081S164` and `OAIQ081S165`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.initializeTarget_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.streaming_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.initializeTarget_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_shift_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.origin_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Padding.streaming_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S130
import Definitions.Def_OAIQ081S131
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S133
import Definitions.Def_OAIQ081S134
import Definitions.Def_OAIQ081S135
import Definitions.Def_OAIQ081S136

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Computing the active completion positions

A fixed program filters a runtime list of unary seed positions. It retains a
position precisely when it is at least the runtime threshold and belongs to
the runtime pair read plan. The plan and threshold are preserved. Applying the
program to the complete ascending seed list gives a duplicate-free completion
plan in ascending order.
-/

namespace SubexponentialSAT.Subexp.ActivePlanProgram

open BitProgram StructuredCalls StackRoutines

/-- Complete execution of the fixed filter, including the order-restoring
pass. Its output is the encoded filtered list in the original input order. -/
theorem command_eval (records seeds : List (List Bool)) (threshold : List Bool) (regs : Regs) :
    ∃ n ≤ sourceBound records seeds threshold - 1, ∃ rf : Regs,
      Eval command n
        (state regs (Encoding.encodeList id seeds) (Encoding.encodeList id records) threshold [] [] [])
        (state rf [] (Encoding.encodeList id records) threshold [] []
          (Encoding.encodeList id (seeds.filter (keep records threshold)))) := by
  obtain ⟨n, hn, rf, he⟩ := filter_eval records seeds threshold (Function.update regs 0 false)
  obtain ⟨m, hm, hr⟩ := reverse_eval (seeds.filter (keep records threshold)).reverse []
    (Encoding.encodeList id records) threshold (Function.update rf 0 false)
  rw [List.reverse_reverse] at hr
  have hinit := initAccumulator_eval regs (Encoding.encodeList id seeds) (Encoding.encodeList id records) threshold
  have hout := initializeOutput_eval rf [] (Encoding.encodeList id records) threshold
    (Encoding.encodeList id (seeds.filter (keep records threshold)).reverse)
  refine ⟨_, ?_, flags (Function.update rf 0 false) false true false,
    hinit.seq (he.seq (hout.seq hr))⟩
  have hlen := encoded_filter_length_le seeds (keep records threshold)
  rw [encoded_reverse_length] at hm
  dsimp [sourceBound]
  omega

/-- The actual program preserves an arbitrary raw threshold word and uses
only its length. In particular, a processed-counter prefix need not contain
canonical bit values. -/
theorem program_runsIn_threshold (regs : Regs) (seeds plan : List ℕ) (threshold : List Bool) :
    ∃ rf : Regs, RunsIn program (traceBoundThreshold seeds plan threshold)
      ((inputStateThreshold regs seeds plan threshold).withPC (some program.entry))
      ((outputStateThreshold rf seeds plan threshold).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval (indexRecords plan) (indexRecords seeds) threshold regs
  rw [filter_indexRecords_threshold] at he
  refine ⟨rf, n + 1, ?_, ?_⟩
  · have hpos : 0 < traceBoundThreshold seeds plan threshold := by
      simp [traceBoundThreshold, sourceBound]
    dsimp [traceBoundThreshold] at *
    omega
  · simpa [program, inputStateThreshold, outputStateThreshold, ProgramEncoding.encodeRecords] using
      compiled_halt_trace he 5 11

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem activeCall_eval (a : Data) (seeds plan : List ℕ) (threshold : List Bool)
    (hs : ∀ i, a.stacks (activeStacks i) =
      (ActivePlanProgram.inputStateThreshold (fun j => a.regs (activeRegs j))
        seeds plan threshold).stacks i) :
    ∃ n ≤ ActivePlanProgram.traceBoundThreshold seeds plan threshold, ∃ rf,
      Eval activeCall n a (activeAfter a rf seeds plan threshold) := by
  obtain ⟨rf, n, hn, ht⟩ := ActivePlanProgram.program_runsIn_threshold
    (fun j => a.regs (activeRegs j)) seeds plan threshold
  have hin : embedState activeRegs activeStacks a
      (ActivePlanProgram.inputStateThreshold (fun j => a.regs (activeRegs j))
        seeds plan threshold) = a := by
    apply SelectorMapProgram.embed_eq _ _ activeRegs_injective activeStacks_injective
    · intro i; rfl
    · exact hs
    · intro j hj; rfl
    · intro j hj; rfl
  have hout : embedState activeRegs activeStacks a
      (ActivePlanProgram.outputStateThreshold rf seeds plan threshold) =
      activeAfter a rf seeds plan threshold := by
    apply SelectorMapProgram.embed_eq _ _ activeRegs_injective activeStacks_injective
    · intro i
      simp [activeAfter, prefixRegs, activeRegs
        ]
    · intro i
      have hi := hs i
      fin_cases i <;>
        simp_all [activeAfter, activeStacks, ActivePlanProgram.inputStateThreshold,
          ActivePlanProgram.outputStateThreshold, ActivePlanProgram.state]
    · intro j hj
      have hge : 10 ≤ j.val := by
        by_contra h
        have hlt : j.val < 10 := by omega
        exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
      simp [activeAfter, prefixRegs, Nat.not_lt.mpr hge]
    · intro j hj
      have h5 : j ≠ 5 := by
        intro h; subst j; exact hj ⟨5, rfl⟩
      have h11 : j ≠ 11 := by
        intro h; subst j; exact hj ⟨11, rfl⟩
      simp [activeAfter, h5, h11]
  refine ⟨n, hn, rf, ?_⟩
  have he := eval_call_lifted ActivePlanProgram.program activeRegs activeStacks a
    activeRegs_injective activeStacks_injective ht
  simpa only [activeCall, hin, hout] using he

theorem selectedPayload_eq (M processed : ℕ) (pair : PlanPair) :
    SelectorPairProgram.payload
      (SelectorPairProgram.planBytes (SelectorProgram.selectionEntries M (remaining M processed pair))
        (pair.1.reverse.map SelectorProgram.unaryIndex))
      (SelectorPairProgram.planBytes (SelectorProgram.selectionEntries M (remaining M processed pair))
        (pair.2.reverse.map SelectorProgram.unaryIndex)) =
    PairScoreProgram.pairBytes (selectedPair M processed pair) := by
  rw [SelectorPairProgram.planBytes_selection, SelectorPairProgram.planBytes_selection]
  simp [SelectorPairProgram.payload, PairScoreProgram.pairBytes, selectedPair,
    CollisionStreamProgram.planBytes, GatherProgram.indexRecords, List.map_map,
    SelectorProgram.unaryIndex, Function.comp_def]

def callbackFinal (ctx : Context) (pair : PlanPair) (acc : List PlanPair)
    (tail : List Bool) (rf3 : Fin 10 → Bool) (rf11 : Fin 8 → Bool) : Data :=
  let l := pair.1.map SelectionTableProgram.unary
  let r := pair.2.map SelectionTableProgram.unary
  let rem := remaining ctx.seedCount ctx.processedBits.length pair
  let table := SelectorProgram.selectionEntries ctx.seedCount rem
  let a0 := RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
    false true false tail (PairScoreProgram.pairBytes pair).reverse
  let a1 := PairPlanPreparation.parsed a0 l r
  let a2 := PairPlanPreparation.unionPrepared a1 l r
  let a3 := copied a2 30 5
  let a4 := activeAfter a3 rf3 (List.range ctx.seedCount)
    (pair.1.reverse ++ pair.2) (true :: ctx.processedBits)
  let a5 := cleared a4 6
  let a6 := moved a5 11 0
  let a7 := copied a6 32 2
  let a8 := tableReset a7
  let a9 := tableAfter a8 ctx.seedCount rem
  let a10 := cleared a9 2
  let a11 := PairPlanPreparation.queriesPrepared a10 l r
  let a12 := selectorAfter a11 rf11 table l.reverse r.reverse
  let a13 := cleared a12 3
  innerReset a13

theorem callbackFinal_eq (ctx : Context) (pair : PlanPair) (acc : List PlanPair)
    (tail : List Bool) (rf3 : Fin 10 → Bool) (rf11 : Fin 8 → Bool) :
    callbackFinal ctx pair acc tail rf3 rf11 = RecordPrograms.state ports
      (baseState ctx (PairScoreProgram.pairRecords
        (selectedPair ctx.seedCount ctx.processedBits.length pair :: acc)))
      false true false tail [] := by
  have hpay := selectedPayload_eq ctx.seedCount ctx.processedBits.length pair
  have hpay' : SelectorPairProgram.payload
      (SelectorPairProgram.planBytes
        (SelectorProgram.selectionEntries ctx.seedCount
          (remaining ctx.seedCount ctx.processedBits.length pair))
        (pair.1.map SelectionTableProgram.unary).reverse)
      (SelectorPairProgram.planBytes
        (SelectorProgram.selectionEntries ctx.seedCount
          (remaining ctx.seedCount ctx.processedBits.length pair))
        (pair.2.map SelectionTableProgram.unary).reverse) =
      PairScoreProgram.pairBytes (selectedPair ctx.seedCount ctx.processedBits.length pair) := by
    rw [show pair.1.map SelectionTableProgram.unary =
      pair.1.map SelectorProgram.unaryIndex by rfl]
    rw [show pair.2.map SelectionTableProgram.unary =
      pair.2.map SelectorProgram.unaryIndex by rfl]
    simpa only [List.map_reverse] using hpay
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    fin_cases j <;>
      simp [cleared, selectorAfter, PairPlanPreparation.queriesPrepared,
        tableAfter, tableReset, moved, copied, activeAfter, prefixRegs,
        PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
        RecordPrograms.state, ports, baseState, inputState, readRegs]
  · funext j
    fin_cases j <;>
      simp [cleared, clearStacks, selectorAfter,
        PairPlanPreparation.queriesPrepared, tableAfter, tableReset, moved, copied,
        copyStacks, activeAfter, PairPlanPreparation.unionPrepared,
        PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState,
        hpay', PairScoreProgram.pairRecords, ProgramEncoding.encodeRecords,
        TupleProgram.prependRecord, Encoding.encodeList]

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete incidence collision scoring from raw two-word read plans.
The fixed legacy program constructs its selection tables and all four-word
completion tuples at runtime. No precomputed collision table is an input. -/

namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

theorem output_frame (d : ScoreBuilderProgram.Data) (regs : Fin 16 → Bool)
    (scores : List Bool) (j : Fin 48) (hj : j ≠ 0) :
    (ScoreBuilderProgram.resultState d regs scores).stacks j = d.stacks j := by
  simp [ScoreBuilderProgram.resultState, hj]

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- This is an actual binary countdown and unary emission, with its
value-dependent time bound; no numeric conversion is free. -/
theorem unaryCommand_eval (ports : Fin 14 ↪ Fin 64) (d : Data)
    (h1 : d.stacks (ports 1)=[]) (h11 : d.stacks (ports 11)=[])
    (h12 : d.stacks (ports 12)=[]) (h13 : d.stacks (ports 13)=[]) :
    ∃ t rf, Eval (unaryCommand ports) t d
      (⟨rf,Function.update d.stacks (ports 1)
        (List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks (ports 0))) true)⟩ : Data) ∧
      t ≤ LeafParametersProgram.Serialization.unaryCopyBound (d.stacks (ports 0))+1 := by
  let a := projectState unaryRegs ports d
  obtain ⟨t,ht,he⟩ := LeafParametersProgram.Serialization.unaryCopy_eval 0 1 a
    (by decide) (by decide) (by decide) (by decide) h1 h11 h12 h13
  let bits := List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks (ports 0))) true
  let b := embedState unaryRegs ports d (SubexponentialSAT.SubexpClauseMastersProgram.write a 1 bits)
  have hc : Eval (unaryCommand ports) (t+1) d b := by
    apply eval_liftCommand_from_state (LeafParametersProgram.Serialization.unaryCopy 0 1)
      0 1 unaryRegs ports d unaryRegs.injective ports.injective
    exact he
  have hbase : Function.extend ports a.stacks d.stacks=d.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project unaryRegs ports d unaryRegs.injective ports.injective)
  have hb : b.stacks=Function.update d.stacks (ports 1) bits := by
    change Function.extend ports (Function.update a.stacks 1 bits) d.stacks=_
    rw [ProgramLinking.extend_update ports.injective,hbase]
  have heq : b=(⟨b.regs,Function.update d.stacks (ports 1) bits⟩ : Data) := by
    exact SubexponentialSAT.CounterForPrograms.data_ext rfl hb
  refine ⟨t+1,b.regs,?_,Nat.add_le_add_right ht 1⟩
  rw [heq] at hc
  exact hc

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

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

 def state (regs : Fin 8 → Bool) (wi wh ci ch score source acc output : List Bool) : Data :=
  ⟨regs, ![wi,ci,wh,ch,score,[],[],[],source,acc,output,[]]⟩
 def ready (regs : Fin 8 → Bool) (wi wh source acc output : List Bool) :=
  state regs wi wh [] [] [] source acc output

 theorem readFields_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (tail acc output : List Bool) :
    ∃ rf, Eval readFields (6*p.1+6*p.2+8)
      (ready regs wi wh (payload p ++ tail) acc output)
      (state rf wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output) := by
  let d := ready regs wi wh (payload p ++ tail) acc output
  let rest := SubexponentialSAT.Encoding.frame (List.replicate p.2 false) ++ tail
  obtain ⟨a, ha, hsa⟩ := SubexponentialSAT.SubexpInputFrames.readField_execute 8 1 (by decide) d
    (List.replicate p.1 false) rest (by simp [d, ready, state, payload, rest, List.append_assoc]) rfl
  have has : a.stacks = (state a.regs wi wh (List.replicate p.1 false) [] [] rest acc output).stacks := by
    rw [hsa]
    funext j; fin_cases j <;> simp [d,ready,state]
  obtain ⟨b, hb, hsb⟩ := SubexponentialSAT.SubexpInputFrames.readField_execute 8 3 (by decide) a
    (List.replicate p.2 false) tail (by rw [has]; rfl) (by rw [has]; rfl)
  have heb : b = state b.regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    rw [hsb,has]
    funext j; fin_cases j <;> simp [state]
  refine ⟨b.regs, ?_⟩
  have h := ha.seq hb
  rw [heb] at h
  convert h using 1 <;> simp only [readFields, List.length_replicate] ; omega

 theorem weighted_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (tail acc output : List Bool) :
    ∃ n ≤ scaleBudget wi p.1 + scaleBudget wh p.2 + 3, ∃ rf,
      Eval weighted n
        (state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output)
        (state rf wi wh (List.replicate p.1 false) (List.replicate p.2 false)
          (List.replicate (value wi wh p) false) tail acc output) := by
  let b := state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) [] tail acc output
  obtain ⟨n, hn, c, hc, hco, hcf⟩ := combine_lifted reg low reg_injective low_injective b
    p.1 p.2 rfl rfl rfl rfl rfl
  have hec : c = state c.regs wi wh (List.replicate p.1 false) (List.replicate p.2 false)
      (List.replicate (value wi wh p) false) tail acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    funext j
    fin_cases j <;> first
      | simpa [low, b, state, value] using hco
      | exact (hcf _ (by decide)).trans (by rfl)
  refine ⟨n, ?_, c.regs, ?_⟩
  · simpa [combineBudget,projectState,reg,low,b,state] using hn
  · rw [hec] at hc
    exact hc

 theorem clearCounts_eval (regs : Fin 8 → Bool) (wi wh : List Bool)
    (p : ℕ × ℕ) (score tail acc output : List Bool) :
    ∃ rf, Eval (.seq (clear 1) (clear 3)) (2*p.1+2*p.2+6)
      (state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) score tail acc output)
      (state rf wi wh [] [] score tail acc output) := by
  let c := state regs wi wh (List.replicate p.1 false) (List.replicate p.2 false) score tail acc output
  let c₁ : Data := ⟨readRegs c.regs 0 1 none, Function.update c.stacks 1 []⟩
  let c₂ : Data := ⟨readRegs c₁.regs 0 1 none, Function.update c₁.stacks 3 []⟩
  have h1raw : Eval (clear 1) (2*(c.stacks 1).length+3) c c₁ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 1 0 1 c.regs c.stacks)
  have h2raw : Eval (clear 3) (2*(c₁.stacks 3).length+3) c₁ c₂ :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 3 0 1 c₁.regs c₁.stacks)
  have hlen1 : (c.stacks 1).length=p.1 := by simp [c,state]
  have hlen2 : (c₁.stacks 3).length=p.2 := by simp [c₁,c,state]
  have h1 : Eval (clear 1) (2*p.1+3) c c₁ := by simpa only [hlen1] using h1raw
  have h2 : Eval (clear 3) (2*p.2+3) c₁ c₂ := by simpa only [hlen2] using h2raw
  have he : c₂ = state c₂.regs wi wh [] [] score tail acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    funext j; fin_cases j <;> rfl
  refine ⟨c₂.regs, ?_⟩
  have h := h1.seq h2
  rw [he] at h
  convert h using 1 ; omega

 theorem state_ready_of_frame (regs : Fin 8 → Bool) (wi wh score tail acc output : List Bool)
    (e : Data)
    (h4 : e.stacks 4=[])
    (h9 : e.stacks 9=CandidateScoreProgram.reverseRecord score acc)
    (hf : ∀ j,j≠4→j≠9→e.stacks j=(state regs wi wh [] [] score tail acc output).stacks j) :
    e=ready e.regs wi wh tail (CandidateScoreProgram.reverseRecord score acc) output := by
  apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj4 : j=4
  · subst j; exact h4
  by_cases hj9 : j=9
  · subst j; exact h9
  rw [hf j hj4 hj9]
  fin_cases j <;> simp_all [state,ready]

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

 theorem ready_update_source (regs : Fin 8 → Bool) (wi wh source tail acc output : List Bool) :
    Function.update (ready regs wi wh source acc output).stacks 8 tail =
      (ready regs wi wh tail acc output).stacks := by
  funext j
  fin_cases j <;> simp [ready,state]

 theorem tag_eval (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ))
    (acc output : List Bool) :
    ∃ rf, Eval readTag 1 (ready regs wi wh (pairsBytes ps) acc output)
      (ready rf wi wh (afterSource ps) acc output) ∧ rf 7 = flag ps := by
  obtain ⟨e, he, hs, hf⟩ := SubexponentialSAT.SubexpInputFrames.readTag_execute 8
    (ready regs wi wh (pairsBytes ps) acc output) (flag ps) (afterSource ps) (bytes_tag ps)
  have heq : e = ready e.regs wi wh (afterSource ps) acc output := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    exact hs.trans (ready_update_source regs wi wh (pairsBytes ps) (afterSource ps) acc output)
  exact ⟨e.regs, eval_congr_output he heq, hf⟩

 theorem finish_eval (regs : Fin 8 → Bool) (wi wh acc output : List Bool) :
    ∃ rf, Eval finish (3*acc.length+8) (ready regs wi wh [] acc output)
      (ready rf wi wh [] [] (acc.reverse ++ [false] ++ output)) := by
  let d := ready regs wi wh [] acc output
  let a := TupleProgram.pushedState 9 0 false d
  have hp := TupleProgram.pushConst_eval 9 0 false d
  have ht := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a 9 10 0 1 (by decide) (by decide)
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer a 9 10 0 1 =
      ready (readRegs a.regs 0 1 none) wi wh [] [] (acc.reverse ++ [false] ++ output) := by
    apply SubexponentialSAT.CounterForPrograms.data_ext <;> try rfl
    funext j; fin_cases j <;>
      simp [SubexponentialSAT.SubexpScanPrimitives.afterTransfer,a,d,ready,state,
        SubexponentialSAT.StackRoutines.transferStacks,List.append_assoc]
  have ht' := eval_congr_output ht he
  refine ⟨readRegs a.regs 0 1 none, ?_⟩
  have h := hp.seq ht'
  convert h using 1 <;> simp [finish,a,d,ready,state] ; omega

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

noncomputable def input (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) : Data :=
  embedState id zipPorts (base regs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs
      (SubexponentialSAT.ProgramEncoding.encodeRecords (firstScores ps))
      (SubexponentialSAT.ProgramEncoding.encodeRecords (secondScores ps)) [] [])

theorem input_regs (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    (input regs wi wh ps).regs = regs := by
  funext i
  exact embedState_register id zipPorts _ _ Function.injective_id i

theorem input_stacks (regs : Fin 8 → Bool) (wi wh : List Bool) (ps : List (ℕ × ℕ)) :
    (input regs wi wh ps).stacks =
      ![SubexponentialSAT.ProgramEncoding.encodeRecords (firstScores ps),
        SubexponentialSAT.ProgramEncoding.encodeRecords (secondScores ps),[],[],[],[],[],[],[],[],[],[],wi,wh] := by
  have hz (i : Fin 8) := embedState_stack id zipPorts (base regs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs
      (SubexponentialSAT.ProgramEncoding.encodeRecords (firstScores ps))
      (SubexponentialSAT.ProgramEncoding.encodeRecords (secondScores ps)) [] []) zipPorts_injective i
  have hf (j : Fin 14) (hj : 8 ≤ j.val) : (input regs wi wh ps).stacks j=(base regs wi wh).stacks j := by
    apply embedState_stack_frame
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    dsimp [zipPorts] at hv
    omega
  funext j
  fin_cases j <;> first
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 0
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 1
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 2
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 3
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 4
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 5
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 6
    | simpa [input,zipPorts,SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state] using hz 7
    | simpa [base] using hf (8 : Fin 14) (by decide)
    | simpa [base] using hf (9 : Fin 14) (by decide)
    | simpa [base] using hf (10 : Fin 14) (by decide)
    | simpa [base] using hf (11 : Fin 14) (by decide)
    | simpa [base] using hf (12 : Fin 14) (by decide)
    | simpa [base] using hf (13 : Fin 14) (by decide)

noncomputable def middle (regs initialRegs : Fin 8 → Bool) (wi wh : List Bool)
    (ps : List (ℕ × ℕ)) : Data :=
  embedState id zipPorts (base initialRegs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs [] [] [] (Streams.pairsBytes ps))

 theorem middle_projection (regs initialRegs : Fin 8 → Bool) (wi wh : List Bool)
    (ps : List (ℕ × ℕ)) :
    projectState id scorePorts (middle regs initialRegs wi wh ps) =
      Streams.ready regs wi wh (Streams.pairsBytes ps) [] [] := by
  have hz (i : Fin 8) := embedState_stack id zipPorts (base initialRegs wi wh)
    (SubexponentialSAT.SubexpInputZip.ready regs [] [] [] (Streams.pairsBytes ps)) zipPorts_injective i
  have hw12 : (middle regs initialRegs wi wh ps).stacks 12 = wi := by
    apply (embedState_stack_frame id zipPorts _ _ 12 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  have hw13 : (middle regs initialRegs wi wh ps).stacks 13 = wh := by
    apply (embedState_stack_frame id zipPorts _ _ 13 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  have hz8 : (middle regs initialRegs wi wh ps).stacks 8 = [] := by
    apply (embedState_stack_frame id zipPorts _ _ 8 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  have hz9 : (middle regs initialRegs wi wh ps).stacks 9 = [] := by
    apply (embedState_stack_frame id zipPorts _ _ 9 ?_).trans
    · rfl
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      dsimp [zipPorts] at hv
      omega
  apply SubexponentialSAT.CounterForPrograms.data_ext
  · funext i
    exact embedState_register id zipPorts _ _ Function.injective_id i
  · funext i
    fin_cases i <;> first
      | exact hw12
      | exact hw13
      | exact hz8
      | exact hz9
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 0
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 1
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 2
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 3
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 4
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 5
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 6
      | simpa [projectState,scorePorts,zipPorts,Streams.ready,Streams.state,
          SubexponentialSAT.SubexpInputZip.ready,SubexponentialSAT.SubexpInputZip.state,middle] using hz 7

 theorem final_clean (rz initialRegs rf : Fin 8 → Bool) (wi wh : List Bool)
    (ps : List (ℕ × ℕ)) (j : Fin 14) (hj8 : j ≠ 8) (hj12 : j ≠ 12) (hj13 : j ≠ 13) :
    (embedState id scorePorts (middle rz initialRegs wi wh ps)
      (Streams.ready rf wi wh [] []
        (SubexponentialSAT.ProgramEncoding.encodeRecords (Streams.scores wi wh ps)))).stacks j = [] := by
  by_cases hs : ∃ i, scorePorts i = j
  · obtain ⟨i, rfl⟩ := hs
    rw [embedState_stack id scorePorts _ _ scorePorts_injective]
    fin_cases i <;> simp [scorePorts,Streams.ready,Streams.state] at hj8 hj12 hj13 ⊢
  · rw [embedState_stack_frame id scorePorts _ _ j hs]
    by_cases hz : ∃ k, zipPorts k = j
    · obtain ⟨k, rfl⟩ := hz
      change (embedState id zipPorts _ _).stacks (zipPorts k) = []
      rw [embedState_stack id zipPorts _ _ zipPorts_injective]
      by_cases hk : k = 6
      · subst k
        exact False.elim (hs ⟨8,rfl⟩)
      · fin_cases k <;> simp [] at hk ⊢
    · change (embedState id zipPorts _ _).stacks j = []
      rw [embedState_stack_frame id zipPorts _ _ j hz]
      simp [base,hj12,hj13]

end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMerge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete stream merger into the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def MergeInput (wi wh : List Bool) (ps : List (ℕ × ℕ)) (d : Data) : Prop :=
  ∀ i, d.stacks (mergePorts i) = (Zip.input (d.regs ∘ mergeRegisters) wi wh ps).stacks i

theorem merge_projection (wi wh : List Bool) (ps : List (ℕ × ℕ))
    (d : Data) (h : MergeInput wi wh ps d) :
    projectState mergeRegisters mergePorts d = Zip.input (d.regs ∘ mergeRegisters) wi wh ps := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · exact (Zip.input_regs _ _ _ _).symm
  · exact funext h

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem park_cost (d : Data) : moveCost metadata d = 6*parameterLength d+24 := by
  simp [moveCost,metadata,moved,parameterLength]
  omega

theorem park_eval (d : Data) (h : parkReady d) :
    Eval park (6*parameterLength d+24) d (parked d) := by
  simpa only [park,parked,park_cost] using moveMany_eval metadata d (park_ready d h)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyWeights
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual native coefficient construction followed by stream weighting. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem weights_mergeInput (d e : Data) (ps : List (ℕ × ℕ))
    (h : inputPairScores d ps) (hf : ∀ j,j≠15→j≠16→e.stacks j=d.stacks j) :
    MergeInput (e.stacks 15) (e.stacks 16) ps e := by
  intro i
  rw [Zip.input_stacks]
  fin_cases i <;> simp [mergePorts,hf,h.1,h.2.1,h.2.2]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Emit the computed beta at the actual all-zero sparse key. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def origin : Code := .seq PerturbationMaskProgram.zeroCommand
  (.seq PerturbationEmitProgram.keyCommand (.seq (copy 220 228)
    (.seq (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))
      (.seq PerturbationEmitProgram.emitCommand (clear 214)))))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native high-variable dispatch from original-coordinate mask/assignment
masters. The runtime index is233, and both source masters are retained. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def readFlag (source : Fin 256) : Code :=
  .seq (copy 233 222) (.seq (copy source 223) bitRead)

/-- For a high literal, select the full ring constant from the current branch. -/
def highConstant : Code := .seq (readFlag 235)
  (.seq (.ite 15 (copy 208 220) (copy 207 220)) (.seq origin (clear 220)))


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native bounded traversal with distinct input cells and output accumulator.
This is used to construct the padded polynomial-cell stream before Horner. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

variable {C : Type*}

def command (body : Code) : Code := HornerProgram.traversal body

end SubexponentialSAT.SqrtLog.PerturbationProgram.Traversal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite scalar-to-polynomial padding. The runtime degree and
coefficient width are tapes, so this command is independent of all dimensions. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open DensePolynomialProgram.Constructor

/-- Read a scalar, build its padded constant polynomial, prepend that cell to
an accumulating output stream, and restore every temporary stack. -/
def iteration : Code :=
  .seq HornerProgram.takeCoefficient
    (.seq (SubexpPolynomialConstructor.construct 241 254 253)
      (.seq (clear 241) (.seq (copy 253 240) (clear 253))))

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def command : Code := .seq HornerProgram.reverseStream (Traversal.command iteration)

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native composition from a complete scalar coefficient row to its shifted
jet. Padding and both runtime counters are executed, rather than supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram
open CRTLocalProgram (ServiceSpec LowFrame serviceSpec_frame)

def shift (multiply add : Code) : Code :=
  .seq loadRow (.seq Padding.command (.seq enterHorner
    (.seq (HornerProgram.command multiply add) (clear 250))))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

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

def peekRow : Code := .base (.atom (.peek 230 0 1))

def skip : Code := clear 246

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- The array is the actual output of the fixed native shift command. -/
def finishCoordinate : Code := .seq (shift DensePolynomialProgram.Fixed.mulCommand
  DensePolynomialProgram.AddService.command) (.seq PerturbationEmitProgram.command
    (.seq (clear 214) PerturbationMaskProgram.advance))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native traversal of the actual runtime-framed row list. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def coordinate : Code := .seq loadCoordinate finishCoordinate


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete native coordinate-row scan with arithmetic callbacks discharged. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def scanStep {B d : ℕ} (ops : RingProgram (Coeff B d)) (J n N : ℕ)
    (theta : Coeff B d) (j : ℕ) (P : Fixed.Array B d N) (acc : List Bool) : List Bool :=
  if hj : j < n then coordinateResult ops J theta ⟨j,hj⟩ P.val acc else acc

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

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

def state (regs : Fin 5 → Bool) (i n : ℕ) (out : List Bool) : Data :=
  ⟨regs, ![unary n, zeros i, [], [], [], [false], out]⟩

def copied (src dst : Fin 7) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst : Fin 7) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 4) (hd : (4 : Fin 7) ≠ dst)
    (h4 : d.stacks 4 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  TupleProgram.copy_eval src dst 4 0 1 hsd hs hd (by decide) d h4

def repeatState (regs : Fin 5 → Bool) (i n : ℕ) (bits count out : List Bool) : Data :=
  ⟨regs, ![unary n, zeros i, bits, count, [], [false], out]⟩

theorem repeatZeros_eval (regs : Fin 5 → Bool) (i n : ℕ) (bits out : List Bool)
    (hr : ∀ j : Fin 3, regs (repeatRegisters j) = false) :
    Eval repeatZeros (14 * n + 3)
      (repeatState regs i n bits (unary n) out)
      (repeatState (resetThree regs) i n (zeros n ++ bits) [] out) := by
  let a := repeatState regs i n bits (unary n) out
  let b := repeatState (resetThree regs) i n (zeros n ++ bits) [] out
  have hc : BlockCopyProgram.copies n [false] = zeros n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [BlockCopyProgram.copies_succ, ih, List.replicate_succ']
  have ha : embedState repeatRegisters repeatStacks a
      (BlockCopyProgram.initialState n [false] bits) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ repeatRegisters_injective repeatStacks_injective
    · intro j; fin_cases j <;>
        simpa [a, repeatState, BlockCopyProgram.initialState, BlockCopyProgram.data] using hr _
    · intros; rfl
    · intro j; fin_cases j <;> rfl
    · intros; rfl
  have hb : embedState repeatRegisters repeatStacks a
      (BlockCopyProgram.data false false [false] (zeros n ++ bits) []) = b := by
    apply embedState_eq_of_ports _ _ _ _ _ repeatRegisters_injective repeatStacks_injective
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h3 : 3 ≤ j.val := by
        by_contra h
        exact hj ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
      simp [b, a, repeatState, resetThree, Nat.not_lt.mpr h3]
    · intro j; fin_cases j <;> rfl
    · intro j hj
      fin_cases j <;> first | rfl | exact (hj ⟨0, rfl⟩).elim |
        exact (hj ⟨1, rfl⟩).elim | exact (hj ⟨2, rfl⟩).elim | exact (hj ⟨3, rfl⟩).elim
  have ht := BlockCopyProgram.program_trace n [false] bits
  rw [hc] at ht
  have h := eval_call_lifted BlockCopyProgram.program repeatRegisters repeatStacks a
    repeatRegisters_injective repeatStacks_injective ht
  simpa only [repeatZeros, ha, hb, List.length_singleton, Nat.mul_one,
    Nat.reduceAdd, Nat.mul_comm] using h

theorem popped_state (regs : Fin 5 → Bool) (i n : ℕ) (out : List Bool) :
    UnaryForPrograms.popped loopPorts (state regs i n out) =
      state (poppedRegs regs n) i (n - 1) out := by
  apply congrArg (StructuredProgram.State.mk _)
  funext j
  fin_cases j <;> simp [ loopPorts, state,
    List.tail_replicate]

def outputState (n : ℕ) : Data :=
  ⟨fun _ => false, ![[], [], [], [], [], [], ProgramEncoding.encodeRecords (rows 0 n)]⟩

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Dynamic target-jet cache installation. Full source-degree metadata at210
is untouched while the arithmetic count is temporarily changed to213. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram.Constructor

def initializeTarget : Code := .seq (saveReplace 213 193 237)
  (.seq (saveReplace 213 243 238) (.seq constructConstants
    (.seq (saveReplace 239 192 236) (clear 239))))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The common perturbation input invariant follows from the actual paid leaf
staging copies and a clean worker. The full source count is built as R+1. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

structure CallerInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J R : ℕ) (theta : Coeff (baseWidth 3 t) d) (s : OuterData) (n : ℕ) : Prop where
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  modulus : s.stacks 194=M.bits
  width : (s.stacks 202).length=baseWidth 3 t
  zero : s.stacks 203=cache.zero.val
  table : s.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable t a M cache)
  degree : (s.stacks 204).length=d
  choicesLength : (s.stacks 145).length=n
  zeroWord : s.stacks 280=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s.stacks 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s.stacks 78=RingProgram.flat theta
  ambientCount : s.stacks 128=List.replicate n true
  targetCount : s.stacks 243=List.replicate J true
  radius : s.stacks 138=List.replicate R true
  highLength : (s.stacks 703).length=n
  workerEmpty : ∀ i:Fin 768,340 ≤ i.val → i.val < 680 → i≠556 → s.stacks i=[]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
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

theorem wordAlphabet_eval (a : Data) (r Q : ℕ) (hc : Clean a)
    (h7 : a.stacks 7 = ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r))
    (h2 : a.stacks 2 = unary Q) :
    Writes wordAlphabet a 30 (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q))
      (TupleProgram.powerCost (OneHotAlphabetProgram.rows 0 r) Q [[]] + 9) := by
  let pre := project (register (r := 10) (by decide)) (stack (s := 9) (by decide))
    (prepareState 31 work [(7, 13), (2, 20)] a)
  have hs (i : Fin 9) : pre.stacks i =
      if i = 8 then unary Q else if i = 1 then
        ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r) else [] := by
    have h := prepare_two_local (r := 10) (s := 9)
      (by decide) (by decide) a hc 7 2 1 8 (by decide) (by decide) i
    change pre.stacks i = _ at h
    simpa only [h7, h2] using h
  have hp : TupleProgram.outerInvariant (OneHotAlphabetProgram.rows 0 r) (unary Q)
      (pre.regs 9) pre := by
    simp [TupleProgram.outerInvariant, hs]
  obtain ⟨out, hout, ticks, htime, ht⟩ := TupleProgram.generateProgram_runsIn
    (OneHotAlphabetProgram.rows 0 r) (unary Q) (pre.regs 9) pre hp
    (by simp [hs]) (by simp [hs]) (by simp [hs])
  obtain ⟨b, he, hb, hclean⟩ := call_eval TupleProgram.generateProgram
    (by decide) (by decide) [(7, 13), (2, 20)] 0 30 a out
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, ?_, hclean, ?_⟩
  · rw [hb, hout.2.1]
    simp only [List.length_replicate, AssignmentAlphabetSemantics.wordBytes]
  · intro B ha hresult hB
    rcases hout with ⟨⟨h1, h3, h4, h6, h7', h8, h9⟩, h0, h2', h5⟩
    have halphabet : (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r)).length ≤ B := by
      simpa only [← h7] using ha 7
    have ho : Within out B := by
      intro j
      fin_cases j <;> simp_all [AssignmentAlphabetSemantics.wordBytes]
    have h := callCost_le (r := 10) (s := 9) (by decide) (by decide)
      [(7, 13), (2, 20)] 0 30 a out ticks B (by decide) ha ho
    simp only [List.length_replicate] at htime
    exact h.trans (Nat.add_le_add_right htime _)

theorem firstWord_eval (a : Data) (bits : List Bool) (rows : List (List Bool))
    (hc : Clean a) (h30 : a.stacks 30 = ProgramEncoding.encodeRecords (bits :: rows)) :
    Writes firstWord a 0 bits (9 * bits.length + 10) := by
  let pre := project (register (r := 3) (by decide)) (stack (s := 3) (by decide))
    (prepareState 31 work [(30, 12)] a)
  have hp : pre = AssignmentRecordViews.data (pre.regs 0) (pre.regs 1) (pre.regs 2)
      (ProgramEncoding.encodeRecords (bits :: rows)) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i
      have h := prepare_one_local (r := 3) (s := 3) (by decide) (by decide) a hc 30 0 i
      change pre.stacks i = _
      change pre.stacks i = _ at h
      rw [h]
      fin_cases i <;> simp [ h30]
  have ht := AssignmentRecordViews.first_trace (pre.regs 0) (pre.regs 1) (pre.regs 2) bits rows
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval AssignmentRecordViews.firstProgram
    (by decide) (by decide) [(30, 12)] 2 0 a
    (AssignmentRecordViews.data false false false (ProgramEncoding.encodeRecords rows) [] bits)
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, hs, hb, ?_⟩
  intro B ha hresult _
  have htail : (ProgramEncoding.encodeRecords rows).length ≤ B := by
    have hh := ha 30
    rw [h30] at hh
    change (Encoding.encodeList id rows).length ≤ B
    change (Encoding.encodeList id (bits :: rows)).length ≤ B at hh
    rw [Encoding.length_encodeList_cons] at hh
    omega
  have ho : Within (AssignmentRecordViews.data false false false
      (ProgramEncoding.encodeRecords rows) [] bits) B := by
    intro j; fin_cases j <;> simp [ htail, hresult]
  exact callCost_le (r := 3) (s := 3) (by decide) (by decide)
    [(30, 12)] 2 0 a _ _ B (by decide) ha ho

theorem packedAlphabet_eval (a : Data) (rows : List (List Bool)) (hc : Clean a)
    (h30 : a.stacks 30 = ProgramEncoding.encodeRecords rows) :
    Writes packedAlphabet a 9 rows.flatten
      (9 * (rows.map List.length).sum + 6 * rows.length + 7) := by
  let pre := project (register (r := 3) (by decide)) (stack (s := 3) (by decide))
    (prepareState 31 work [(30, 12)] a)
  have hp : pre = AssignmentRecordViews.data (pre.regs 0) (pre.regs 1) (pre.regs 2)
      (ProgramEncoding.encodeRecords rows ++ []) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i
      have h := prepare_one_local (r := 3) (s := 3) (by decide) (by decide) a hc 30 0 i
      change pre.stacks i = _
      change pre.stacks i = _ at h
      rw [h]
      fin_cases i <;> simp [ h30]
  have ht := AssignmentRecordViews.flatten_trace (pre.regs 0) (pre.regs 1) (pre.regs 2) rows [] []
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval AssignmentRecordViews.flattenProgram
    (by decide) (by decide) [(30, 12)] 2 9 a
    (AssignmentRecordViews.data false false false [] [] (rows.flatten ++ []))
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, by simpa using hs, hb, ?_⟩
  intro B ha hresult _
  simp only [List.length_flatten] at hresult
  have ho : Within (AssignmentRecordViews.data false false false [] [] (rows.flatten ++ [])) B := by
    intro j; fin_cases j <;> simp [ hresult]
  exact callCost_le (r := 3) (s := 3) (by decide) (by decide)
    [(30, 12)] 2 9 a _ _ B (by decide) ha ho

theorem deltaPlusOne_eval (a : Data) (delta : ℕ) (hc : Clean a)
    (h3 : a.stacks 3 = unary delta) (h6 : a.stacks 6 = []) :
    Writes deltaPlusOne a 6 (unary (delta + 1)) (7 * delta + 7) := by
  let b := copyState 3 6 a
  let c := TupleProgram.pushedState 6 0 true b
  have h1 := copy_eval 3 6 31 a (by decide) (by decide) (by decide) hc.2
  have h2 := TupleProgram.pushConst_eval 6 0 true b
  have hs : c.stacks = Function.update a.stacks 6 (unary (delta + 1)) := by
    funext j
    by_cases hj : j = 6
    · subst j
      simp [c, b, copyState_stack, h3, h6, unary, List.replicate_succ]
    · simp [c, b, copyState_stack, hj]
  refine ⟨_, c, h1.seq h2, hs, clean_of_update a c 6 _ hc (by decide) (by decide) hs, ?_⟩
  intro B _ _ _
  simp only [h3, List.length_replicate]
  omega

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end


