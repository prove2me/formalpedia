-- Prove2me | Definitions.Def_OAIQ082C023
-- name    : OAIQ082C023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:47:03.688392+00:00
-- url     : https://prove2.me/theorems/d97b0c43-8d34-4ffe-9bee-2cf7053472b2
-- title:
--   Definitions bundle OAIQ082C023 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 304 declarations of OpenAI's Lean: 59 definitions and 245 theorems. The definitions and types are `OAI.BinPackingCompleteness.PreprocessingMachine.preprocessing`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs.boundary`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs.finished`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs.localBase`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTable.bodySteps`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTable.loopSteps`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTable.machineInTime`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTable.outputBlocks`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTable.totalSteps`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTable.vertexBlock`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime.computableInPolyTime`, `OAI.BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime.terminalRun`, `OAI.BinPackingGames.Foundations.Complexity.MachineOverlayTable.tableInTime`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddedOverlay.execution`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddedOverlay.familyInTime`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddedOverlay.overlayInTime`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddedOverlay.paddingInTime`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddedOverlayRuntime.computableInPolyTime`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddedOverlayRuntime.terminalRun`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddingRows.cfg`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddingRows.initialTapes`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddingRows.paddingBits`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddingRows.steps`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddingRows.tapes`, `OAI.BinPackingGames.Foundations.Complexity.MachinePaddingTable.execution`, `OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.machineInTime`, `OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.oldData`, `OAI.BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime.computableInPolyTime`, `OAI.BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime.terminalRun`, `OAI.BinPackingGames.Foundations.Complexity.MachineVertexPadding.rowTime`, `OAI.BinPackingGames.Foundations.Complexity.MachineVertexPadding.totalTime`, `OAI.BinPackingGames.Foundations.Complexity.MachineVertexPadding.vertexPaddingInTime`, `OAI.BinPackingGames.Foundations.Complexity.PoweringInitializeFrame.initialExtra`, `OAI.BinPackingGames.Foundations.Complexity.PoweringInitializeFrame.initializeInTime`, `OAI.BinPackingGames.Foundations.Complexity.PoweringInitializeFrame.preparedCfg`, `OAI.BinPackingGames.Foundations.Complexity.PoweringInitializeFrame.preparedTapes`, `OAI.BinPackingGames.Foundations.Complexity.PoweringMachineField.instruction`, `OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.machine`, `OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.program`, `OAI.BinPackingGames.Foundations.Complexity.PoweringMachineOuterLoop.loopInTime` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Computation_MachineCloudPrefix`, `BinPacking_Computation_MachineCloudRank`, `BinPacking_Computation_MachineCloudSelect`, `BinPacking_Computation_MachineLazyRows`, `BinPacking_Computation_MachineLazyTableRuntime`, `BinPacking_Computation_MachineOverlayRows`, `BinPacking_Computation_MachineOverlayTable`, `BinPacking_Computation_MachinePaddedOverlayRuntime`, `BinPacking_Computation_MachineRegularDummyRow`, `BinPacking_Computation_MachineRegularExecutionBounds`, `BinPacking_Computation_MachineRegularInternalRow`, `BinPacking_Computation_MachineRegularOwnerBodyBounds`, `BinPacking_Computation_MachineRegularOwnerProgram`, `BinPacking_Computation_MachineRegularTable`, `BinPacking_Computation_MachineRegularTableRuntime`, `BinPacking_Computation_MachineRegularVertexBlock`, `BinPacking_Computation_MachineVertexPadding`, `BinPacking_Computation_PoweringGlobalEnumeration`, `BinPacking_Computation_PoweringMachineRowBody`, `BinPacking_Computation_PoweringMachineRuntime`, `BinPacking_CookLevin_Completeness`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_PCP_FinalConstants`, `BinPacking_PCP_Initialization`, `BinPacking_PCP_PCPSourceHardness`, `BinPacking_PCP_PreprocessingMachineBounds`, `BinPacking_PCP_PreprocessingRegularBounds`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C016` and `OAIQ082C017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C027`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C016
import Definitions.Def_OAIQ082C017

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCloudRank
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

open BinPackingGames.Foundations.PCP

theorem cloudRankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[
        rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hk : e.val.val ≤ (tableRows t).length := by
    rw [tableRows_length]
    exact e.val.isLt.le
  have h := rankTrace t.vertices t.darts v.val e.val.val (tableRows t) hk
    (tableRows_width t) querySuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, ← cloudRank_eq_prefix_count t v e, ← List.append_assoc,
    replicate_encodeWord, Nat.add_zero] at h
  exact h

end BinPackingGames.Foundations.Complexity.MachineCloudRank

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularDummyRow
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

variable {σ : Type}

theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

end BinPackingGames.Foundations.Complexity.MachineDummyRows

namespace BinPackingGames.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

def tapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineDummyRows.fieldTapes v e output)
    (fun _ : Unit => encodeWord fuel)

def cfg (d : Nat) (label : Option (Label d)) (v e fuel : Nat)
    (output : List Bool) : TM2.Cfg Alphabet (Label d) State :=
  ⟨label, (((), none), ()), tapes v e fuel output⟩

theorem bodyTrace (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d]
      (some (cfg d (some (bodyEntry d hd)) v e fuel output)) =
      some (cfg d (some (.inr .bump)) v (e + d) fuel
        (output ++ MachineDummyRows.rowsBits v e d)) := by
  have run := MachineDummyRows.suffixTrace d ⟨0, hd⟩ (by simp)
    v e output () none
  have lifted := liftSuccessfulTrace
    (TM2.step (MachineDummyRows.program d)) (TM2.step (program d hd))
    (MachineEmbedding.configuration (some (.inr .bump)) ()
      (fun _ : Unit => encodeWord fuel))
    (by
      intro a b h
      exact MachineEmbedding.step_simulation (some (.inr Control.bump)) ()
        (fun _ : Unit => encodeWord fuel) (MachineDummyRows.program d) (extra d hd) a b h)
    (MachineDummyRows.steps v e output d) _ _ run
  exact lifted

theorem guard_succ (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e (fuel + 1) output) =
      some (cfg d (some (bodyEntry d hd)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_succ, List.cons_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_true]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem guard_zero (d : Nat) (hd : 0 < d) (v e : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e 0 output) =
      some (cfg d none v e 0 output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_zero, List.nil_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem bump_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .bump)) v e fuel output) =
      some (cfg d (some (.inr .guard)) (v + 1) e fuel output) := by
  change some (TM2.stepAux (extra d hd .bump) _ _) = _
  simp only [extra, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes, encodeWord, List.replicate_succ]
  | inr k => simp [tapes, MachineEmbedding.tapes]

def paddingBits (d v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => MachineDummyRows.rowsBits v e d ++ paddingBits d (v + 1) (e + d) count

def steps (d v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 1
  | count + 1 => (MachineDummyRows.steps v e output d + 2) +
      steps d (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d) count

theorem loopTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count]
      (some (cfg d (some (.inr .guard)) v e count output)) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  induction count generalizing v e output with
  | zero => simpa [steps, paddingBits] using guard_zero d hd v e output
  | succ count ih =>
      rw [steps, Nat.add_comm (MachineDummyRows.steps v e output d + 2),
        Function.iterate_add_apply]
      have hb : (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d + 2]
          (some (cfg d (some (.inr .guard)) v e (count + 1) output)) =
          some (cfg d (some (.inr .guard)) (v + 1) (e + d) count
            (output ++ MachineDummyRows.rowsBits v e d)) := by
        rw [show MachineDummyRows.steps v e output d + 2 =
          (MachineDummyRows.steps v e output d + 1) + 1 by omega,
          Function.iterate_succ_apply, advance_some, guard_succ,
          Function.iterate_succ_apply', bodyTrace, advance_some, bump_step]
      rw [hb, ih]
      simp only [paddingBits, List.append_assoc, Nat.succ_mul]
      congr 2 <;> omega

def initialTapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  Function.update (tapes v e fuel output) (.inl 2) []

theorem initialize_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd)
      ⟨some (.inr .initialize_), (((), none), ()), initialTapes v e fuel output⟩ =
      some (cfg d (some (.inr .guard)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .initialize_) _ _) = _
  simp only [extra, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, initialTapes, Function.update_self, List.append_nil,
    Function.update_idem, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes]
  | inr k => simp [tapes, MachineEmbedding.tapes]

theorem paddingTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count + 1]
      (some ⟨some (.inr .initialize_), (((), none), ()), initialTapes v e count output⟩) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  rw [Function.iterate_succ_apply, advance_some, initialize_step, loopTrace]

end BinPackingGames.Foundations.Complexity.MachinePaddingRows

namespace BinPackingGames.Foundations.Complexity.MachinePaddingBounds

theorem rowsBits_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    have hi := ih (e + 1)
    have hb : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [hb] at hi
    have hr : v + e + 8194 ≤ v + e + (count + 1) + 8194 := by omega
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    calc
      _ ≤ (v + e + (count + 1) + 8194) +
          count * (v + e + (count + 1) + 8194) := Nat.add_le_add hr hi
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem steps_le_bound (d v e : Nat) (output : List Bool) (count : Nat) :
    MachinePaddingRows.steps d v e output count ≤
      count * (d * (4 * rowBound d v e count +
        2 * (output.length + count * d * rowBound d v e count) + 10) + 2) + 1 := by
  induction count generalizing v e output with
  | zero => simp [MachinePaddingRows.steps]
  | succ count ih =>
    let B := rowBound d v e (count + 1)
    let C := d * (4 * B + 2 * (output.length + (count + 1) * d * B) + 10) + 2
    have hb : rowBound d (v + 1) (e + d) count = B := rowBound_next d v e count
    have hr : v + e + d + 8194 ≤ B := blockRow_le_rowBound d v e count
    have hlen : (MachineDummyRows.rowsBits v e d).length ≤ d * B :=
      (rowsBits_length_le v e d).trans (Nat.mul_le_mul_left d hr)
    have hout : (output ++ MachineDummyRows.rowsBits v e d).length + count * d * B ≤
        output.length + (count + 1) * d * B := by
      rw [List.length_append]
      calc
        _ ≤ output.length + d * B + count * d * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hlen output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hi := ih (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d)
    rw [hb] at hi
    have hconstant :
        d * (4 * B + 2 * ((output ++ MachineDummyRows.rowsBits v e d).length +
          count * d * B) + 10) + 2 ≤ C := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left d
        (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10)) 2
    have hremaining := hi.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left count hconstant) 1)
    have hcount : d * B ≤ (count + 1) * d * B := by
      simpa only [Nat.one_mul, Nat.mul_assoc] using
        Nat.mul_le_mul_right (d * B) (Nat.succ_le_succ (Nat.zero_le count))
    have hbodyOutput : output.length + d * (v + e + d + 8194) ≤
        output.length + (count + 1) * d * B :=
      Nat.add_le_add_left ((Nat.mul_le_mul_left d hr).trans hcount) output.length
    have hbodyInner : 4 * (v + e + d + 8194) +
        2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
          4 * B + 2 * (output.length + (count + 1) * d * B) + 10 := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hr)
        (Nat.mul_le_mul_left 2 hbodyOutput)) 10
    have hbody : MachineDummyRows.steps v e output d + 2 ≤ C :=
      Nat.add_le_add_right ((MachineDummyRows.steps_le_bound v e output d).trans
        (Nat.mul_le_mul_left d hbodyInner)) 2
    change (MachineDummyRows.steps v e output d + 2) +
      MachinePaddingRows.steps d (v + 1) (e + d)
        (output ++ MachineDummyRows.rowsBits v e d) count ≤ (count + 1) * C + 1
    calc
      _ ≤ C + (count * C + 1) := Nat.add_le_add hbody hremaining
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem timePolynomial_bounds (d v e count : Nat) (output : List Bool) :
    MachinePaddingRows.steps d v e output count ≤
      (timePolynomial d).eval (inputSize v e count output) := by
  have hc : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have ho : output.length ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hb := rowBound_le_cap d v e count output
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_right d hc) hb
  have hout := Nat.add_le_add ho hp
  have hinner := Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 4 hb) (Nat.mul_le_mul_left 2 hout)) 10
  have hbody := Nat.add_le_add_right (Nat.mul_le_mul_left d hinner) 2
  have h := (steps_le_bound d v e output count).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hc hbody) 1)
  simpa only [timePolynomial, rowPolynomial, rowCap, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end BinPackingGames.Foundations.Complexity.MachinePaddingBounds

namespace BinPackingGames.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowsBits_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn fun p : Fin count => MachineDummyRows.rowBits v (e + p.val)).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons]
    simp only [Fin.val_zero, Nat.add_zero]
    apply congrArg (MachineDummyRows.rowBits v e ++ ·)
    rw [ih]
    apply congrArg List.flatten
    congr 1
    funext p
    simp only [Fin.val_succ]
    congr 1
    omega

theorem rowBits_stay {n d : Nat} (v : Fin n) (p : Fin d) :
    MachineDummyRows.rowBits v.val (2 * d * v.val + p.val) =
      encodeWords (rowWords (stayRow d v p)) := by
  have h := MachineDummyRows.rowBits_eq_graph_row v (stayRow d v p).reverseIndex
  rw [stayRow_reverse_val] at h
  exact h

theorem rowsBits_stay {n d : Nat} (v : Fin n) :
    MachineDummyRows.rowsBits v.val (2 * d * v.val) d =
      encodeWords ((List.ofFn (stayRow d v)).flatMap rowWords) := by
  rw [rowsBits_ofFn, encodeWords_flatMap]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext p
  exact rowBits_stay v p

end BinPackingGames.Foundations.Complexity.MachineLazyCodec

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem rowBits_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) p =
      MachineDummyRows.rowBits (n + v.val) (p.val + d * (n + v.val)) := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_new,
    PreprocessingPaddingTables.relations_pad_new]
  rfl

theorem dummy_rowsBits_eq_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn (fun p : Fin count => MachineDummyRows.rowBits v (e + p.val))).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext p
    congr 1
    omega

theorem paddingBits_eq_ofFn (d v e count : Nat) :
    MachinePaddingRows.paddingBits d v e count =
      (List.ofFn (fun k : Fin count =>
        MachineDummyRows.rowsBits (v + k.val) (e + k.val * d) d)).flatten := by
  induction count generalizing v e with
  | zero => rfl
  | succ count ih =>
    rw [MachinePaddingRows.paddingBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ, Nat.add_mul, Nat.one_mul]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext k
    congr 1 <;> omega

theorem vertexBits_pad_new (table : Table n d) (h : n ≤ m) (v : Fin (m - n)) :
    vertexBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) =
      MachineDummyRows.rowsBits (n + v.val) (n * d + v.val * d) d := by
  unfold vertexBits
  simp_rw [rowBits_pad_new]
  rw [dummy_rowsBits_eq_ofFn]
  apply congrArg (fun f : Fin d → List Bool => (List.ofFn f).flatten)
  funext p
  congr 1
  ring

theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end BinPackingGames.Foundations.PCP.PreprocessingPaddingWords

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingMachineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open BinPackingGames.Foundations.Complexity
open scoped BigOperators

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

end BinPackingGames.Foundations.PCP.PreprocessingMachineBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCloudPrefix
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open BinPackingGames.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

theorem paddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining total : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] [] bound remaining total⟩) =
      some ⟨some .add, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v))
          (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          bound remaining total⟩ := by
  have h := MachineCloudPadding.Placement.trace Tape.inner paddingView paddingView_left paddingView_right
    Label.padding (some Label.add) (frame [] [] [] [] [] bound remaining total)
    (MachineCloudPadding.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudPadding.cloudPaddingTrace t v [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label, placedTapes,
    frame_bound, frame_remaining, frame_total, List.append_nil, frame, memory] using h

theorem bodyTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[bodyTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
          bound remaining (encodeWord acc)⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + acc))⟩ := by
  let k := PreprocessingCloudIndex.cloudSize t v
  let p := MachineCloudPadding.padding k
  let l := PreprocessingLevels.boundedLevel k
  have hp := paddingTrace t v bound remaining (encodeWord acc) ambient register
  have ha := MachineUnaryAddAt.addFromTapes (Tape.inner .power) Tape.total (by decide)
    Label.add (some Label.clearCount) program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord p) (encodeWord l) bound remaining (encodeWord acc))
    p acc [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_power, update_frame_total] at ha
  have hc := MachineLookup.discardTrace (Tape.inner .count) Label.clearCount Label.clearLevel
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    k [] (by simp) (ambient, false) none
  simp only [update_frame_count] at hc
  have hl := MachineLookup.discardTrace (Tape.inner .level) Label.clearLevel Label.increment
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) []
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    l [] (by simp) (ambient, false) none
  simp only [update_frame_level] at hl
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .increment, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] (encodeWord 0) []
          bound remaining (encodeWord (p + acc))⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (p + acc))⟩ :=
    incrementStep _ _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hp ha) hc) hl) hi

theorem loopTrace (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (bound suffix : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[loopTime t v n]
      (some ⟨some .guard, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v) [] [] []
          bound (encodeWord n ++ suffix) (encodeWord acc)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v + n)) [] [] []
          bound (encodeWord 0 ++ suffix) (encodeWord (sumFrom t v n + acc))⟩ := by
  induction n generalizing v acc register with
  | zero =>
      simpa only [loopTime, sumFrom, Nat.add_zero, Nat.zero_add] using
        zeroTrace _ bound suffix (encodeWord acc) v ambient register
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hg : (advance (TM2.step program))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord (n + 1) ++ suffix) (encodeWord acc)⟩) =
          some ⟨some (.padding .init), ((ambient, false), none),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord n ++ suffix) (encodeWord acc)⟩ :=
        guardStep_succ _ bound suffix (encodeWord acc) v n ambient register
      have hb := bodyTrace t ⟨v, hv⟩ bound (encodeWord n ++ suffix) acc ambient none
      have ht := ih (v + 1) hnext
        (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, hv⟩) + acc) none
      have hall := appendTrace _ (appendTrace _ hg hb) ht
      simpa only [loopTime, cycleTime, dite_eq_left hv, sumFrom, amount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem prefixTrace (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t b suffix]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord b) [] [] []
          (encodeWord b ++ suffix) (encodeWord 0 ++ suffix)
          (encodeWord (PreprocessingPaddingOffsets.offset
            (PreprocessingRegularTables.padding t) b))⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
          (encodeWord b ++ suffix) [] (encodeWord 0)⟩ :=
    initStep _ _ ambient register
  have hc := MachineCopy.copyTrace Tape.bound Tape.remaining (Tape.inner .scratch)
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.guard) program rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
      (encodeWord b ++ suffix) [] (encodeWord 0)) rfl (ambient, false) register
  simp only [frame_bound, frame_remaining, List.append_nil, update_frame_remaining] at hc
  have hl := loopTrace t b 0 (by simpa only [Nat.zero_add] using hb)
    (encodeWord b ++ suffix) suffix 0 ambient none
  simp only [Nat.zero_add, Nat.add_zero, sumFrom_eq_offset t b hb] at hl
  exact appendTrace _ (appendTrace _ hi hc) hl

end BinPackingGames.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCloudSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

open BinPackingGames.Foundations.PCP

theorem cloudSelectSteps_le (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) :
    cloudSelectSteps t v i querySuffix ≤
      10 * ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length) + 20 := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have h := totalSteps_le t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val) querySuffix
    (tableWord_split t v e.val e.property)
  simpa only [cloudSelectSteps, e, MachineCloudCount.tableRows_input] using h

end BinPackingGames.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringGlobalEnumeration
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

end BinPackingGames.Foundations.Complexity.MachineAffineLookup

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

theorem rotorTrace (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (port : Fin d)
    (atLabels : ∀ l, program (labels l) = instruction tape d port.val labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table)
    (scratchEmpty : base (tape 6) = []) (suffix : List Bool)
    (sourceWord : base (tape 1) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table vertex port]
      (some ⟨some (labels (.reverse .seed)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape table vertex port base⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have hrDistinct : Function.Injective (reverseTapes tape) := distinct.comp reverseRole_injective
  have heDistinct : Function.Injective (endpointTapes tape) := distinct.comp endpointRole_injective
  have hrOutside : ∀ i, tape 1 ≠ reverseTapes tape i := fun i =>
    hd 1 (reverseRole i) (source_outside_reverse i)
  have heOutside : ∀ i, tape 4 ≠ endpointTapes tape i := fun i =>
    hd 4 (endpointRole i) (reverse_outside_endpoint i)
  have hreverse := MachineAffineLookup.affineLookupTrace (tape 1) (reverseTapes tape)
    hrDistinct hrOutside (4098 * d) (4098 * port.val + 3)
    (fun q => labels (.reverse q)) (some (labels (.endpoint .seed)))
    program (fun q => atLabels (.reverse q)) base (PortTables.tableWords table)
    tableWord scratchEmpty vertex.val suffix sourceWord (reverseId table vertex port)
    (reverse_selected table vertex port) ambient register
  let mid := afterReverse tape table vertex port base
  have hmidTable : mid (tape 0) = PortTables.tableBits table := by
    calc
      mid (tape 0) = base (tape 0) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 0 4 (by decide))
      _ = _ := tableWord
  have hmidScratch : mid (tape 6) = [] := by
    calc
      mid (tape 6) = base (tape 6) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 6 2 (by decide)) (hd 6 3 (by decide)) (hd 6 4 (by decide))
      _ = _ := scratchEmpty
  have hmidSource : mid (tape 4) = encodeWord (reverseId table vertex port) ++ base (tape 4) :=
    MachineAffineLookup.finalTapes_output _ _ _ _ _
  have hendpoint := MachineAffineLookup.affineLookupTrace (tape 4) (endpointTapes tape)
    heDistinct heOutside 4098 2 (fun q => labels (.endpoint q)) exit
    program (fun q => atLabels (.endpoint q)) mid (PortTables.tableWords table)
    hmidTable hmidScratch (reverseId table vertex port) (base (tape 4)) hmidSource
    ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) ambient none
  rw [steps, Nat.add_comm, Function.iterate_add_apply, hreverse]
  exact hendpoint

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    steps table vertex port ≤ 14 * (PortTables.tableBits table).length + 12 := by
  have hvertex : vertex.val ≤ (encodeWords (PortTables.tableWords table)).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
  have hreverse := MachineLookupSpec.output_length_le (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port) (reverse_selected table vertex port)
  rw [encodeWord_length] at hreverse
  have hr := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    vertex.val (4098 * d) (4098 * port.val + 3) (reverseId table vertex port)
    (reverse_selected table vertex port) hvertex
  have he := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    (reverseId table vertex port) 4098 2 ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) (by omega)
  change _ ≤ 14 * (encodeWords (PortTables.tableWords table)).length + 12
  unfold steps
  omega

end BinPackingGames.Foundations.Complexity.PoweringMachineRotor

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

theorem relationTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape port position labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table) (scratchEmpty : base (tape 4) = [])
    (suffix : List Bool) (sourceWord : base source = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (PortTables.tableWords table)
      vertex.val (4098 * d) (4098 * port.val + 4 + position.val)]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), MachineAffineLookup.finalTapes tape base
        (PortTables.tableWords table) (address vertex port position) (value table vertex port position)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside
    (4098 * d) (4098 * port.val + 4 + position.val) labels exit program atLabels
    base (PortTables.tableWords table) tableWord scratchEmpty vertex.val suffix sourceWord
    (value table vertex port position) (selected table vertex port position) ambient register

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    MachineAffineLookup.steps (PortTables.tableWords table) vertex.val
      (4098 * d) (4098 * port.val + 4 + position.val) ≤
      7 * (PortTables.tableBits table).length + 6 :=
  MachineAffineLookup.steps_le_table (PortTables.tableWords table) vertex.val
    (4098 * d) (4098 * port.val + 4 + position.val) (value table vertex port position)
    (selected table vertex port position)
    (Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table))

end BinPackingGames.Foundations.Complexity.PoweringMachineRelation

namespace BinPackingGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

theorem wordTrace (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (ports : Fin t → Fin d)
    (labels : Label t → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction t placement ports labels exit l)
    (base : K → List Bool) (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 4)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inr (first t))) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table t vertex ports]
      (some ⟨some (labels (entry t)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes table t placement vertex ports base⟩ ∧
    finalTapes table t placement vertex ports base (placement (.inl 5)) =
      encodeWord (PoweringWalks.wordEnd (PortTables.portGraph table) t vertex ports).val ++
        base (placement (.inl 5)) := by
  induction t generalizing vertex base suffix register with
  | zero =>
      have hd (i j : Tape 0) (hne : i ≠ j) : placement i ≠ placement j := fun h => hne (distinct h)
      have hrun := MachineUnaryAffineAt.seededAffineTrace
        (placement (.inr (first 0))) (placement (.inl 4)) (placement (.inl 5))
        (hd _ _ (by simp [first])) (hd _ _ (by simp [first])) (hd _ _ (by simp))
        1 0 (labels .seed) (labels .scan) (labels .restore) exit program
        (atLabels .seed) (atLabels .scan) (atLabels .restore)
        base vertex.val suffix sourceWord scratchEmpty ambient register
      constructor
      · simpa only [steps, entry, finalTapes, Nat.one_mul, Nat.add_zero] using hrun
      · simp only [finalTapes, Function.update_self, PoweringWalks.wordEnd]
  | succ t ih =>
      have hd (i j : Tape (t + 1)) (hne : i ≠ j) : placement i ≠ placement j :=
        fun h => hne (distinct h)
      have hrotor := PoweringMachineRotor.rotorTrace (placement ∘ rotorRole t)
        (distinct.comp (rotorRole_injective t)) (fun q => labels (.inl q))
        (some (labels (.inr (entry t)))) program (ports 0) (fun q => atLabels (.inl q))
        table vertex base tableWord scratchEmpty suffix sourceWord ambient register
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
        calc
          mid (placement (.inl 0)) = base (placement (.inl 0)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := tableWord
      have hmidScratch : mid (placement (.inl 4)) = [] := by
        calc
          mid (placement (.inl 4)) = base (placement (.inl 4)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := scratchEmpty
      have hmidOutput : mid (placement (.inl 5)) = base (placement (.inl 5)) :=
        PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
      have hmidSource : mid (placement (.inr (first t).succ)) =
          encodeWord (PortTables.rotation table (vertex, ports 0)).1.val ++
            base (placement (.inr (first t).succ)) :=
        PoweringMachineRotor.finalTapes_endpoint _ (distinct.comp (rotorRole_injective t)) _ _ _ _
      have htail := ih (placement ∘ shift t) (distinct.comp (shift_injective t))
        (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
        (fun q => labels (.inr q)) (fun q => atLabels (.inr q)) mid hmidTable hmidScratch
        (base (placement (.inr (first t).succ))) hmidSource none
      constructor
      · rw [steps, Nat.add_comm, Function.iterate_add_apply]
        simp only [entry]
        rw [hrotor]
        exact htail.1
      · change finalTapes table t (placement ∘ shift t)
          (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ) mid
          ((placement ∘ shift t) (.inl 5)) = _
        rw [htail.2]
        change _ ++ mid (placement (.inl 5)) = _
        rw [hmidOutput]
        rfl

theorem steps_le (table : PortTables.Table n d) (t : Nat)
    (vertex : Fin n) (ports : Fin t → Fin d) :
    steps table t vertex ports ≤ (14 * t + 2) * (PortTables.tableBits table).length + 12 * t + 3 := by
  induction t generalizing vertex with
  | zero =>
      have h := Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
      simp only [steps, Nat.mul_zero, Nat.zero_add]
      omega
  | succ t ih =>
      have hr := PoweringMachineRotor.steps_le table vertex (ports 0)
      have ht := ih (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
      simp only [steps, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at ht ⊢
      omega

end BinPackingGames.Foundations.Complexity.PoweringMachineWord

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

theorem fieldTrace (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement path lengthBound port left right labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 5)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix) (ambient : A) :
    (advance (TM2.step program))^[steps path port left right table vertex]
      (some ⟨some (labels (.inl (PoweringMachineWord.entry path.length))), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes placement path lengthBound port left right table vertex base⟩ ∧
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl 10)) =
      encodeWord (bit table vertex path port left right) ++ base (placement (.inl 10)) := by
  have hword := PoweringMachineWord.wordTrace table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective lengthBound false)) vertex path.get
    (fun q => labels (.inl q)) (some (labels (.inr .seed))) program
    (fun q => atLabels (.inl q)) base (by simpa [PoweringMachineTapes.table] using tableWord)
    (by simpa [PoweringMachineTapes.scratch] using scratchEmpty) suffix
    (by simpa [PoweringMachineTapes.start] using sourceWord) (ambient, false, none) none
  let mid := afterWord placement path lengthBound table vertex base
  have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 0
      (by decide) (by decide) (by decide) (by decide)]
    exact tableWord
  have hmidScratch : mid (placement (.inl 5)) = [] := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 5
      (by decide) (by decide) (by decide) (by decide)]
    exact scratchEmpty
  have hmidOutput : mid (placement (.inl 10)) = base (placement (.inl 10)) :=
    afterWord_frame placement distinct path lengthBound table vertex base 10
      (by decide) (by decide) (by decide) (by decide)
  have hmidEndpoint : mid (placement (.inl 6)) = encodeWord (endpoint table vertex path).val ++
      base (placement (.inl 6)) := by
    dsimp only [mid, afterWord]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five, PoweringMachineTapes.endpoint_false,
      PoweringMachineTapes.leftEndpoint, ← endpoint_eq_wordEnd] using hword.2
  have hrelation := PoweringMachineRelation.relationTrace (placement (.inl 6)) (lookupTapes placement)
    (lookupTapes_injective placement distinct) (source_outside_lookup placement distinct)
    port (GraphTables.relationIndex (left, right)) (fun q => labels (.inr q)) exit program
    (fun q => atLabels (.inr q)) table (endpoint table vertex path) mid
    (by simpa [lookupTapes, PoweringMachineTapes.table] using hmidTable)
    (by simpa [lookupTapes, PoweringMachineTapes.scratch] using hmidScratch)
    (base (placement (.inl 6))) hmidEndpoint (ambient, false, none) none
  constructor
  · simp only [MachineUnaryEqualityBit.clean]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, hword.1]
    exact hrelation
  · change MachineAffineLookup.finalTapes (lookupTapes placement) _ _ _ _ (lookupTapes placement 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord (bit table vertex path port left right) ++ mid (placement (.inl 10)) = _
    rw [hmidOutput]

theorem steps_le (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) :
    steps path port left right table vertex ≤
      (14 * path.length + 9) * (PortTables.tableBits table).length + 12 * path.length + 9 := by
  have hw := PoweringMachineWord.steps_le table path.length vertex path.get
  have hr := PoweringMachineRelation.steps_le table (endpoint table vertex path) port
    (GraphTables.relationIndex (left, right))
  simp only [steps, Nat.add_mul, Nat.mul_assoc] at hw ⊢
  omega

end BinPackingGames.Foundations.Complexity.PoweringMachineRelationField

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineLazyRows
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem affined_other (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₆ : k ≠ 6) (h₇ : k ≠ 7) :
    affined q t e base k = base k := by
  simp only [affined, Function.update_of_ne h₆, copied_other t e base k h₂ h₃ h₄ h₇]

theorem affined_fields (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineTableRows.fieldBits fields (affined q t e base) = encodeWords (emittedWords q t e) := by
  have htail := affined_other q t e base 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simp only [MachineTableRows.fieldBits, fields_zero, fields_one, fields_two,
    htail, input.indexWord, affined_reverse, input.computedEmpty,
    affined_relation, input.relationEmpty, List.append_nil,
    emittedWords, encodeWords, List.append_assoc]

section Execution

variable {Λ σ : Type}

theorem lookupTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩ := by
  exact MachineAffineLookup.affineLookupTrace 0 lookupTape lookupTape_injective source_outside
    4098 3 (fun l => labels (.lookup l)) (some (labels .copyRelation)) program
    (fun l => code (.lookup l)) base (GraphTables.tableWords t) input.tableWord input.scratchEmpty
    e.val [] (by simpa only [List.append_nil] using input.indexWord)
    t.rows[e].reverseIndex.val (selected_reverse t e) (ambient, zeroBuffer) register

theorem affineTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[2 * (t.rows[e].reverseIndex.val + 1) + 1]
      (some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩) =
      some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none),
        affined q t e base⟩ := by
  have hsource : copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ [] := by
    rw [copied_reverse, input.reverseEmpty]
  have hscratch : copied t e base 5 = [] := by
    rw [copied_other t e base 5 (by decide) (by decide) (by decide) (by decide), input.scratchEmpty]
  have run := MachineUnaryAffineAt.seededAffineTrace (4 : Tape) 5 6 (by decide) (by decide)
    (by decide) (q + 1) q (labels .reverseSeed) (labels .reverseScan) (labels .reverseRestore)
    (some (labels (.emit .relationRead))) program (code .reverseSeed) (code .reverseScan)
    (code .reverseRestore) (copied t e base) t.rows[e].reverseIndex.val [] hsource hscratch
    (ambient, zeroBuffer) none
  rw [copied_other t e base 6 (by decide) (by decide) (by decide) (by decide)] at run
  exact run

theorem emitTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[rowSteps q t e base]
      (some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none), affined q t e base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hrow : affined q t e base 8 = [] := by
    rw [affined_other q t e base 8 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.rowEmpty]
  have hscratch : affined q t e base 5 = [] := by
    rw [affined_other q t e base 5 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.scratchEmpty]
  have hout := affined_other q t e base 9 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hfields := affined_fields q t e base input
  have hsize : MachineTableRows.fieldSize fields (affined q t e base) =
      (encodeWords (emittedWords q t e)).length := by
    rw [← MachineTableRows.fieldBits_length, hfields]
  have run := MachineTableRows.appendTrace fields (8 : Tape) 9 5 fields_separate
    (by decide) (by decide) (by decide) (fun l => labels (.emit l)) exit program
    (fun l => code (.emit l)) (affined q t e base) hrow hscratch (ambient, zeroBuffer) none
  rw [hsize, hout, hfields] at run
  exact run

theorem traceAt (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hlookup := lookupTrace q labels exit program code t e base input ambient register
  have hcopy := copyTrace q labels exit program code t e base ambient
  have haffine := affineTrace q labels exit program code t e base input ambient
  have hemit := emitTrace q labels exit program code t e base input ambient
  exact join_trace (join_trace (join_trace hlookup hcopy) haffine) hemit

end Execution

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalRow

namespace BinPackingGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

theorem reindexRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = reindexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        reindexResultTapes d c b v j relation tape base⟩ := by
  have hd (i k : Fin 9) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  have ha0 : addressIndex 0 = 1 := rfl
  have ha4 : addressIndex 4 = 6 := rfl
  have mapRun := MachinePortReindex.reindexTrace d positive c b
    (tape ∘ addressIndex) (distinct.comp addressIndex_injective)
    (fun stage => labels (.inl stage)) (some (labels (.inr .relationRead)))
    program (fun stage => atLabels (.inl stage)) base j []
    (by simpa only [Function.comp_apply, ha0, List.append_nil] using reverseWord)
    scratchEmpty workEmpty quotientEmpty ambient
  simp only [Function.comp_apply, ha4, newReverseEmpty,
    List.append_nil] at mapRun
  change (advance (TM2.step program))^[MachinePortReindex.steps d j]
    (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
    some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩ at mapRun
  have hfields (i : Fin 3) : fields tape i ≠ tape 8 ∧ fields tape i ≠ tape 3 := by
    fin_cases i
    · exact ⟨hd 0 8 (by decide), hd 0 3 (by decide)⟩
    · exact ⟨hd 6 8 (by decide), hd 6 3 (by decide)⟩
    · exact ⟨hd 2 8 (by decide), hd 2 3 (by decide)⟩
  have hbits : MachineTableRows.fieldBits (fields tape) (reindexMappedTapes d c b j tape base) =
      reindexRowBits d c b v j relation := by
    simp [MachineTableRows.fieldBits, fields, reindexMappedTapes, hd 0 6 (by decide),
      hd 2 6 (by decide), tailWord, relationWord, reindexRowBits]
  have hsize : MachineTableRows.fieldSize (fields tape) (reindexMappedTapes d c b j tape base) =
      (reindexRowBits d c b v j relation).length := by
    rw [← MachineTableRows.fieldBits_length, hbits]
  have hout : reindexMappedTapes d c b j tape base (tape 7) = base (tape 7) := by
    simp [reindexMappedTapes, hd 7 6 (by decide)]
  have appendRun := MachineTableRows.appendTrace (fields tape) (tape 8) (tape 7) (tape 3)
    hfields (hd 8 7 (by decide)) (hd 8 3 (by decide)) (hd 7 3 (by decide))
    (fun stage => labels (.inr stage)) exit program
    (fun stage => atLabels (.inr stage)) (reindexMappedTapes d c b j tape base)
    (by simp [reindexMappedTapes, hd 8 6 (by decide), rowEmpty])
    (by simp [reindexMappedTapes, hd 3 6 (by decide), scratchEmpty])
    (ambient, MachineFixedDivMod.residue d positive 0) none
  rw [hsize, hout, hbits] at appendRun
  change (advance (TM2.step program))^[4 * (reindexRowBits d c b v j relation).length +
      2 * (base (tape 7)).length + 9]
    (some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩) =
    some ⟨exit, MachinePortReindex.clean d positive ambient,
      reindexResultTapes d c b v j relation tape base⟩ at appendRun
  rw [show reindexSteps d c b v j relation (base (tape 7)) =
      (4 * (reindexRowBits d c b v j relation).length + 2 * (base (tape 7)).length + 9) +
        MachinePortReindex.steps d j by unfold reindexSteps; omega,
    Function.iterate_add_apply, mapRun, appendRun]

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

theorem vertexSuffixTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A)
    (remaining : Nat) (i : Fin (d + 1)) (count : i.val + remaining = d) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b ((List.ofFn rows).drop i.val) output]
      (some ⟨some (labels (i, none)), streamClean d positive ambient,
        streamFrame tape base ((List.ofFn rows).drop i.val) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b ((List.ofFn rows).drop i.val))⟩ := by
  have hd (a k : Fin 10) (h : a ≠ k) : tape a ≠ tape k := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = d := by omega
      have hdrop : (List.ofFn rows).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, recordsOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < d := by omega
      let port : Fin d := ⟨i.val, hi⟩
      let next : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn rows).drop (i.val + 1)
      have split : (List.ofFn rows).drop i.val = rows port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn rows)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (rows port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), streamClean d positive ambient, initial⟩) =
          some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := streamRowTrace d positive c b tape distinct
        (fun stage => labels (i, some stage)) (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using (atLabels (i, some stage)))
        initial (rows port).tail.val (rows port).reverseIndex.val (rows port).relation
        (recordsInput rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 9 7 (by decide), recordsInput, List.append_assoc])
        (by
          intro k hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[streamRowSteps d c b
        (rows port).tail.val (rows port).reverseIndex.val (rows port).relation output]
        (some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
            (rows port).relation tape initial (recordsInput rest ++ base (tape 9))⟩ at body
      rw [show streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
        (rows port).relation tape initial (recordsInput rest ++ base (tape 9)) =
        streamFrame tape base rest
          (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) from
          streamFrame_afterRow d c b (rows port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = d := by dsimp [next]; omega
      have tail := ih next nextCount
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)
      change (advance (TM2.step program))^[vertexSteps d c b rest
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)]
        (some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamFrame tape base rest (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation)⟩) =
        some ⟨exit, streamClean d positive ambient,
          streamFrame (n := n) (m := m) tape base [] ((output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) ++ recordsOutput d c b rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, recordsOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b (List.ofFn rows) output]
      (some ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base [] (output ++ recordsOutput d c b (List.ofFn rows))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d positive c b tape distinct
    labels exit program atLabels base rows empty ambient d 0 (by simp) output

end BinPackingGames.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineVertexPadding
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def execution {n d m : Nat} (table : PortTables.Table n d) (h : n ≤ m) (hd : 0 < d) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize_), (((), none), ()),
        initialTapes n (n * d) (m - n) (initialOutput (m := m) table)⟩
      (some (cfg d none m (m * d) 0
        (PortTables.tableBits (PreprocessingPaddingTables.pad table h))))
      ((MachinePaddingCertificate.timePolynomial d).eval
        (MachinePaddingBounds.inputSize n (n * d) (m - n) (initialOutput (m := m) table))) where
  steps := steps d n (n * d) (initialOutput (m := m) table) (m - n) + 1
  evals_in_steps := by
    have run := paddingTrace d hd (m - n) n (n * d) (initialOutput (m := m) table)
    have hv : n + (m - n) = m := Nat.add_sub_of_le h
    have he : n * d + (m - n) * d = m * d := by rw [← Nat.add_mul, hv]
    have hout : initialOutput (m := m) table ++ paddingBits d n (n * d) (m - n) =
        PortTables.tableBits (PreprocessingPaddingTables.pad table h) := by
      rw [PreprocessingPaddingWords.tableBits_pad]
      rfl
    rw [hv, he, hout] at run
    convert run using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  steps_le_m := by
    simp only [MachinePaddingCertificate.timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d n (n * d) (m - n) (initialOutput (m := m) table)) 1

end BinPackingGames.Foundations.Complexity.MachinePaddingTable

namespace BinPackingGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open BinPackingGames.Foundations.PCP
open MachineCloudPadding

theorem subtractTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge power level : List Bool) (n m : Nat) (hnm : n ≤ m)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * n + 2]
      (some ⟨some (.subtractCode .subtract), ((ambient, false), register),
        memory input output (encodeWord n) edge power level (encodeWord m) []⟩) =
      some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input output (encodeWord n) edge power level (encodeWord (m - n)) []⟩ := by
  have h := Placement.trace subtractTape subtractView subtractView_left subtractView_right
    (Label.subtractCode (d := d)) (some (.rowsCode (.inr .initialize_)))
    (memory [] [] [] edge power [] [] [])
    (MachineCloudPadding.program (σ := σ)) (program d hd) (fun _ => rfl) _ _ _
    (MachineCloudPadding.subtractTrace input output level n m hnm ambient register)
  simpa only [Placement.configuration, Placement.label, subtractTapes] using h

theorem rowInitialTapes (input power level output : List Bool) (v e fuel : Nat) :
    Placement.tapes rowView (rowBoolTapes (MachinePaddingRows.initialTapes v e fuel output))
      (memory input [] [] [] power level [] []) =
      memory input output (encodeWord v) (encodeWord e) power level (encodeWord fuel) [] := by
  funext k
  cases k <;> rfl

theorem rowFinalTapes (input power level output : List Bool) (v e fuel : Nat) :
    Placement.tapes rowView (rowBoolTapes (MachinePaddingRows.tapes v e fuel output))
      (memory input [] [] [] power level [] []) =
      memory input output (encodeWord v) (encodeWord e) power level (encodeWord fuel)
        MachineDummyRows.trueBits := by
  funext k
  cases k <;> rfl

def rowTime {n d m : Nat} (t : PortTables.Table n d) : Nat :=
  MachinePaddingRows.steps d n (n * d) (MachinePaddingTable.initialOutput (m := m) t) (m - n) + 1

theorem rowsTrace {σ : Type} {n d m : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (hnm : n ≤ m) (input power level : List Bool) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[rowTime (m := m) t]
      (some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input (MachinePaddingTable.initialOutput (m := m) t)
          (encodeWord n) (encodeWord (n * d)) power level (encodeWord (m - n)) []⟩) =
      some ⟨some .cleanVertex, ((ambient, false), none),
        memory input (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))
          (encodeWord m) (encodeWord (m * d)) power level (encodeWord 0)
          MachineDummyRows.trueBits⟩ := by
  have hraw := (MachinePaddingTable.execution t hnm hd).evals_in_steps
  change (advance (TM2.step (MachinePaddingRows.program d hd)))^[rowTime (m := m) t]
    (some ⟨some (.inr .initialize_), (((), none), ()),
      MachinePaddingRows.initialTapes n (n * d) (m - n)
        (MachinePaddingTable.initialOutput (m := m) t)⟩) =
    some (MachinePaddingRows.cfg d none m (m * d) 0
      (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))) at hraw
  have hb := MachineAlphabetTransport.successfulTrace rowAlphabet_eq
    (MachinePaddingRows.program d hd) _ _ _ hraw
  have hf := frameTrace
    (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd))
    (ambient, false) _ _ _ hb
  have hs := MachineStateEquiv.trace (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))
    _ _ _ hf
  have hp := Placement.trace rowTape rowView rowView_left rowView_right
    (Label.rowsCode (d := d)) (some .cleanVertex) (memory input [] [] [] power level [] [])
    (rowProgram d hd (σ := σ)) (program d hd) (fun _ => rfl) _ _ _ hs
  simpa only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    MachineStateFrame.frameConfiguration, MachineAlphabetTransport.configuration_mk,
    rowCastTapes, MachinePaddingRows.cfg, rowStateEquiv, Equiv.coe_fn_mk,
    rowInitialTapes, rowFinalTapes] using hp

theorem cleanupTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output level : List Bool) (m : Nat) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[cleanupTime d m]
      (some ⟨some .cleanVertex, ((ambient, false), none),
        memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
          (encodeWord 0) MachineDummyRows.trueBits⟩) =
      some ⟨none, ((ambient, false), none), memory input output [] [] [] level [] []⟩ := by
  have h₁ := (MachineDrain.drainInTime Tape.vertex (Label.cleanVertex (d := d)) (some .cleanEdge)
    (program d hd) rfl
    (memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₂ := (MachineDrain.drainInTime Tape.edge (Label.cleanEdge (d := d)) (some .cleanPower)
    (program d hd) rfl
    (memory input output [] (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₃ := (MachineDrain.drainInTime Tape.power (Label.cleanPower (d := d)) (some .cleanRelation)
    (program d hd) rfl
    (memory input output [] [] (encodeWord m) level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₄ := (MachineDrain.drainInTime Tape.relation (Label.cleanRelation (d := d)) (some .cleanFuel)
    (program d hd) rfl
    (memory input output [] [] [] level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₅ := (MachineDrain.drainInTime Tape.fuel (Label.cleanFuel (d := d)) none
    (program d hd) rfl (memory input output [] [] [] level (encodeWord 0) [])
    (ambient, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, memory, encodeWord_length, MachineDummyRows.trueBits_length,
    update_vertex, update_edge, update_power, update_relation, update_fuel] at h₁ h₂ h₃ h₄ h₅
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅
  have ht : cleanupTime d m = (((m + 2 + (m * d + 2)) + (m + 2)) + 8193) + 2 := by
    unfold cleanupTime
    omega
  rw [ht]
  exact h

def totalTime {n d : Nat} (t : PortTables.Table n d) : Nat :=
  otherTime t + rowTime (m := PreprocessingLevels.paddedSize n) t

theorem vertexPaddingTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[totalTime t]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  let m := PreprocessingLevels.paddedSize n
  let level := encodeWord (PreprocessingLevels.boundedLevel n)
  let input := PortTables.tableBits t
  let rows := PreprocessingPaddingWords.rowsBits t
  let initialOutput := MachinePaddingTable.initialOutput (m := m) t
  have h₁ := splitTrace hd t ambient register
  have h₂ := powerTrace d hd input rows (encodeWord (n * d)) n ambient none
  have h₃ := headersTrace d hd input rows (encodeWord n) (encodeWord (n * d)) level m ambient none
  have h₄ := copyPowerTrace d hd input initialOutput (encodeWord n) (encodeWord (n * d))
    level m ambient none
  have h₅ := subtractTrace d hd input initialOutput (encodeWord (n * d)) (encodeWord m)
    level n m (PreprocessingLevels.le_paddedSize n) ambient none
  have h₆ := rowsTrace hd t (PreprocessingLevels.le_paddedSize n) input (encodeWord m) level ambient
  have h₇ := cleanupTrace d hd input
    (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
    level m ambient
  have h := appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _
    (appendTrace _ (appendTrace _ h₁ h₂) h₃) h₄) h₅) h₆) h₇
  have ht : totalTime t =
      (((((MachineTableSplit.exactSteps n (n * d) rows +
        MachineCeilingPower.totalTime ExpanderFamily.growth n) + (4 * (m + 1) + 2)) +
        (2 * (m + 2))) + (2 * n + 2)) + rowTime (m := m) t) + cleanupTime d m := by
    dsimp only [totalTime, otherTime, m, rows]
    omega
  rw [ht]
  exact h

theorem totalTime_le {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    totalTime t ≤ (timePolynomial d).eval (PortTables.tableBits t).length := by
  have hrow := (MachinePaddingTable.execution t (PreprocessingLevels.le_paddedSize n) hd).steps_le_m
  change rowTime (m := PreprocessingLevels.paddedSize n) t ≤
    (MachinePaddingCertificate.timePolynomial d).eval
      (MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
        (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t)) at hrow
  have hmono := natPolynomial_eval_mono (MachinePaddingCertificate.timePolynomial d) (intermediate_bound t)
  have h := Nat.add_le_add (otherTime_le t) (hrow.trans hmono)
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp] using h

def vertexPaddingInTime {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program d hd))
      ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) where
  steps := totalTime t
  evals_in_steps := vertexPaddingTrace hd t ambient register
  steps_le_m := totalTime_le hd t

end BinPackingGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

theorem dummyTrace (d : Nat) (positive : 0 < d) (base : Tape → List Bool) (v e : Nat)
    (ht : base .tail = encodeWord v) (he : base .reverse = encodeWord e)
    (hr : base .relation = []) (hb : base .rowBuffer = []) (hs : base .scratch = []) :
    (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v e (base .output) d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, base⟩) =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
          .relation MachineDummyRows.trueBits)
          .output (base .output ++ MachineDummyRows.rowsBits v e d)⟩ := by
  have initial : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.initialTapes v e (base .output)) base = base := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes, ht, he, hr, hb, hs]
  have final : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.fieldTapes v (e + d) (base .output ++ MachineDummyRows.rowsBits v e d))
      base = Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
        .relation MachineDummyRows.trueBits)
        .output (base .output ++ MachineDummyRows.rowsBits v e d) := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.fieldTapes, ht, hb, hs]
  have run := MachineCloudPadding.Placement.trace dummyRoles dummyView
    dummyRoles_left dummyRoles_right Label.dummy (some .clearDummyTail) base
    (MachineDummyRows.program d) (program d positive) (fun _ => rfl) _ _ _
    (MachineDummyRows.allTrace d v e (base .output) (clean d positive).1 none)
  simpa only [clean_pair, MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, initial, final] using run

theorem oldTrace {n m : Nat} (d : Nat) (positive : 0 < d)
    (base : Tape → List Bool) (rows : Fin d → GraphTables.DartRow n m) (rest : List Bool)
    (hi : base .source = MachineLazyRows.recordsInput (List.ofFn rows) ++ rest)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (oldRoles i) = []) :
    (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (base .output)]
      (some ⟨some (.oldRows (0, none)), clean d positive, base⟩) =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update base .source rest) .output
          (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows))⟩ := by
  let tailBase := Function.update base Tape.source rest
  have cleanBase : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → tailBase (oldRoles i) = [] := by
    intro i h7 h9
    have hn : oldRoles i ≠ Tape.source := by
      intro h
      have h' : oldRoles i = oldRoles 9 := h
      exact h9 (oldRoles_injective h')
    simpa only [tailBase, Function.update_of_ne hn] using empty i h7 h9
  have initial : MachineLazyRows.streamFrame oldRoles tailBase (List.ofFn rows) (base .output) = base := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, tailBase, oldRoles, hi]
  have final : MachineLazyRows.streamFrame (n := n) (m := m) oldRoles tailBase []
      (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) =
      Function.update (Function.update base .source rest) .output
        (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, MachineLazyRows.recordsInput, tailBase, oldRoles]
  have run := MachineLazyRows.vertexTrace d positive (2 * d) d oldRoles oldRoles_injective
    Label.oldRows (some .nextVertex) (program d positive) (fun _ => rfl)
    tailBase rows cleanBase () (base .output)
  simpa only [initial, final, clean] using run

def vertexBlock {n m : Nat} (d v : Nat) (rows : Fin d → GraphTables.DartRow n m) : List Bool :=
  MachineDummyRows.rowsBits v (2 * d * v) d ++
    MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)

def bodySteps {n m : Nat} (d v : Nat) (rows : Fin d → GraphTables.DartRow n m)
    (output : List Bool) : Nat :=
  2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) + (v + 2) + 8193 +
    MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows)
      (output ++ MachineDummyRows.rowsBits v (2 * d * v) d) + 1

theorem bodyTrace {n m : Nat} (d : Nat) (positive : 0 < d) (input : List Bool)
    (left v : Nat) (rows : Fin d → GraphTables.DartRow n m) (rest output : List Bool) :
    (advance (TM2.step (program d positive)))^[bodySteps d v rows output]
      (some ⟨some .copyVertexFirst, clean d positive,
        loopTapes d input n m left v (MachineLazyRows.recordsInput (List.ofFn rows) ++ rest) output⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
  let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let moving := MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)
  let b₀ := loopTapes d input n m left v source output
  let b₁ := Function.update b₀ Tape.tail (encodeWord v)
  let b₄ := frame input source (output ++ dummy) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  let b₂ := Function.update (Function.update b₄ Tape.tail (encodeWord v))
    Tape.relation MachineDummyRows.trueBits
  let b₃ := Function.update b₄ Tape.relation MachineDummyRows.trueBits
  let b₅ := frame input rest ((output ++ dummy) ++ moving) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  have hcopy : Function.update b₀ Tape.tail (b₀ .vertex ++ b₀ .tail) = b₁ := by
    simp [b₀, b₁, loopTapes, frame]
  have copy := MachineCopy.copyTrace Tape.vertex .tail .scratch
    (by decide) (by decide) (by decide) false .copyVertexFirst .copyVertexSecond
    (some (.dummy (MachineDummyRows.start d))) (program d positive) rfl rfl b₀ rfl
    (clean d positive).1 none
  rw [hcopy] at copy
  have c₀ : (advance (TM2.step (program d positive)))^[2 * (v + 2)]
      (some ⟨some .copyVertexFirst, clean d positive, b₀⟩) =
      some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩ := by
    simpa only [clean_pair, show b₀ .vertex = encodeWord v from rfl, encodeWord_length,
      Nat.add_assoc] using copy
  have hdummy : Function.update (Function.update (Function.update b₁ Tape.reverse
      (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
      Tape.output (b₁ .output ++ dummy) = b₂ := by
    funext t; cases t <;> simp [b₀, b₁, b₂, b₄, loopTapes, frame]
  have dummies := dummyTrace d positive b₁ v (2 * d * v)
    (by simp [b₁]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame])
  have c₁ : (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v
      (2 * d * v) output d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩) =
      some ⟨some .clearDummyTail, clean d positive, b₂⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update b₁ Tape.reverse
          (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
          Tape.output (b₁ .output ++ dummy)⟩ at dummies
    rw [hdummy] at dummies
    simpa only [show b₁ .output = output by simp [b₁, b₀, loopTapes, frame]] using dummies
  have ht : Function.update b₂ Tape.tail [] = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, b₄, frame]
  have drainTail := MachineDrain.drainTrace Tape.tail .clearDummyTail (some .clearDummyRelation)
    (program d positive) rfl b₂ (b₂ .tail) (clean d positive).1 none
  simp only [Function.update_eq_self, ht] at drainTail
  have c₂ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearDummyTail, clean d positive, b₂⟩) =
      some ⟨some .clearDummyRelation, clean d positive, b₃⟩ := by
    simpa only [clean_pair, show b₂ .tail = encodeWord v by simp [b₂], encodeWord_length,
      Nat.add_assoc] using drainTail
  have hr : Function.update b₃ Tape.relation [] = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have drainRelation := MachineDrain.drainTrace Tape.relation .clearDummyRelation
    (some (.oldRows (0, none))) (program d positive) rfl b₃ (b₃ .relation)
    (clean d positive).1 none
  simp only [Function.update_eq_self, hr] at drainRelation
  have c₃ : (advance (TM2.step (program d positive)))^[8193]
      (some ⟨some .clearDummyRelation, clean d positive, b₃⟩) =
      some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .relation = MachineDummyRows.trueBits by simp [b₃],
      MachineDummyRows.trueBits_length] using drainRelation
  have hmoving : Function.update (Function.update b₄ Tape.source rest) Tape.output
      (b₄ .output ++ moving) = b₅ := by
    funext t; cases t <;> simp [b₄, b₅, frame]
  have old := oldTrace d positive b₄ rows rest rfl
    (fun i h7 h9 => frame_old_empty _ _ _ _ _ _ _ _ i h7 h9)
  have c₄ : (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (output ++ dummy)]
      (some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩) =
      some ⟨some .nextVertex, clean d positive, b₅⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update b₄ Tape.source rest) Tape.output
          (b₄ .output ++ moving)⟩ at old
    rw [hmoving] at old
    exact old
  have c₅ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .nextVertex, clean d positive, b₅⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
    have hrev : List.replicate d true ++ encodeWord (2 * d * v + d) =
        encodeWord (2 * d * (v + 1)) := by
      have hw := MachineUnaryAffineAt.prepend_replicate_word d (2 * d * v + d) []
      simp only [List.append_nil] at hw
      rw [hw]
      exact congrArg encodeWord (show d + (2 * d * v + d) = 2 * d * (v + 1) by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have ht : Function.update (Function.update b₅ Tape.reverse
        ((List.replicate d true).reverse ++ b₅ .reverse)) Tape.vertex (true :: b₅ .vertex) =
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows) := by
      funext t
      cases t <;> simp [b₅, frame, loopTapes, vertexBlock, dummy, moving,
        hrev, List.append_assoc]
      simp [encodeWord, List.replicate_succ]
    simp only [Function.iterate_one, advance_some, TM2.step, program,
      stepAux_pushWord, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  exact all

def outputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => vertexBlock d v.val (PreprocessingLazyWords.row table v))

theorem vertexBlock_codec {n d : Nat} (table : PortTables.Table n d) (v : Fin n) :
    vertexBlock d v.val (PreprocessingLazyWords.row table v) =
      encodeWords ((PreprocessingLazyWords.vertexRows table v).flatMap GraphTables.rowWords) := by
  rw [vertexBlock, MachineLazyCodec.rowsBits_stay, MachineLazyRows.recordsOutput_lazy,
    PreprocessingLazyWords.vertexRows, List.flatMap_append, encodeWords_append]

theorem outputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    outputBlocks table events = encodeWords
      ((events.flatMap (PreprocessingLazyWords.vertexRows table)).flatMap GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [outputBlocks, vertexBlock_codec]

theorem output_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits (PreprocessingOverlayTables.lazy table) =
      encodeWords [n, 2 * (n * d)] ++ outputBlocks table (List.finRange n) := by
  rw [outputBlocks_codec, PreprocessingLazyWords.tableBits_lazy, encodeWords_append]
  have hm : n * (2 * d) = 2 * (n * d) := by ac_rfl
  have hrows : (List.ofFn (PreprocessingLazyWords.vertexRows table)).flatten =
      (List.finRange n).flatMap (PreprocessingLazyWords.vertexRows table) := by
    rw [List.ofFn_eq_map]
    rfl
  exact congrArg₂ List.append (congrArg (fun k => encodeWords [n, k]) hm)
    (congrArg (fun rows => encodeWords (rows.flatMap GraphTables.rowWords)) hrows)

def loopSteps {n d : Nat} (table : PortTables.Table n d) (r : Nat) : Nat → List Bool → Nat
  | 0, _ => finishSteps d n (n * d) r
  | count + 1, output => if h : r < n then
      (1 + bodySteps d r (PreprocessingLazyWords.row table ⟨r, h⟩) output) +
        loopSteps table (r + 1) count
          (output ++ vertexBlock d r (PreprocessingLazyWords.row table ⟨r, h⟩))
      else 0

theorem loopTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d)
    (input : List Bool) (count r : Nat) (hsum : r + count = n) (output : List Bool) :
    (advance (TM2.step (program d positive)))^[loopSteps table r count output]
      (some ⟨some .guard, clean d positive,
        loopTapes d input n (n * d) count r (inputBlocks table (remaining n r)) output⟩) =
      some ⟨none, clean d positive,
        finalTapes input (output ++ outputBlocks table (remaining n r))⟩ := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    simpa only [loopSteps, remaining_done, inputBlocks, outputBlocks, List.flatMap_nil,
      List.append_nil] using finishTrace d positive input output n (n * d) n
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    let rest := inputBlocks table (remaining n (r + 1))
    let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
    let b₀ := loopTapes d input n (n * d) (count + 1) r source output
    let b₁ := loopTapes d input n (n * d) count r source output
    have hguard (k : Nat) : MachineUnaryCounter.counterTapes Tape.fuel b₀ k [] =
        loopTapes d input n (n * d) k r source output := by
      funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
    have guard := MachineUnaryCounter.guardTrace_succ Tape.fuel .guard .copyVertexFirst
      .clearVertices (program d positive) rfl b₀ count [] (clean d positive).1 none
    have c₀ : (advance (TM2.step (program d positive)))^[1]
        (some ⟨some .guard, clean d positive, b₀⟩) =
        some ⟨some .copyVertexFirst, clean d positive, b₁⟩ := by
      simpa only [hguard, clean_pair] using guard
    have c₁ := bodyTrace d positive input count r rows rest output
    have c₂ := ih (r + 1) (by omega) (output ++ vertexBlock d r rows)
    have all := joinTrace (joinTrace c₀ c₁) c₂
    have hi : inputBlocks table (remaining n r) = source := by
      rw [remaining_cons n r hr]
      rfl
    have ho : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    simpa only [loopSteps, dite_eq_left hr, hi, ho, List.append_assoc] using all

def totalSteps {n d : Nat} (table : PortTables.Table n d) : Nat :=
  prefixSteps n (n * d) (inputBlocks table (List.finRange n)) +
    loopSteps table 0 n (encodeWords [n, 2 * (n * d)])

theorem tableTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    (advance (TM2.step (program d positive)))^[totalSteps table]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes (PortTables.tableBits table)⟩) =
      some ⟨none, clean d positive,
        finalTapes (PortTables.tableBits table)
          (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩ := by
  have prefixRun := prefixTrace d positive n (n * d) (inputBlocks table (List.finRange n))
  rw [← input_table_codec table] at prefixRun
  have loop := loopTrace table positive (PortTables.tableBits table) n 0 (by omega)
    (encodeWords [n, 2 * (n * d)])
  simp only [remaining_zero] at loop
  have all := joinTrace prefixRun loop
  rw [← output_table_codec table] at all
  exact all

theorem dummyRows_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    have h := ih (e + 1)
    have he : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [he] at h
    nlinarith only [h]

theorem bodySteps_le {n d : Nat} (rows : Fin d → GraphTables.DartRow n (n * d))
    (v L : Nat) (output : List Bool) (hv : v ≤ n) (hn : n ≤ L) (hm : n * d ≤ L)
    (ho : output.length ≤ 20000 * (L + 1) ^ 2) :
    bodySteps d v rows output ≤ 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by
  let D := d + 1
  let N := L + 1
  let P := D * N
  let Q := P * P
  let S := v + 2 * d * v + d + 8194
  let V := (2 * d) * (n * d) + n * d + d
  let R := n + V + 8194
  let C := 2 * n + 8 * (n * d) + V + 4 * R + 8224
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let after := output ++ dummy
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hdD : d ≤ D := by dsimp [D]; omega
  have hLN : L ≤ N := by dsimp [N]; omega
  have hDP : D ≤ P := by
    have h := Nat.mul_le_mul_left D hN
    simpa [P] using h
  have hNP : N ≤ P := by
    have h := Nat.mul_le_mul_right N hD
    simpa [P] using h
  have hP : 1 ≤ P := hN.trans hNP
  have hPQ : P ≤ Q := by
    have h := Nat.mul_le_mul_right P hP
    simpa [Q] using h
  have hQ : 1 ≤ Q := hP.trans hPQ
  have hdP : d ≤ P := hdD.trans hDP
  have hvN : v ≤ N := hv.trans (hn.trans hLN)
  have hvP : v ≤ P := hvN.trans hNP
  have hnP : n ≤ P := hn.trans (hLN.trans hNP)
  have hmN : n * d ≤ N := hm.trans hLN
  have hmP : n * d ≤ P := hmN.trans hNP
  have hdv : d * v ≤ P := by simpa [P] using Nat.mul_le_mul hdD hvN
  have hdm : d * (n * d) ≤ P := by simpa [P] using Nat.mul_le_mul hdD hmN
  have hdPQ : d * P ≤ Q := by simpa [Q] using Nat.mul_le_mul_right P hdP
  have hNQ : N ^ 2 ≤ Q := by simpa [pow_two, Q] using Nat.mul_le_mul hNP hNP
  have hS : S ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [S]
    nlinarith only [hvP, hdP, hdv, hconst, hP]
  have hV : V ≤ 4 * P := by
    dsimp [V]
    nlinarith only [hdm, hmP, hdP]
  have hR : R ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [R]
    nlinarith only [hnP, hV, hconst, hP]
  have hC : C ≤ 50000 * P := by
    have hconst := Nat.mul_le_mul_left 8224 hP
    dsimp [C]
    nlinarith only [hnP, hmP, hV, hR, hconst, hP]
  have hSQ : S ≤ 10000 * Q := hS.trans (Nat.mul_le_mul_left 10000 hPQ)
  have hCQ : C ≤ 50000 * Q := hC.trans (Nat.mul_le_mul_left 50000 hPQ)
  have hdSQ : d * S ≤ 10000 * Q := by
    calc
      d * S ≤ d * (10000 * P) := Nat.mul_le_mul_left d hS
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hdRQ : d * R ≤ 10000 * Q := by
    calc
      d * R ≤ d * (10000 * P) := Nat.mul_le_mul_left d hR
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hOut : output.length ≤ 20000 * Q := by
    change output.length ≤ 20000 * N ^ 2 at ho
    exact ho.trans (Nat.mul_le_mul_left 20000 hNQ)
  have hDummyLength : dummy.length ≤ 10000 * Q := by
    have h := dummyRows_length_le v (2 * d * v) d
    change dummy.length ≤ d * S at h
    exact h.trans hdSQ
  have hAfter : after.length ≤ 30000 * Q := by
    dsimp [after]
    rw [List.length_append]
    omega
  have hDummyInside : 4 * S + 2 * (output.length + d * S) + 10 ≤ 100010 * Q := by
    have hconst := Nat.mul_le_mul_left 10 hQ
    nlinarith only [hSQ, hOut, hdSQ, hconst]
  have hDummySteps : MachineDummyRows.steps v (2 * d * v) output d ≤ 100010 * d * Q := by
    calc
      MachineDummyRows.steps v (2 * d * v) output d ≤
          d * (4 * S + 2 * (output.length + d * S) + 10) := by
        simpa only [S] using MachineDummyRows.steps_le_bound v (2 * d * v) output d
      _ ≤ d * (100010 * Q) := Nat.mul_le_mul_left d hDummyInside
      _ = 100010 * d * Q := by ring
  have hOldInside : C + 2 * (after.length + d * R) + 1 ≤ 130001 * Q := by
    nlinarith only [hCQ, hAfter, hdRQ, hQ]
  have hOldSteps : MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      130001 * d * Q + 1 := by
    have h := MachineLazyRows.vertexSteps_le d (2 * d) d (List.ofFn rows) after
    simp only [List.length_ofFn] at h
    change MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      d * (C + 2 * (after.length + d * R) + 1) + 1 at h
    calc
      MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
          d * (C + 2 * (after.length + d * R) + 1) + 1 := h
      _ ≤ d * (130001 * Q) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left d hOldInside) 1
      _ = 130001 * d * Q + 1 := by ring
  have hvQ : v ≤ Q := hvP.trans hPQ
  have hOverhead : 3 * v + 8201 ≤ 10000 * Q := by
    have hconst := Nat.mul_le_mul_left 8201 hQ
    nlinarith only [hvQ, hconst, hQ]
  have hBody : bodySteps d v rows output ≤ 230011 * d * Q + 10000 * Q + 1 := by
    change 2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) +
      (v + 2) + 8193 + MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after + 1 ≤ _
    nlinarith only [hDummySteps, hOldSteps, hOverhead]
  have hdQQ : d * Q ≤ D * Q := Nat.mul_le_mul_right Q hdD
  have hQQ : Q ≤ D * Q := by simpa using Nat.mul_le_mul_right Q hD
  have hDQ : 1 ≤ D * Q := hQ.trans hQQ
  have hCoarse : bodySteps d v rows output ≤ 300000 * D * Q := by
    nlinarith only [hBody, hdQQ, hQQ, hDQ]
  calc
    bodySteps d v rows output ≤ 300000 * D * Q := hCoarse
    _ ≤ 1000000 * D * Q := by
      have h := Nat.mul_le_mul_right (D * Q) (by norm_num : (300000 : Nat) ≤ 1000000)
      simpa only [Nat.mul_assoc] using h
    _ = 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by dsimp [D, N, P, Q]; ring

theorem loopSteps_le {n d : Nat} (table : PortTables.Table n d) (L count r : Nat)
    (hsum : r + count = n) (hn : n ≤ L) (hm : n * d ≤ L) (output : List Bool)
    (hout : (output ++ outputBlocks table (remaining n r)).length ≤ 20000 * (L + 1) ^ 2) :
    loopSteps table r count output ≤
      count * (1 + 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2) + 5 * L + 11 := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    have hdouble : 2 * d * n = 2 * (n * d) := by ac_rfl
    simp only [loopSteps, finishSteps, Nat.zero_mul, Nat.zero_add, hdouble]
    omega
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    have ho : output.length ≤ 20000 * (L + 1) ^ 2 := by
      rw [List.length_append] at hout
      omega
    have hb := bodySteps_le rows r L output hr.le hn hm ho
    have hs : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    have hout' : ((output ++ vertexBlock d r rows) ++
        outputBlocks table (remaining n (r + 1))).length ≤ 20000 * (L + 1) ^ 2 := by
      simpa only [hs, List.append_assoc] using hout
    have ht := ih (r + 1) (by omega) (output ++ vertexBlock d r rows) hout'
    simp only [loopSteps, dite_eq_left hr]
    change (1 + bodySteps d r rows output) +
      loopSteps table (r + 1) count (output ++ vertexBlock d r rows) ≤ _
    nlinarith only [hb, ht]

theorem totalSteps_le {n d : Nat} (table : PortTables.Table n d) :
    totalSteps table ≤ (timePolynomial d).eval (PortTables.tableBits table).length := by
  let L := (PortTables.tableBits table).length
  let N := L + 1
  let C := 1000000 * (d + 1) ^ 3
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have hout : (encodeWords [n, 2 * (n * d)] ++
      outputBlocks table (remaining n 0)).length ≤ 20000 * (L + 1) ^ 2 := by
    rw [remaining_zero, ← output_table_codec]
    exact output_length_le table
  have hl := loopSteps_le table L n 0 (by omega) hn hm _ hout
  have hp : prefixSteps n (n * d) (inputBlocks table (List.finRange n)) ≤ 10 * L + 17 := by
    unfold prefixSteps
    rw [← input_table_codec table]
    change 2 * L + 5 * n + 3 * (n * d) + 17 ≤ _
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnN : n ≤ N := by dsimp [N]; omega
  have hN2 : 1 ≤ N ^ 2 := by nlinarith only [hN]
  have hN3 : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N hN2
    nlinarith only [h]
  have hc := Nat.mul_le_mul_right (1 + C * N ^ 2) hnN
  change loopSteps table 0 n (encodeWords [n, 2 * (n * d)]) ≤ n * (1 + C * N ^ 2) + 5 * L + 11 at hl
  rw [timePolynomial_eval]
  change totalSteps table ≤ (C + 100) * N ^ 3
  unfold totalSteps
  have hLN : L + 1 = N := rfl
  nlinarith only [hp, hl, hc, hN, hN3, hLN]

def machineInTime {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    StateTransition.EvalsToInTime (machine d positive).step
      (initList (machine d positive) (PortTables.tableBits table))
      (some ⟨none, clean d positive, finalTapes (PortTables.tableBits table)
        (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩)
      ((timePolynomial d).eval (PortTables.tableBits table).length) where
  steps := totalSteps table
  evals_in_steps := by
    rw [initial_configuration]
    exact tableTrace table positive
  steps_le_m := totalSteps_le table

end BinPackingGames.Foundations.Complexity.MachineLazyTable

namespace BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineOverlayRows
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineOverlayRows

open Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

theorem rowTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : Label e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = instruction d e positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (suffix : List Bool)
    (tailWord : base (tape 0) = encodeWord v)
    (inputWord : base (tape 9) = encodeWord j ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[rowSteps d e v j (base (tape 7))]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        resultTapes d e v j tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have h₁ := empty 1 (by decide) (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide) (by decide)
  have hi0 : bodyIndex 0 = 0 := rfl
  have hi3 : bodyIndex 3 = 3 := rfl
  have hi4 : bodyIndex 4 = 4 := rfl
  have hi5 : bodyIndex 5 = 5 := rfl
  have hi6 : bodyIndex 6 = 6 := rfl
  have hi8 : bodyIndex 8 = 8 := rfl
  let loaded := Function.update (Function.update base (tape 9) suffix) (tape 1) (encodeWord j)
  let seeded := Function.update loaded (tape 2) trueBits
  let rowed := MachineLazyRows.reindexResultTapes e (d + e) d v j trueRelation
    (tape ∘ bodyIndex) seeded
  let oldCleared := Function.update rowed (tape 1) []
  let newCleared := Function.update oldCleared (tape 6) []
  have loadRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .loadStart) (labels .loadLoop) (some (labels .seedRelation)) program
      (atLabels .loadStart) (atLabels .loadLoop) base j suffix inputWord
      (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
    change (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient,
        Hastad.SourceMachine.fieldTapes (tape 9) (tape 1) base suffix
          (encodeWord j ++ base (tape 1))⟩ at h
    simpa only [Hastad.SourceMachine.fieldTapes,
      h₁, List.append_nil, MachinePortReindex.clean, loaded] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))),
        MachinePortReindex.clean e positive ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .seedRelation)) _ _) = _
    rw [atLabels]
    simp [instruction, stepAux_pushWord, TM2.stepAux, seeded, loaded,
      hd 2 1 (by decide), hd 2 9 (by decide), h₂]
  have hs (i : Fin 10) (hi : i ≠ 1) (hi' : i ≠ 2) (hi'' : i ≠ 9) :
      seeded (tape i) = base (tape i) := by
    simp [seeded, loaded, hd i 1 hi, hd i 2 hi', hd i 9 hi'']
  have bodyRun := MachineLazyRows.reindexRowTrace e positive (d + e) d
    (tape ∘ bodyIndex) (distinct.comp bodyIndex_injective) (fun s => labels (.row s))
    (some (labels .drainOld)) program (fun s => atLabels (.row s)) seeded v j trueRelation
    (by simpa only [Function.comp_apply, hi0] using
      (hs 0 (by decide) (by decide) (by decide)).trans tailWord)
    (by simp [seeded, loaded, Function.comp_apply, bodyIndex, hd 1 2 (by decide)])
    (by simp [seeded, Function.comp_apply, bodyIndex, trueBits])
    (by simpa only [Function.comp_apply, hi3] using
      (hs 3 (by decide) (by decide) (by decide)).trans h₃)
    (by simpa only [Function.comp_apply, hi4] using
      (hs 4 (by decide) (by decide) (by decide)).trans h₄)
    (by simpa only [Function.comp_apply, hi5] using
      (hs 5 (by decide) (by decide) (by decide)).trans h₅)
    (by simpa only [Function.comp_apply, hi6] using
      (hs 6 (by decide) (by decide) (by decide)).trans h₆)
    (by simpa only [Function.comp_apply, hi8] using
      (hs 8 (by decide) (by decide) (by decide)).trans h₈) ambient
  have hout : seeded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[MachineLazyRows.reindexSteps e (d + e) d v j
      trueRelation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), MachinePortReindex.clean e positive ambient, seeded⟩) =
    some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩ at bodyRun
  have rowedOld : rowed (tape 1) = encodeWord j := by
    simp [rowed, MachineLazyRows.reindexResultTapes, MachineLazyRows.reindexMappedTapes,
      Function.comp_apply, bodyIndex, seeded, loaded, hd 1 7 (by decide),
      hd 1 6 (by decide), hd 1 2 (by decide)]
  have rowedNew : oldCleared (tape 6) = encodeWord (MachinePortReindex.value e (d + e) d j) := by
    simp [oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
      hd 6 1 (by decide), hd 6 7 (by decide)]
  have rowedRelation : newCleared (tape 2) = trueBits := by
    simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex, seeded,
      hd 2 6 (by decide), hd 2 1 (by decide), hd 2 7 (by decide)]
  have drainOld := (MachineDrain.drainInTime (tape 1) (labels .drainOld)
    (some (labels .drainNew)) program (atLabels .drainOld) rowed
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 1)).length + 1]
    (some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩) =
    some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩ at drainOld
  rw [rowedOld, encodeWord_length] at drainOld
  have drainNew := (MachineDrain.drainInTime (tape 6) (labels .drainNew)
    (some (labels .drainRelation)) program (atLabels .drainNew) oldCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 6)).length + 1]
    (some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩) =
    some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩ at drainNew
  rw [rowedNew, encodeWord_length] at drainNew
  have drainRelation := (MachineDrain.drainInTime (tape 2) (labels .drainRelation)
    exit program (atLabels .drainRelation) newCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(newCleared (tape 2)).length + 1]
    (some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩) =
    some ⟨exit, MachinePortReindex.clean e positive ambient,
      Function.update newCleared (tape 2) []⟩ at drainRelation
  rw [rowedRelation] at drainRelation
  have finalFrame : Function.update newCleared (tape 2) [] = resultTapes d e v j tape base suffix := by
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [resultTapes, hd 2 7 (by decide), hd 2 9 (by decide), h₂]
    · by_cases h6 : k = tape 6
      · subst k
        simp [newCleared, resultTapes, hd 6 2 (by decide), hd 6 7 (by decide),
          hd 6 9 (by decide), h₆]
      · by_cases h1 : k = tape 1
        · subst k
          simp [newCleared, oldCleared, resultTapes, hd 1 2 (by decide),
            hd 1 6 (by decide), hd 1 7 (by decide), hd 1 9 (by decide), h₁]
        · by_cases h7 : k = tape 7
          · subst k
            simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              resultTapes, rowBits, seeded, loaded, hd 7 2 (by decide),
              hd 7 6 (by decide), hd 7 1 (by decide), hd 7 9 (by decide)]
          · simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              seeded, loaded, resultTapes, h2, h6, h1, h7]
  rw [finalFrame] at drainRelation
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace loadRun seedRun) bodyRun)
    drainOld) drainNew) drainRelation

theorem vertexSuffixTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (remaining : Nat) (i : Fin (e + 1)) (count : i.val + remaining = e)
    (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v ((List.ofFn values).drop i.val) output]
      (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base ((List.ofFn values).drop i.val) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v ((List.ofFn values).drop i.val))⟩ := by
  have hd (a b : Fin 10) (h : a ≠ b) : tape a ≠ tape b := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = e := by omega
      have hdrop : (List.ofFn values).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, streamOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < e := by omega
      let port : Fin e := ⟨i.val, hi⟩
      let next : Fin (e + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn values).drop (i.val + 1)
      have split : (List.ofFn values).drop i.val = values port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn values)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (values port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient, initial⟩) =
          some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := rowTrace d e positive tape distinct (fun stage => labels (i, some stage))
        (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using
            (atLabels (i, some stage))) initial v (values port)
        (encodeWords rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 0 7 (by decide), hd 0 9 (by decide), tailWord])
        (by simp [initial, streamFrame, hd 9 7 (by decide), encodeWords, List.append_assoc])
        (by
          intro k hk0 hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk0 hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[rowSteps d e v (values port) output]
        (some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9))⟩ at body
      rw [show resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9)) =
        streamFrame tape base rest (output ++ rowBits d e v (values port)) from
          streamFrame_afterRow d e v (values port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = e := by dsimp [next]; omega
      have tail := ih next nextCount (output ++ rowBits d e v (values port))
      change (advance (TM2.step program))^[vertexSteps d e v rest (output ++ rowBits d e v (values port))]
        (some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          streamFrame tape base rest (output ++ rowBits d e v (values port))⟩) =
        some ⟨exit, MachinePortReindex.clean e positive ambient,
          streamFrame tape base [] ((output ++ rowBits d e v (values port)) ++ streamOutput d e v rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, streamOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v (List.ofFn values) output]
      (some ⟨some (labels (0, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base (List.ofFn values) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v (List.ofFn values))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d e positive tape distinct
    labels exit program atLabels base v values tailWord empty ambient e 0 (by simp) output

end BinPackingGames.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineOverlayTable
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type}

theorem oldVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (v : Fin n) (g h gs hs nv mv f current out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) hs nv mv f current [] out⟩) =
      some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f current [] (out ++ oldOutput G e v)⟩ := by
  have hrun := MachineLazyRows.vertexTrace d hd (d + e) 0 oldTapes oldTapes_injective
    (fun stage => .inr (.old stage)) (next .tailSeed) (program d e hd he) (fun _ => rfl)
    (memory g h gs hs nv mv f current [] []) (row G v)
    (by
      intro i hi7 hi9
      fin_cases i <;> simp_all [oldTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, graphStream])
    (a, MachineFixedDivMod.residue e he 0) out
  simpa only [next, oldFrame, MachineLazyRows.recordsInput, List.flatMap_nil, List.nil_append,
    clean, oldBlock, oldRows, oldOutput] using hrun

theorem expanderVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (H : ExpanderTables.Table n e) (v : Fin n) (g h gs hs nv mv f current out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineOverlayRows.vertexSteps d e v.val
      (List.ofFn (expanderValues H v)) out]
      (some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs (expanderBlock H v ++ hs) nv mv f current (encodeWord v.val) out⟩) =
      some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f current (encodeWord v.val) (out ++ expanderOutput d H v)⟩ := by
  let source := MachineStateEquiv.program (expanderState A d e).symm (program d e hd he)
  have code (stage : MachineOverlayRows.VertexLabel e) : source (.inr (.expander stage)) =
      MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage := by
    change MachineStateEquiv.statement (expanderState A d e).symm
      (MachineStateEquiv.statement (expanderState A d e) _) = _
    exact MachineStateEquiv.statement_symm_statement _ _
  have native := MachineOverlayRows.vertexTrace d e he expanderTapes expanderTapes_injective
    (fun stage => .inr (.expander stage)) (next .drainTail) source code
    (memory g h gs hs nv mv f current (encodeWord v.val) []) v.val (expanderValues H v)
    rfl
    (by
      intro i hi0 hi7 hi9
      fin_cases i <;> simp_all [expanderTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream])
    ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0) out
  have transported := MachineStateEquiv.trace (expanderState A d e) source _ _ _ native
  have back : MachineStateEquiv.program (expanderState A d e) source = program d e hd he :=
    MachineStateEquiv.program_symm_program (expanderState A d e).symm _
  rw [back] at transported
  simpa only [next, MachineStateEquiv.configuration, expanderState_clean, expanderFrame,
    encodeWords, List.nil_append, expanderBlock, expanderOutput] using transported

theorem pairTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n)
    (g h gs hs nv mv f out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[pairSteps G H v out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) (expanderBlock H v ++ hs)
          nv mv f (encodeWord v.val) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (v.val + 1)) [] (out ++ outputBlock G H v)⟩ := by
  have h₁ := oldVertexTrace d e hd he G v g h gs (expanderBlock H v ++ hs)
    nv mv f (encodeWord v.val) out a
  have h₂ := tailCopyTrace d e hd he g h gs (expanderBlock H v ++ hs)
    nv mv f (out ++ oldOutput G e v) v.val a
  have h₃ := expanderVertexTrace d e hd he H v g h gs hs nv mv f
    (encodeWord v.val) (out ++ oldOutput G e v) a
  have h₄ := tailFinishTrace d e hd he g h gs hs nv mv f
    ((out ++ oldOutput G e v) ++ expanderOutput d H v) v.val a
  simpa only [pairSteps, outputBlock, List.append_assoc] using
    joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

theorem loopBodyTraces {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    MachineCountedLoop.BodyTraces fuel (.inr .guard) (.inr (.old (0, none)))
      (program d e hd he) [] (fun _ => (clean d e hd he a).1) (fun _ => none)
      (loopBase G H) (loopCost G H) n := by
  intro r hr
  let v : Fin n := ⟨n - (r + 1), by omega⟩
  have hv : v.val + 1 = n - r := by dsimp [v]; omega
  have hinput : MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (oldBlock G v ++ remaining (oldBlock G) (v.val + 1))
        (expanderBlock H v ++ remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord v.val) []
        (outputPrefix G H v.val) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    change memory _ _ (remaining (oldBlock G) v.val) (remaining (expanderBlock H) v.val)
      _ _ _ _ _ _ = _
    rw [remaining_step (oldBlock G) v, remaining_step (expanderBlock H) v]
  have houtput : MachineUnaryCounter.counterTapes fuel (loopBase G H r) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord (v.val + 1)) []
        (outputPrefix G H v.val ++ outputBlock G H v) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    rw [← hv, outputPrefix_step]
  have run := pairTrace d e hd he G H v (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
    (encodeWord n) (encodeWord (n * d)) (encodeWord r) (outputPrefix G H v.val) a
  change (advance (TM2.step (program d e hd he)))^[loopCost G H r]
    (some ⟨next (.old (0, none)), clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r []⟩) =
    some ⟨next .guard, clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H r) r []⟩
  rw [hinput, houtput]
  simpa only [loopCost, dite_eq_left hr, v] using run

theorem loopTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineCountedLoop.totalSteps (loopCost G H) n]
      (some ⟨next .guard, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H)
          (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
          (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩) =
      some ⟨next .drainFuel, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] []
          (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have run := MachineCountedLoop.loopTrace fuel (.inr .guard) (.inr (.old (0, none)))
    (.inr .drainFuel) (program d e hd he) rfl []
    (fun _ => (clean d e hd he a).1) (fun _ => none) (loopBase G H) (loopCost G H) n
    (loopBodyTraces d e hd he G H a)
  have startFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H n) n [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
        (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
        (encodeWords [n, n * (d + e)]) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_self, remaining_zero, outputPrefix, prefix_zero]
    simp only [graphRows_blocks, rawExpander, expanderRows_blocks]
  have endFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H 0) 0 [] =
      memory (PortTables.tableBits G) (rawExpander H) [] []
        (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
        (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_zero, remaining_end, outputPrefix, prefix_end, tableBits_blocks]
  simp only [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration] at run
  rw [startFrame, endFrame] at run
  simpa only [next, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using run

theorem tableTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    (advance (TM2.step (program d e hd he)))^[tableSteps G H]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
      some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have h₁ := splitTrace d e hd he (PortTables.graphTable G) (rawExpander H) a
  rw [splitTapes_memory] at h₁
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  change (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps n (n * d)
      (MachineTableSplit.rowsBits (PortTables.graphTable G))]
    (some ⟨some (.inl .copyFirst), clean d e hd he a,
      initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
    some ⟨next .copyHFirst, clean d e hd he a,
      memory (encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G))
        (rawExpander H) (MachineTableSplit.rowsBits (PortTables.graphTable G)) []
        (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ at h₁
  rw [header] at h₁
  have h₂ := preparationTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (MachineTableSplit.rowsBits (PortTables.graphTable G)) n (n * d) a
  have h₃ := loopTrace d e hd he G H a
  have h₄ := cleanupTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) n (n * d) a
  exact joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

def tableInTime {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    StateTransition.EvalsToInTime (TM2.step (program d e hd he))
      ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩
      (some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩)
      ((timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length)) where
  steps := tableSteps G H
  evals_in_steps := tableTrace d e hd he G H a
  steps_le_m := tableSteps_le G H

end BinPackingGames.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachinePaddedOverlayRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

noncomputable def paddingInTime (H : BaseTable) {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨some familyEntry, clean H d hd, paddedTapes t⟩)
      ((MachineVertexPadding.timePolynomial d).eval (PortTables.tableBits t).length) := by
  let ambient := (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ())
  have run := placeExecution paddingTape paddingView paddingView_left paddingView_right
    paddingLabel (some familyEntry) (fun _ => []) (MachineVertexPadding.program d hd) (program H d hd)
    (fun _ => rfl) (MachineVertexPadding.vertexPaddingInTime hd t ambient none)
  simpa only [Placement.configuration, Placement.label, padding_initial_memory,
    padding_final_memory, initialTapes, paddedTapes, padded, main, clean, ambient] using run

noncomputable def familyInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some familyEntry, clean H d hd, paddedTapes t⟩
      (some ⟨some overlayEntry, clean H d hd, familyTapes H t⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  let o := MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()
  have caller : MachineExpanderFamily.caller f = () := Subsingleton.elim _ _
  have castRun := MachineAlphabetTransport.successfulExecutionInTime
    MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)
    (MachineExpanderFamily.paddedFamilyInTime H n f [])
  have boolRun : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [MachineExpanderFamily.boolView, MachineExpanderFamily.configuration_toBool,
      caller] using castRun
  have framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) ((o, false), (none : Option Bool)) boolRun
  have transported := MachineStateEquiv.execution (familyStates d)
    (MachineStateFrame.frameProgram
      (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (familySource H d))
      ⟨some (.inr .initialize_), clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [familySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, familyStates,
      Equiv.coe_fn_mk, clean, f, o]
      using transported
  have run := placeExecution familyTape familyView familyView_left familyView_right
    familyLabel (some overlayEntry) (paddedTapes t) (familySource H d) (program H d hd)
    (fun _ => rfl) sourceRun
  have finishRaw := family_final_memory H (PortTables.tableBits t)
    (PortTables.tableBits (padded t)) (PreprocessingLevels.boundedLevel n)
  have hsize : ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n) =
      PreprocessingLevels.paddedSize n := PreprocessingLevels.table_vertexCount_eq_paddedSize n
  have count : memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n)
      (encodeWord (ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n))) [] =
      familyTapes H t :=
    congrArg (fun size => memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n) (encodeWord size) []) hsize
  have finish := finishRaw.trans count
  simpa only [Placement.configuration, Placement.label, paddedTapes,
    family_initial_memory, finish, familyEntry] using run

noncomputable def overlayInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some overlayEntry, clean H d hd, familyTapes H t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  have original := MachineOverlayTable.tableInTime d overlayDegree hd overlayDegree_positive
    (padded t) (PreprocessingStageMaps.familyAt H n) ()
  have framed := MachineStateFrame.frameExecution
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)
    ((f, false), (none : Option Bool))
    original
  have transported := MachineStateEquiv.execution (overlayStates d)
    (MachineStateFrame.frameProgram
      (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (overlaySource d hd))
      ⟨some (.inl .copyFirst), clean H d hd,
        MachineOverlayTable.initialTapes (PortTables.tableBits (padded t)) (rotor H n)⟩
      (some ⟨none, clean H d hd,
        MachineOverlayTable.memory (PortTables.tableBits (padded t)) (rotor H n)
          [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
    simpa only [overlaySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, overlayStates, Equiv.coe_fn_mk, clean, f,
      rotor_familyAt, PreprocessingStageMaps.paddedOverlay, PreprocessingStageMaps.padding,
      padded] using transported
  have run := placeExecution overlayTape overlayView overlayView_left overlayView_right
    overlayLabel none (familyTapes H t) (overlaySource d hd) (program H d hd)
    (fun _ => rfl) sourceRun
  simpa only [Placement.configuration, Placement.label, familyTapes, finalTapes,
    MachineOverlayTable.initialTapes_memory, overlay_memory, overlayEntry] using run

noncomputable def execution (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) := by
  let first := paddingInTime H hd t
  let second := familyInTime H hd t
  let third := overlayInTime H hd t
  let firstTwo := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ firstTwo third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := all.steps_le_m.trans ?_ }
  have hn := PortTables.vertices_le_tableBits_length t
  have hf := Nat.mul_le_mul_left MachineExpanderFamilyBounds.inputCoefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 5)
  have ho := natPolynomial_eval_mono (MachineOverlayTable.timePolynomial d overlayDegree)
    (archive_length_le H t)
  have h := Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl ((MachineVertexPadding.timePolynomial d).eval
      (PortTables.tableBits t).length)) hf) ho
  simpa only [timePolynomial, familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end BinPackingGames.Foundations.Complexity.MachinePaddedOverlay

namespace BinPackingGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

noncomputable def terminalRun (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram H d hd) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d a))
      ((MachinePaddedOverlay.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachinePaddedOverlay.clean H d hd
  tapes := MachinePaddedOverlay.finalTapes H a.2
  execution := by
    rw [initial_configuration]
    exact MachinePaddedOverlay.execution H hd a.2
  output_eq := MachinePaddedOverlay.final_output H hd a.2

noncomputable def computableInPolyTime (H : BaseTable) (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := d + MachinePaddedOverlay.overlayDegree))
      (PreprocessingStageMaps.paddedOverlay H d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end BinPackingGames.Foundations.Complexity.MachinePaddedOverlayRuntime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularInternalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem rotorSteps_le {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    rotorSteps table i p ≤ 2 * i.val +
      5 * (encodeWords (ExpanderTableWords.rotationWords table)).length + n * q + 8 := by
  have hl := MachineAffineLookup.steps_le (ExpanderTableWords.rotationWords table)
    i.val q p.val _ (selected_rotation table i p)
  have hb := (ExpanderTables.rowIndex n q (ExpanderTables.lookup table (i, p))).isLt
  rw [ExpanderTables.rowIndex_val] at hb
  unfold rotorSteps
  omega

theorem selectionSteps_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    selectionSteps t padding v i ≤
      10 * (GraphTables.tableBits t).length + 16 * i.val + 13 * v.val +
      5 * PreprocessingCloudIndex.cloudSize t v +
      2 * PreprocessingPaddingOffsets.offset padding v.val + 2 * t.darts + 57 := by
  unfold selectionSteps
  split
  · rename_i hi
    have hb := MachineCloudSelect.cloudSelectSteps_le t v ⟨i.val, hi⟩ []
    have hmin : min i.val (PreprocessingCloudIndex.cloudSize t v) = i.val := Nat.min_eq_left hi.le
    simp only [oldSelectSteps, MachineUnaryLessAt.steps, hmin]
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord,
      List.length_append, encodeWord_length, List.length_nil] at hb
    omega
  · rename_i hi
    rw [dummySelectSteps_eq _ _ _ _ (Nat.le_of_not_gt hi)]
    have hmin := Nat.min_le_right i.val (PreprocessingCloudIndex.cloudSize t v)
    unfold MachineUnaryLessAt.steps
    omega

theorem coreSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) :
    coreSteps t padding tables v x p outputLength ≤
      coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
        (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
        (PreprocessingCloudIndex.cloudSize t v)
        (PreprocessingPaddingOffsets.offset padding v.val) t.darts outputLength := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let L := (GraphTables.tableBits t).length
  let R := (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
  let k := PreprocessingCloudIndex.cloudSize t v
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  have hN : k + padding v ≤ R := rotorSize_le_encodedLength positive (tables v)
  have hj : step.1.val ≤ R := step.1.isLt.le.trans hN
  have hr : step.2.val ≤ q := step.2.isLt.le
  have hz : z ≤ t.darts + o + R := by
    have h := selectedIndex_le t padding v step.1
    change z ≤ t.darts + o + step.1.val at h
    omega
  have hsize : (k + padding v) * q ≤ R := by
    dsimp only [R, k]
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  have hrotor : rotorSteps (tables v) rank p ≤ 2 * rank.val + 6 * R + 8 := by
    have h := rotorSteps_le (tables v) rank p
    change rotorSteps (tables v) rank p ≤ 2 * rank.val + 5 * R + (k + padding v) * q + 8 at h
    omega
  have hselect : selectionSteps t padding v step.1 ≤
      10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 := by
    have h := selectionSteps_le t padding v step.1
    change selectionSteps t padding v step.1 ≤
      10 * L + 16 * step.1.val + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 at h
    omega
  have hfinish : finishSteps q X z step.2.val outputLength ≤
      (5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986 := by
    have h := finishSteps_le q X z step.2.val outputLength
    have hm := Nat.mul_le_mul_left (5 * q + 7) hz
    omega
  have htail : tailBits.length ≤ R := encodedDrop_length_le
    (ExpanderTableWords.rotationWords (tables v)) (q * rank.val + p.val + 1)
  have hcleanup : tailBits.length + step.1.val + step.2.val + z + 15 ≤
      R + R + q + (t.darts + o + R) + 15 := by omega
  calc
    coreSteps t padding tables v x p outputLength
        ≤ (2 * rank.val + 6 * R + 8) +
          (10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57) +
          ((5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986) +
          (R + R + q + (t.darts + o + R) + 15) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrotor hselect) hfinish) hcleanup
    _ = _ := by
      change _ = coreTimeBound q L R X v.val rank.val k o t.darts outputLength
      unfold coreTimeBound
      ring

end BinPackingGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingRegularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

theorem rowsBits_ofCloudTables :
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) =
      (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  rw [PreprocessingPaddingWords.rowsBits_eq_vertices]
  have hblocks :
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables) i) =
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        vertexBits t padding tables ((vertexOrder t padding).symm i)) := by
    apply congrArg List.ofFn
    funext i
    rw [vertexBits_eq, Equiv.apply_symm_apply]
  rw [hblocks, vertexOrder_ofFn, List.flatten_append]
  change (List.ofFn (originalVertexBits t padding tables)).flatten ++
      ((paddingList padding).map (fun z => dummyVertexBits t padding tables z.1 z.2)).flatten = _
  rw [← List.flatMap_def, paddingList_flatMap]

theorem tableBits_ofCloudTables :
    PortTables.tableBits (ofCloudTables t padding tables) =
      encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
        (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  change encodeWords (PortTables.tableWords (ofCloudTables t padding tables)) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  change encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) = _
  rw [rowsBits_ofCloudTables, List.append_assoc]

end BinPackingGames.Foundations.PCP.PreprocessingRegularWords

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open BinPackingGames.Foundations.Complexity
open scoped BigOperators

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

end BinPackingGames.Foundations.PCP.PreprocessingRegularBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularExecutionBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

variable {σ : Type}

theorem prefixTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hoffset : data.offset = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixSteps t v]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some (cfg (some (.cloud .init)) (prefixData t v data) ambient none) := by
  have raw := MachineCloudPrefix.prefixTrace t v.val v.isLt.le [] ambient register
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes prefixView
    (MachineCloudPrefix.frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
      (encodeWord v.val) (encodeWord 0)
      (encodeWord (PreprocessingPaddingOffsets.offset
        (PreprocessingRegularTables.padding t) v.val))) (frame data)
  have placed := MachineCloudPadding.Placement.trace prefixTape prefixView prefixView_left
    prefixView_right Label.prefixCode (some .prefixClearQuery) (frame data)
    MachineCloudPrefix.program program (fun _ => rfl)
    (MachineCloudPrefix.totalTime t v.val []) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes prefixView
      (MachineCloudPrefix.frame (GraphTables.tableBits t) [] [] [] [] (encodeWord v.val) [] [])
      (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, hoffset, MachineCloudPadding.Placement.tapes, prefixView, frame,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  have phase : (advance (TM2.step program))^[MachineCloudPrefix.totalTime t v.val []]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some ⟨some .prefixClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label, hstart, cfg, mid] using placed
  have first := drainAt (.inl 9) .prefixClearQuery (some .prefixClearFuel) rfl mid ambient none
  have second := drainAt (.inl 18) .prefixClearFuel (some (.cloud .init)) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = v.val + 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      MachineCloudPadding.memory, encodeWord_length]
  have hfuel : ((Function.update mid (.inl 9) []) (.inl 18)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      encodeWord_length]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 18) [] =
      frame (prefixData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, mid, MachineCloudPadding.Placement.tapes, prefixView, frame, prefixData,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hfuel, hfinish] at second
  exact join_trace (join_trace phase first) second

theorem ownerTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val) (howner : data.owner = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[ownerSteps t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg (some .copyXFirst) (ownerData t e data) ambient none) := by
  have distinct : Function.Injective ownerTapes := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ownerTapes]
  have outside : ∀ i, (.inl 1 : Tape) ≠ ownerTapes i := by
    intro i
    fin_cases i <;> decide
  let mid := MachineAffineLookup.finalTapes ownerTapes (frame data)
    (GraphTables.tableWords t) (4098 * e.val + 2) t.rows[e].tail.val
  have phase : (advance (TM2.step program))^[
      MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some ⟨some .ownerClearQuery, ((ambient, false), none), mid⟩ := by
    exact MachineAffineLookup.affineLookupTrace (.inl 1) ownerTapes distinct outside 4098 2
      Label.owner (some .ownerClearQuery) program (fun _ => rfl) (frame data)
      (GraphTables.tableWords t) htable rfl e.val []
      (by change data.globalIndex = encodeWord e.val ++ [];
          simpa only [List.append_nil] using hindex)
      t.rows[e].tail.val (selected_owner t e) (ambient, false) register
  have first := drainAt (.inl 9) .ownerClearQuery (some .ownerClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .ownerClearWork (some .copyXFirst) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = 2 := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, encodeWord_length]
  have hwork : (Function.update mid (.inl 9) []) (.inl 10) = ownerRemainder t e := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, ownerRemainder]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 10) [] =
      frame (ownerData t e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [howner, mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
          MachineLookup.tapes, ownerTapes, frame, ownerData]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork, hfinish] at second
  exact join_trace (join_trace phase first) second

theorem queryTrace (data : Data) (v x : Nat)
    (howner : data.owner = encodeWord v) (hindex : data.globalIndex = encodeWord x)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[querySteps v x]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
  let first := Function.update (frame data) (.inl 9) data.globalIndex
  let second := Function.update first (.inl 9) (data.owner ++ data.globalIndex)
  have copyX := MachineCopy.copyTrace (.inl 1 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyXFirst Label.copyXSecond
    (some .copyOwnerFirst) program rfl rfl (frame data) rfl (ambient, false) register
  have copyOwner := MachineCopy.copyTrace (.inl 2 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyOwnerFirst Label.copyOwnerSecond
    (some .rankInit) program rfl rfl first (by simp [first, frame]) (ambient, false) none
  have firstRun : (advance (TM2.step program))^[2 * (x + 2)]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩ := by
    simpa only [frame_index, frame_query_empty, hindex, encodeWord_length,
      List.append_nil, cfg, first] using copyX
  have secondRun : (advance (TM2.step program))^[2 * (v + 2)]
      (some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩) =
      some ⟨some .rankInit, ((ambient, false), none), second⟩ := by
    simpa [first, frame, howner, encodeWord_length, second] using copyOwner
  have init : (advance (TM2.step program))^[1]
      (some ⟨some .rankInit, ((ambient, false), none), second⟩) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
    have ht : Function.update second (.inl 3) (false :: second (.inl 3)) =
        queryFrame data v x := by
      funext j
      cases j with
      | inl j => fin_cases j <;>
          simp_all [queryFrame, second, first, frame, rankQuery,
            MachineCloudRank.queryWord, encodeWord]
      | inr j => cases j <;> rfl
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux, ht]
  exact join_trace (join_trace firstRun secondRun) init

theorem rankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (howner : data.owner = encodeWord v.val) (hindex : data.globalIndex = encodeWord e.val.val)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rankSteps t v e]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some (cfg (some (.prefixCode .init)) (rankData t v e data) ambient none) := by
  have query := queryTrace data v.val e.val.val howner hindex hrank ambient register
  have raw := MachineCloudRank.cloudRankTrace t v e [] [] ambient none
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes rankView
    (MachineCloudCount.memory (GraphTables.tableBits t) (rankRemainder t v e)
      (rankQuery v.val e.val.val) []
      (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val) (encodeWord 0)) (frame data)
  have placed := MachineCloudPadding.Placement.trace rankTape rankView rankView_left
    rankView_right Label.rank (some .rankClearQuery) (frame data)
    MachineCloudRank.rankProgram program (fun _ => rfl)
    (MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [])
    _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes rankView
      (MachineCloudCount.memory (GraphTables.tableBits t) []
        (rankQuery v.val e.val.val) [] (encodeWord 0) []) (frame data) =
      queryFrame data v.val e.val.val := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, MachineCloudPadding.Placement.tapes, rankView, frame,
          queryFrame, MachineCloudCount.memory]
    | inr j => cases j <;> rfl
  simp only [rankQuery] at hstart
  have phase : (advance (TM2.step program))^[
      MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) []]
      (some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v.val e.val.val⟩) =
      some ⟨some .rankClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
      hstart, mid, rankQuery, rankRemainder] using placed
  have first := drainAt (.inl 9) .rankClearQuery (some .rankClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .rankClearWork (some .rankClearFuel) rfl
    (Function.update mid (.inl 9) []) ambient none
  have third := drainAt (.inl 12) .rankClearFuel (some (.prefixCode .init)) rfl
    (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) ambient none
  have hquery : mid (.inl 9) = rankQuery v.val e.val.val := rfl
  have hwork : Function.update mid (.inl 9) [] (.inl 10) = rankRemainder t v e := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory]
  have hfuel : ((Function.update (Function.update mid (.inl 9) []) (.inl 10) [])
      (.inl 12)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory,
      encodeWord_length]
  have hfinish : Function.update
      (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) (.inl 12) [] =
      frame (rankData t v e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, mid, MachineCloudPadding.Placement.tapes, rankView, frame, rankData,
          MachineCloudCount.memory]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork] at second
  rw [hfuel, hfinish] at third
  exact join_trace (join_trace (join_trace (join_trace query phase) first) second) third

theorem originalTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val)
    (howner : data.owner = []) (hrank : data.localRank = []) (hcount : data.count = [])
    (hoffset : data.offset = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg none (originalData t e data) ambient none) := by
  have own := ownerTrace t e data htable hindex howner ambient register
  have rank := rankTrace t t.rows[e].tail (originalMember t e) (ownerData t e data)
    htable rfl hindex hrank ambient none
  have pref := prefixTrace t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data))
    htable rfl hoffset ambient none
  have cloud := cloudTrace t t.rows[e].tail
    (prefixData t t.rows[e].tail
      (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))
    htable rfl hcount hpadding hlevel ambient none
  exact join_trace (join_trace (join_trace own rank) pref) cloud

end BinPackingGames.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem cleanup_frame (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupTapes (MachineRegularOriginalRow.finalTapes q t e base) =
      Function.update base 9
        (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)) := by
  funext k
  fin_cases k <;>
    simp [cleanupTapes, MachineRegularOriginalRow.finalTapes,
      MachineRegularOriginalRow.affined, MachineRegularOriginalRow.copied,
      MachineRegularOriginalRow.looked, MachineAffineLookup.finalTapes,
      MachinePreservingLookup.finalTapes, MachineLookup.tapes,
      MachineRegularOriginalRow.lookupTape, input.queryEmpty, input.scanEmpty,
      input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.row (.lookup .seed))),
        ((ambient, MachineRegularOriginalRow.zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, MachineRegularOriginalRow.zeroBuffer), none),
        Function.update base 9
          (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ := by
  have row := MachineRegularOriginalRow.traceAt q (fun l => labels (.row l))
    (some (labels .query)) program (fun l => code (.row l)) t e base input.toInput ambient register
  have clean := cleanupTraceAt q labels exit program code
    (MachineRegularOriginalRow.finalTapes q t e base)
    ((ambient, MachineRegularOriginalRow.zeroBuffer), none)
  rw [cleanup_frame q t e base input] at clean
  exact join_trace row clean

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalClean

namespace BinPackingGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

theorem originalFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes originalView (originalMemory graph x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

theorem originalCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularOriginalClean.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = originalCoreInstruction q labels exit l)
    (t : GraphTables.Table) (e : Fin t.darts) (v i k o m : Nat)
    (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularOriginalClean.steps q t e
        (originalMemory (GraphTables.tableBits t) e.val output)]
      (some ⟨some (labels (.row (.lookup .seed))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor
          (output ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))
          [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedDivMod.residue q positive 0,
    (false, MachineCloudSelect.Phase.checking)))
  have run := MachineRegularOriginalClean.traceAt q id none
    (MachineRegularOriginalClean.instruction q id none) (fun _ => rfl) t e
    (originalMemory (GraphTables.tableBits t) e.val output)
    (originalMemory_input t e output) state none
  rw [originalMemory_update] at run
  have moved := MachineStateEquiv.trace (originalStateEquiv σ q)
    (MachineRegularOriginalClean.instruction q id none) _ _ _ run
  have placed := MachineCloudPadding.Placement.trace originalTapes originalView
    originalView_left originalView_right labels exit
    (coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] [])
    (MachineStateEquiv.program (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none)) program code _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, originalFrame] at placed
  convert placed using 1 <;> rfl

theorem originalRowSteps_eq (q : Nat) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalClean.steps q t e (originalMemory (GraphTables.tableBits t) e.val output) =
      originalRowSteps q t e output.length := by
  unfold originalRowSteps MachineRegularOriginalClean.steps
  rw [MachineRegularOriginalClean.cleanupSteps_eq q t e _ (originalMemory_input t e output),
    MachineRegularOriginalClean.cleanupSteps_eq q t e _
      (originalMemory_input t e (List.replicate output.length false))]
  simp only [MachineRegularOriginalRow.steps, MachineRegularOriginalRow.rowSteps,
    originalMemory, Matrix.cons_val, List.length_replicate]

theorem originalTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[originalSteps t padding tables e output.length]
      (some ⟨some (labels (originalEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables t.rows[e].tail (oldCloud t padding e)
          (output ++ PreprocessingRegularWords.originalVertexBits t padding tables e)⟩ := by
  let x := oldCloud t padding e
  let bits := (List.ofFn (rowBits t padding tables t.rows[e].tail x)).flatten
  have ports := portTrace q positive (fun l => labels (.originalPort l))
    (some (labels (.original (.row (.lookup .seed))))) program
    (fun l => code (.originalPort l)) t padding tables t.rows[e].tail x output ambient
  have inherited := originalCoreTrace q positive (fun l => labels (.original l)) exit program
    (fun l => code (.original l)) t e t.rows[e].tail.val
    (paddedCloudRank t padding t.rows[e].tail x).val (cloudSize t t.rows[e].tail)
    (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))) (output ++ bits) ambient
  rw [originalRowSteps_eq] at inherited
  change (advance (TM2.step program))^[originalRowSteps q t e (output ++ bits).length]
    (some ⟨some (labels (.original (.row (.lookup .seed)))), coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x (output ++ bits)⟩) =
    some ⟨exit, coreInitialState q positive ambient,
      coreInputTapes t padding tables t.rows[e].tail x
        ((output ++ bits) ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ at inherited
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e) := by
    have h := vertexBits_split t padding tables t.rows[e].tail x
    change PreprocessingRegularWords.originalVertexBits t padding tables e =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inl e) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_original_words] at h
    exact h
  rw [hbits]
  simpa only [originalSteps, portEntry, dite_eq_left positive, originalEntry,
    List.length_append, List.append_assoc, x, bits] using total

theorem portSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) (n : Nat) (hn : n ≤ q) :
    portSteps t padding tables v x outputLength n ≤
      n * coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
        (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
  induction n with
  | zero => simp only [portSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < q := by omega
    have first := ih (by omega)
    have second := coreSteps_le q positive t padding tables v x ⟨n, h⟩
      (outputLength + (portBits (rowBits t padding tables v x) n).length)
    have hlen := portBits_length_le (rowBits t padding tables v x)
      (rowSizeBound q (vertexCount t padding)) (rowBits_length_le t padding tables v x) n
    have hmul := Nat.mul_le_mul_right (rowSizeBound q (vertexCount t padding)) (Nat.le_of_lt h)
    have hcost : coreSteps t padding tables v x ⟨n, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) n).length) ≤
        coreTimeBound q (GraphTables.tableBits t).length
          (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
          (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
          (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
          (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
      unfold coreTimeBound at second ⊢
      omega
    rw [portSteps, dite_eq_left h, Nat.succ_mul]
    exact Nat.add_le_add first hcost

theorem originalSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) :
    originalSteps t padding tables e outputLength ≤
      originalTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))).length
        e.val t.rows[e].tail.val (paddedCloudRank t padding t.rows[e].tail (oldCloud t padding e)).val
        (cloudSize t t.rows[e].tail) (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val)
        t.darts outputLength (vertexCount t padding) := by
  let v := t.rows[e].tail
  let x := oldCloud t padding e
  let extra := (List.ofFn (rowBits t padding tables v x)).flatten.length
  have hp := portSteps_le q positive t padding tables v x outputLength q le_rfl
  have hi := MachineRegularOriginalClean.steps_le q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate (outputLength + extra) false))
    (originalMemory_input t e (List.replicate (outputLength + extra) false))
  have hl := allRowBits_length_le t padding tables v x
  change originalRowSteps q t e (outputLength + extra) ≤
    MachineRegularOriginalClean.timeBound q (GraphTables.tableBits t).length
      (List.replicate (outputLength + extra) false).length at hi
  rw [List.length_replicate] at hi
  change portSteps t padding tables v x outputLength q +
    originalRowSteps q t e (outputLength + extra) ≤ _
  unfold originalTimeBound portTimeBound MachineRegularOriginalClean.timeBound at *
  have hx : (vertexOrder t padding x.val).val = e.val := rfl
  rw [hx] at hp
  dsimp only [v, x, extra] at *
  omega

theorem dummySteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) :
    dummySteps t padding tables v j outputLength ≤
      dummyTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding (.inr ⟨v, j⟩)).val v.val
        (paddedCloudRank t padding v (paddedNew t padding v j)).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val)
        t.darts outputLength (vertexCount t padding) := by
  have hp := portSteps_le q positive t padding tables v (paddedNew t padding v j) outputLength q le_rfl
  have hl := allRowBits_length_le t padding tables v (paddedNew t padding v j)
  unfold dummySteps dummyTimeBound portTimeBound MachineRegularDummyRow.timeBound
  have hx : (paddedNew t padding v j).val = Sum.inr ⟨v, j⟩ := rfl
  rw [hx] at hp
  omega

end BinPackingGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

theorem vertexView_left (k : Fin 27) : vertexView (.inl k) = some k := rfl

theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularMetadata.totalTime t e]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H (some (.family .start)) (metadataData t e output)) := by
  have raw := MachineRegularMetadata.originalTrace t e (initialData t e output)
    rfl rfl rfl rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.family .start)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) (frame (initialData t e output))
    MachineRegularMetadata.program (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    metadataStates, Equiv.coe_fn_mk, entry] using placed

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t e output]
      (some (cfg H (some (.family .start)) (metadataData t e output))) =
      some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output)) := by
  have raw := (familyExecution H t e output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
    familyStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      ((((), false), none) : MetaState)) (frame (metadataData t e output))
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familyData, familySteps, cfg, readyState,
    familyStates, Equiv.prodComm_apply, Prod.swap_prod_mk] using placed

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length + 1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val + 1), readyState H, Function.update base (clearTape i) []⟩ := by
  have raw := MachineDrain.drainTrace (clearTape i) () none (clearSource (clearTape i)) rfl
    base (base (clearTape i)) ((), false) none
  simp only [Function.update_eq_self] at raw
  have placed := Lift.trace id some (fun _ => rfl)
    (fun j k h => (Option.some.inj h).symm)
    (fun _ : Unit => Label.clear i) (clearEntry (i.val + 1)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) base (clearSource (clearTape i)) (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    identityPlacement, metadataStates, Equiv.coe_fn_mk, readyState] using placed

theorem clearPrefixTrace (H : BaseTable) (base : Tape → List Bool)
    (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[clearSteps base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, clearMemory base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k, h⟩ (clearMemory base k)
    have atEntry : clearEntry k = some (.clear ⟨k, h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace first second

theorem clearTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[clearSteps base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, clearMemory base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using clearPrefixTrace H base 7 le_rfl

theorem coreFrame_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    coreFrame (familyData H t e output) =
      MachineRegularInternalRow.coreInputTapes t (padding t) (familyCloudTable H t)
        t.rows[e].tail (MachineRegularVertexBlock.oldCloud t (padding t) e) output := by
  have rotor : MachineRegularFamily.rotor H (cloudSize t t.rows[e].tail) =
      encodeWords (ExpanderTableWords.rotationWords (familyCloudTable H t t.rows[e].tail)) :=
    PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t t.rows[e].tail
      (PreprocessingFamilyBridge.cloudSize_pos_of_dart t e)
  funext i
  fin_cases i <;>
    simp [coreFrame, familyData, metadataData, MachineRegularMetadata.originalData,
      MachineRegularMetadata.cloudData, MachineRegularMetadata.prefixData,
      MachineRegularMetadata.rankData, MachineRegularMetadata.ownerData,
      MachineRegularMetadata.frame, initialData,
      MachineRegularInternalRow.coreInputTapes, MachineRegularInternalRow.coreMemory,
      MachineRegularVertexBlock.oldCloud, paddedOld,
      MachineRegularMetadata.originalMember]
  all_goals first | exact rotor | rfl

theorem vertexPlacement (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output output' : List Bool) :
    MachineCloudPadding.Placement.tapes vertexView (coreFrame (familyData H t e output'))
      (frame (familyData H t e output)) = frame (familyData H t e output') := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j with
    | inl e => cases e <;> rfl
    | inr e => rfl

theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[vertexSteps H t e output]
      (some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output))) =
      some (cfg H (clearEntry 0) (emittedData H t e output)) := by
  have raw := MachineRegularVertexBlock.originalTraceAt internalDegree degree_positive id none
    vertexSource (fun _ => rfl) t (padding t) (familyCloudTable H t) e output ()
  have finished := coreFrame_eq H t e (output ++ emittedBits H t e)
  simp only [emittedBits] at finished
  rw [← coreFrame_eq H t e output, ← finished] at raw
  have placed := Lift.trace Sum.inl vertexView vertexView_left vertexView_right
    Label.vertex (clearEntry 0) vertexStates
    (((((), false), none) : MetaState), MachineRegularFamily.readyState H)
    (frame (familyData H t e output)) vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    emittedData_eq, cfg, readyState, vertexStates, Equiv.prodAssoc_symm_apply,
    vertexSteps, emittedBits, id_eq] using placed

theorem originalTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t e output]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H none (initialData t e (output ++ emittedBits H t e))) := by
  have metadata := metadataTrace H t e output
  have family := familyTrace H t e output
  have vertex := vertexTrace H t e output
  have cleanup := clearTrace H (frame (emittedData H t e output))
  have final : clearMemory (frame (emittedData H t e output)) 7 =
      frame (initialData t e (output ++ emittedBits H t e)) := by
    rw [clearFrame]
    rfl
  rw [final] at cleanup
  exact joinTrace (joinTrace (joinTrace metadata family) vertex) cleanup

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalBody

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

theorem vertexSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalBody.vertexSteps H t e output ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := e.isLt.le.trans (GraphTables.darts_le_tableBits_length t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have raw := MachineRegularVertexBlock.originalSteps_le internalDegree degree_positive
    t (padding t) (familyCloudTable H t) e output.length
  have bound := originalTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _
    bounds.1 hR (hx.trans bounds.1) (hv.trans bounds.1) (hi.trans bounds.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) bounds.2.2
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem totalSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    totalSteps H t e output ≤ timePolynomial.eval (bodySize t output) := by
  have hsize : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hm := (MachineRegularMetadata.totalTime_le t e).trans
    (natPolynomial_eval_mono MachineRegularMetadata.timePolynomial hsize)
  have hf := (familyExecution H t e output).steps_le_m
  have hfb := MachineRegularExecutionBounds.family_budget_le t t.rows[e].tail
  simp only [MachineRegularFamily.timePolynomial, encodeWord_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hf
  have hf' := (hf.trans hfb).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial hsize)
  have hv := vertexSteps_le H t e output
  have hc := cleanupSteps_le H t e output
  simp only [totalSteps, familySteps, timePolynomial, Polynomial.eval_add]
  omega

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularOwnerBodyBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

theorem ownerTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t v output]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H none (finalData H t v output)) := (ownerInTime H t v output).evals_in_steps

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : totalSteps H t v output ≤ ownerTime H t v output :=
  (ownerInTime H t v output).steps_le_m

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem ownerPrefix_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) :
    (blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤ regularPolynomial.eval (inputLength t) := by
  have h := PreprocessingRegularBounds.regular_dummyPrefix_le t H v n
  simp only [PreprocessingRegularBounds.dummyPrefix, List.length_append] at h
  omega

theorem growingOutput_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) (output : List Bool) :
    (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤
      (ExpanderFamily.growth+1)*bodySize t output + regularPolynomial.eval (bodySize t output) := by
  have h := (ownerPrefix_length_le H t v n).trans
    (natPolynomial_eval_mono regularPolynomial (Nat.le_add_right (inputLength t) output.length))
  have hO := (wide_le t output).2.2
  rw [List.length_append]
  exact Nat.add_le_add hO h

theorem dummySteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (n : Nat) (output : List Bool) :
    MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let x := paddedNew t (padding t) v j
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hi := (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hk := cloudSize_le_input t v
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have hO := growingOutput_length_le H t v n output
  have raw := MachineRegularVertexBlock.dummySteps_le internalDegree
    MachineRegularOriginalBody.degree_positive t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length
  have bound := dummyTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _ _
    bounds.1 hR (hx.trans bounds.2.1) (hv.trans bounds.1) (hi.trans bounds.2.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) hO
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem preSteps_le (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.preSteps t v ≤ prePolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := cloudSize_le_input t v
  have hd := cloudTotal_le_input t v
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  change v.val ≤ inputLength t at hv
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2*bodySize t output+1 := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    change inputLength t + (v.val+1) ≤ _
    omega
  have hm := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineRegularOwnerBody.preSteps, prePolynomial, wide, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

theorem loopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    MachineRegularOwnerBody.loopSteps H t v output n hn ≤
      n * ((blockPolynomial internalDegree).eval (bodySize t output) + 2) := by
  induction n with
  | zero => simp only [MachineRegularOwnerBody.loopSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < padding t v := by omega
    have first := ih (by omega)
    have second := dummySteps_le H t v ⟨n, h⟩ n output
    rw [MachineRegularOwnerBody.loopSteps, Nat.succ_mul]
    change MachineRegularOwnerBody.loopSteps H t v output n _ +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v ⟨n, h⟩
        (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
          (familyCloudTable H t) v) n).length + 1) ≤ _
    omega

theorem allLoopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.loopSteps H t v output (padding t v) le_rfl ≤
      loopPolynomial.eval (bodySize t output) := by
  have hd := (cloudTotal_le_input t v).trans (wide_le t output).2.1
  have hp : padding t v ≤ (ExpanderFamily.growth+1)*bodySize t output := by omega
  have h := (loopSteps_le H t v output (padding t v) le_rfl).trans
    (Nat.mul_le_mul_right _ hp)
  simpa only [loopPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

theorem cleanupSteps_working (data : MachineRegularOwnerBody.Data)
    (fuel saved : List Bool) (d : Nat) :
    MachineRegularOwnerCleanup.steps (MachineRegularOwnerBody.working data fuel saved) d =
      2*(d+1) + data.localRank.length + data.count.length + data.rotor.length +
        data.padding.length + data.level.length + fuel.length + 6 := by
  change 2*(d+1) + ((data.localRank.length+1) + ((data.count.length+1) +
    ((data.rotor.length+1) + ((data.padding.length+1) + ((data.level.length+1) +
      ((fuel.length+1)+0)))))) = _
  omega

theorem cleanupCost_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.cleanupCost H t v output ≤
      cleanupPolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := (cloudSize_le_input t v).trans bounds.1
  have htotal := (cloudTotal_le_input t v).trans bounds.2.1
  have hl := (level_le_input t v).trans bounds.1
  have hp : MachineCloudPadding.padding (cloudSize t v) = padding t v := rfl
  by_cases hd : padding t v = 0
  · rw [MachineRegularOwnerBody.cleanupCost, ite_eq_left hd, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, List.length_nil, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · have hpositive : 0 < padding t v := by omega
    have hkpos := PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v ⟨0, hpositive⟩
    have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v hkpos
    change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
    have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
      (natPolynomial_eval_mono (rotorPolynomial internalDegree)
        (Nat.le_add_right (inputLength t) output.length))
    rw [← hrotor] at hR
    change (MachineRegularFamily.rotor H (cloudSize t v)).length ≤
      (rotorPolynomial internalDegree).eval (bodySize t output) at hR
    rw [MachineRegularOwnerBody.cleanupCost, ite_eq_right hd,
      MachineRegularOwnerBody.loopFrame, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.loopData, MachineRegularOwnerBody.vertexData,
      MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, Nat.sub_self, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

theorem ownerTime_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.ownerTime H t v output ≤ timePolynomial.eval (bodySize t output) := by
  have hp := preSteps_le t v output
  have hc := cleanupCost_le H t v output
  have hl := allLoopSteps_le H t v output
  have hf := (MachineRegularExecutionBounds.family_budget_le t v).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial
      (Nat.le_add_right (inputLength t) output.length))
  have hfamily : MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length ≤
      MachineRegularExecutionBounds.familyPolynomial.eval (bodySize t output) := by
    simpa only [bodySize, MachineRegularFamily.timePolynomial, encodeWord_length, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using hf
  simp only [MachineRegularOwnerBody.ownerTime, timePolynomial, Polynomial.eval_add,
    Polynomial.eval_ofNat]
  split_ifs <;> omega

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.totalSteps H t v output ≤ timePolynomial.eval (bodySize t output) :=
  (MachineRegularOwnerBody.totalSteps_le H t v output).trans (ownerTime_le H t v output)

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularTable
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

namespace Header

variable {σ : Type}

theorem readTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[readTime t]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ := by
  have hi : (advance (TM2.step (program q)))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ :=
    initStep q _ _ ambient register
  have hn := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .vertices)
    (lookupSlots_injective .vertices) (Label.lookup .vertices) (some Label.seedM)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 0 t.vertices (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) register
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hn
  have hs : (advance (TM2.step (program q)))^[1]
      (some ⟨some .seedM, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 1) [] [] [] [] [] output⟩ :=
    seedMStep q _ _ _ ambient none
  have hm := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .darts)
    (lookupSlots_injective .darts) (Label.lookup .darts) (some Label.clearIndex)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
      (encodeWord 1) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 1 t.darts (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) none
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hm
  have hc : (advance (TM2.step (program q)))^[1]
      (some ⟨some .clearIndex, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ :=
    clearIndexStep q _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hi hn) hs) hm) hc

theorem prefixTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[MachineCloudPrefix.totalTime t t.vertices []]
      (some ⟨some (.prefix .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .count), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩ := by
  have h := MachineCloudPadding.Placement.trace Sum.inl prefixView prefixView_left prefixView_right
    Label.prefix (some (Label.copyFirst .count))
    (frame [] [] [] [] [] (encodeWord t.darts) [] [] [] [] [] [] output)
    (MachineCloudPrefix.program (σ := σ)) (program q) (fun _ => rfl) _ _ _
    (MachineCloudPrefix.prefixTrace t t.vertices (Nat.le_refl _) [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    prefixTapes, frame_m, frame_index, frame_work, frame_scratch, frame_vertices, frame_darts,
    frame_emit, frame_output, List.append_nil, paddingTotal, frame, memory,
    mTape, indexTape, workTape, scratchTape, verticesTape, dartsTape, emitTape, outputTape] using h

theorem emitTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[emitTime q t output]
      (some ⟨some (.copyFirst .rEmit), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := by
  have hr := MachineCopy.copyTrace dartsTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .rEmit) (Label.copySecond .rEmit)
    (some (Label.copyFirst .nEmit)) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output)
    rfl (ambient, false) register
  simp only [frame_darts, frame_emit, encodeWord_length, List.append_nil, update_frame_emit] at hr
  have hn := MachineCopy.copyTrace verticesTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .nEmit) (Label.copySecond .nEmit)
    (some Label.appendFirst) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (encodeWord (dartTotal q t)) output)
    rfl (ambient, false) none
  simp only [frame_vertices, frame_emit, encodeWord_length, update_frame_emit, ← headerBits_eq] at hn
  have ha := MachineAppendAt.appendTrace emitTape outputTape scratchTape
    (by decide) (by decide) (by decide) false Label.appendFirst Label.appendSecond Label.appendThird
    (some Label.cleanupZeros) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (headerBits q t) output)
    rfl (ambient, false) none
  simp only [frame_emit, frame_output, MachineAppendAt.appendTapes,
    Reduction.MachineTransfer.tapesAt, update_frame_emit, update_frame_output] at ha
  have hz : (advance (TM2.step (program q)))^[1]
      (some ⟨some .cleanupZeros, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
          (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩) =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
          (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩ :=
    cleanupZerosStep q _ _ _ _ _ _ ambient none
  have hc := MachineLookup.discardTrace queryTape Label.clearQuery Label.done (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
      (encodeWord (dartTotal q t)) [] (output ++ headerBits q t))
    t.vertices [] (by simp) (ambient, false) none
  simp only [update_frame_query] at hc
  have hd : (advance (TM2.step (program q)))^[1]
      (some ⟨some .done, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := rfl
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hr hn) ha) hz) hc) hd

theorem trace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[totalTime q t output]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ :=
  appendTrace _ (appendTrace _ (appendTrace _ (readTrace q t output ambient register)
    (prefixTrace q t output ambient none)) (computeTrace q t output ambient none))
      (emitTrace q t output ambient none)

end Header

namespace Top

theorem headerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t output]
      (some (cfg H (some (.header .init)) (inputData t output) (fun _ => []) counters)) =
      some (cfg H (some .oldSeed)
        (headerData t (output ++ Header.headerBits PreprocessingRegularTables.internalDegree t))
        (headerStacks t) counters) := by
  have raw := Header.trace PreprocessingRegularTables.internalDegree t output () none
  have placed := Lift.trace headerTape headerView headerView_left headerView_right
    Label.header (some .oldSeed) headerStates
    (MachineRegularInternalRow.coreInitialState PreprocessingRegularTables.internalDegree
      MachineRegularOriginalBody.degree_positive (), (MachineRegularFamily.readyState H, none))
    (frame (inputData t output) (fun _ => []) counters)
    (Header.program PreprocessingRegularTables.internalDegree) (program H) (fun _ => rfl)
    _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, headerPlacement,
    headerAux_empty, cfg, readyState, MachineRegularOriginalBody.readyState, headerStates,
    Equiv.coe_fn_mk, headerData, inputData, headerStacks] using placed

def oldData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with globalIndex := encodeWord index }

theorem originalData_eq (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalBody.initialData t e output = oldData t e.val output := rfl

theorem oldBodyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOriginalBody.totalSteps H t e output]
      (some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry))
        (oldData t e.val output) header counters)) =
      some (cfg H (some .oldIncrement)
        (oldData t e.val (output ++ MachineRegularOriginalBody.emittedBits H t e)) header counters) := by
  have raw := MachineRegularOriginalBody.originalTrace H t e output
  have placed := Lift.trace Sum.inl bodyView bodyView_left bodyView_right Label.oldBody
    (some .oldIncrement) (Equiv.refl _) none
    (frame (oldData t e.val output) header counters)
    (MachineRegularOriginalBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, bodyPlacement,
    MachineRegularOriginalBody.cfg, originalData_eq, cfg, readyState, Equiv.refl_apply] using placed

theorem oldIncrementStep (H : BaseTable) (t : GraphTables.Table) (index : Nat)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldIncrement) (oldData t index output) header counters)) =
      some (cfg H (some .oldGuard) (oldData t (index + 1) output) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 1) Label.oldGuard)
    (readyState H) (frame (oldData t index output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.oldGuard, readyState H,
    Function.update (frame (oldData t index output) header counters) (coreTape 1)
      (true :: encodeWord index)⟩ : TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  simp only [cfg, oldData, encodeWord, List.replicate_succ, List.cons_append]

theorem oldPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.darts →
    (advance (TM2.step (program H)))^[oldElapsed H t output k]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t k (output ++ oldPrefix H t k)) header
        (counterStacks (encodeWord (t.darts-k)) [] [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [oldElapsed, oldPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.darts := by omega
    have hremaining : t.darts-k = (t.darts-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := oldGuardStep H (oldData t k (output ++ oldPrefix H t k)) header
      (t.darts-(k+1))
    rw [← hremaining] at guard
    have body := oldBodyTrace H t ⟨k,hlt⟩ (output ++ oldPrefix H t k) header
      (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have increment := oldIncrementStep H t k
      ((output ++ oldPrefix H t k) ++ MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩)
      header (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have combined := joinTrace_p0 (joinTrace_p0 (joinTrace_p0 previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOriginalBody.emittedBits H t) k hlt
    change oldPrefix H t (k+1) = oldPrefix H t k ++
      MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩ at bits
    simpa only [oldElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem oldLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[oldElapsed H t output t.darts + 1]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := oldPrefixTrace H t output header t.darts (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_p0 prefixRun (oldGuardExit H _ header)

theorem oldSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldSeed) (headerData t output) header counters)) =
      some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header counters) := by
  change some (TM2.stepAux (.push (coreTape 1) (fun _ => false)
    (.goto fun _ => Label.copyFirst CopyPhase.old)) (readyState H) (frame (headerData t output) header counters)) = _
  change some (⟨some (Label.copyFirst CopyPhase.old), readyState H,
    Function.update (frame (headerData t output) header counters) (coreTape 1) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  rfl

theorem copyOldTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[2*(t.darts+2)]
      (some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] [])) := by
  have h := MachineCopy.copyTrace (coreTape 6) oldFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .old) (.copySecond .old)
    (some .oldGuard) (program H) rfl rfl
    (frame (oldData t 0 output) header (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [frame_darts, oldData, headerData, inputData, encodeWord_length,
    frame_oldFuel, List.append_nil, update_frame_oldFuel, cfg, readyState, Nat.add_assoc] using h

theorem oldStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.darts+2)+(oldElapsed H t output t.darts+1)]
      (some (cfg H (some .oldSeed) (headerData t output) header (counterStacks [] [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) :=
  joinTrace_p0 (joinTrace_p0 (oldSeedStep H t output header _) (copyOldTrace H t output header))
    (oldLoopTrace H t output header)

theorem ownerSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) header counters)) =
      some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) header counters) := by
  change some (TM2.stepAux
    (.push (coreTape 2) (fun _ => false) (.push (coreTape 5) (fun _ => false)
      (.goto fun _ => Label.copyFirst CopyPhase.owner))) (readyState H)
      (frame (oldData t t.darts output) header counters)) = _
  simp only [TM2.stepAux, frame_core]
  change some (⟨some (Label.copyFirst CopyPhase.owner), readyState H,
    Function.update (Function.update (frame (oldData t t.darts output) header counters)
      (coreTape 2) [false]) (coreTape 5) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner, update_frame_offset]
  simp only [cfg, ownerData, oldData, PreprocessingPaddingOffsets.offset_zero, Nat.add_zero,
    encodeWord, List.replicate_zero, List.nil_append]

theorem copyOwnerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[2*(t.vertices+2)]
      (some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] (encodeWord t.vertices) [] [])) := by
  have h := MachineCopy.copyTrace (headerTape Header.nTape) ownerFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .owner) (.copySecond .owner)
    (some .ownerGuard) (program H) rfl rfl
    (frame (ownerData t 0 output) (headerStacks t) (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [headerStacks, frame_header_n, encodeWord_length, frame_ownerFuel,
    List.append_nil, update_frame_ownerFuel, cfg, readyState, Nat.add_assoc] using h

theorem ownerPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (old owners : List Bool) :
    MachineCloudPadding.Placement.tapes ownerView (MachineRegularOwnerBody.frame data)
      (frame extra header (counterStacks old owners [] [])) =
      frame data header (counterStacks old owners [] []) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

theorem ownerInitialData_eq (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.initialData t v output = ownerData t v.val output := rfl

theorem ownerBodyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (owners : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerBody.totalSteps H t v output]
      (some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry))
        (ownerData t v.val output) header (counterStacks [] owners [] []))) =
      some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header (counterStacks [] owners [] [])) := by
  have raw := MachineRegularOwnerBody.ownerTrace H t v output
  have placed := MachineCloudPadding.Placement.trace ownerTape ownerView ownerView_left ownerView_right
    Label.ownerBody (some .ownerIncrement)
    (frame (ownerData t v.val output) header (counterStacks [] owners [] []))
    (MachineRegularOwnerBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    ownerPlacement, MachineRegularOwnerBody.cfg, MachineRegularOwnerBody.readyState,
    ownerInitialData_eq, cfg, readyState] using placed

theorem ownerIncrementStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header counters)) =
      some (cfg H (some .ownerGuard)
        (ownerData t (v.val+1) (output ++ MachineRegularOwnerBody.ownerBits H t v)) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 2) Label.ownerGuard) (readyState H)
    (frame (MachineRegularOwnerBody.finalData H t v output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.ownerGuard, readyState H,
    Function.update (frame (MachineRegularOwnerBody.finalData H t v output) header counters)
      (coreTape 2) (true :: encodeWord v.val)⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner]
  have offset := PreprocessingRegularBounds.offset_succ (PreprocessingRegularTables.padding t) v.val v.isLt
  simp only [cfg, ownerData, headerData, inputData, MachineRegularOwnerBody.finalData,
    MachineRegularOwnerBody.initialData, offset, encodeWord, List.replicate_succ,
    List.cons_append, Nat.add_assoc]

theorem ownerPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.vertices →
    (advance (TM2.step (program H)))^[ownerElapsed H t output k]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t k (output ++ ownerPrefix H t k)) header
        (counterStacks [] (encodeWord (t.vertices-k)) [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [ownerElapsed, ownerPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.vertices := by omega
    have hremaining : t.vertices-k = (t.vertices-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := ownerGuardStep H (ownerData t k (output ++ ownerPrefix H t k)) header
      (t.vertices-(k+1))
    rw [← hremaining] at guard
    have body := ownerBodyTrace H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (encodeWord (t.vertices-(k+1)))
    have increment := ownerIncrementStep H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (counterStacks [] (encodeWord (t.vertices-(k+1))) [] [])
    have combined := joinTrace_p0 (joinTrace_p0 (joinTrace_p0 previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOwnerBody.ownerBits H t) k hlt
    change ownerPrefix H t (k+1) = ownerPrefix H t k ++
      MachineRegularOwnerBody.ownerBits H t ⟨k,hlt⟩ at bits
    simpa only [ownerElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem ownerLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[ownerElapsed H t output t.vertices+1]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := ownerPrefixTrace H t output header t.vertices (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_p0 prefixRun (ownerGuardExit H _ header)

theorem ownerStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.vertices+2)+(ownerElapsed H t output t.vertices+1)]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) (headerStacks t)
        (counterStacks [] [] [] [])) :=
  joinTrace_p0 (joinTrace_p0 (ownerSeedStep H t output (headerStacks t) _) (copyOwnerTrace H t output))
    (ownerLoopTrace H t output (headerStacks t))

theorem owner_output_eq_ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    (Header.headerBits PreprocessingRegularTables.internalDegree t ++ oldPrefix H t t.darts) ++
        ownerPrefix H t k =
      PreprocessingRegularBounds.ownerPrefix t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) k := by
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      PreprocessingRegularBounds.ownerBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  simp only [Header.headerBits, Header.vertexTotal, Header.dartTotal, oldPrefix,
    ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    PreprocessingRegularBounds.ownerPrefix, PreprocessingRegularBounds.header]
  rw [oldBits, ownerBits]

theorem cleanupPrefixTrace (H : BaseTable) (base : Tape → List Bool) (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[cleanupTime base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, cleaned base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k,h⟩ (cleaned base k)
    have atEntry : clearEntry k = some (.clear ⟨k,h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [cleanupTime, cleaned, dite_eq_left h] using joinTrace_p0 first second

theorem cleanupTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, cleaned base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using cleanupPrefixTrace H base 7 le_rfl

theorem cleaned_finalStacks (t : GraphTables.Table) (output : List Bool) :
    cleaned (finalStacks t output) 7 =
      frame (inputData t output) (fun _ => []) (counterStacks [] [] [] []) := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j with
    | inl k => cases k with
      | inl k => cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => fin_cases i <;> rfl

theorem finalOutput_eq (H : BaseTable) (t : GraphTables.Table) :
    finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.regularize H t) := by
  change finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.ofCloudTables t
    (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t))
  rw [PreprocessingRegularWords.tableBits_ofCloudTables]
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      (fun v => (List.ofFn (PreprocessingRegularWords.dummyVertexBits t
        (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t) v)).flatten) := rfl
  simp only [finalOutput, oldOutput, headerOutput, Header.headerBits, Header.vertexTotal,
    Header.dartTotal, oldPrefix, ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    List.append_assoc]
  rw [oldBits, ownerBits]

end Top

end BinPackingGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularTableRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularTable.Top

section

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinTrace_p1 (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinTrace_p1 (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinTrace_p1 (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => (fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]); rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    rw [← input_stacks_eq]
    exact (update_frame_output (inputData t []) (fun _ => []) (counterStacks [] [] [] [])
      (PortTables.tableBits (PreprocessingRegularTables.regularize H t))).symm
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds

theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end BinPackingGames.Foundations.Complexity.MachineRegularTable.Top

namespace BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)

noncomputable def terminalRun (H : PreprocessingRegularTables.BaseTable)
    (t : GraphTables.Table) :
    MachineCanonicalOutput.TerminalRun (rawProgram H) (GraphTables.tableBits t)
      (PortTables.inputBits (PreprocessingStageMaps.regular H t))
      (MachineRegularTable.Top.timePolynomial.eval (GraphTables.tableBits t).length) where
  state := readyState H
  tapes := Function.update
    (initList (MachineRegularTable.Top.machine H) (GraphTables.tableBits t)).stk
    (coreTape 8) (PortTables.inputBits (PreprocessingStageMaps.regular H t))
  execution := by
    simpa only [sourceMachine_eq, FinTM2.Cfg, FinTM2.step, MachineRegularTable.Top.machine,
      PreprocessingMachineBounds.inputLength, PreprocessingStageMaps.regular,
      PortTables.inputBits] using!
      MachineRegularTable.Top.machineInTime H t
  output_eq := by
    change Function.update _ (coreTape 8) _ (coreTape 8) = _
    exact Function.update_self _ _ _

noncomputable def computableInPolyTime (H : PreprocessingRegularTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingRegularTables.internalDegree + 1))
      (PreprocessingStageMaps.regular H) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRowBody
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

theorem steps_le (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) :
    steps graph vertex left right ≤
      (14 * (l + r) + 10) * (PortTables.tableBits graph).length + 12 * (l + r) + 15 := by
  have hl := PoweringMachineWord.steps_le graph l vertex left
  have hr := PoweringMachineWord.steps_le graph r vertex right
  have he := MachineUnaryEqualityBit.steps_le
    (endpoint graph vertex left).val (endpoint graph vertex right).val
  have hleft := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex left).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  have hright := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex right).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  unfold steps
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hl hr ⊢
  omega

theorem fieldTrace (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ q, program (labels q) = instruction hl hr placement left right labels exit q)
    (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits graph)
    (scratchEmpty : base (placement (.inl 5)) = [])
    (leftCopyEmpty : base (placement (.inl 8)) = [])
    (rightCopyEmpty : base (placement (.inl 9)) = [])
    (suffix : List Bool) (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix)
    (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex left right]
      (some ⟨some (labels (entry l r)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph hl hr placement vertex left right base⟩ := by
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  have leftFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h6 : j ≠ 6) :
      afterLeft (placement (.inl j)) = base (placement (.inl j)) :=
    wordTapes_role graph hl placement distinct false vertex left base j h2 h3 h4 h6
  have rightFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = afterLeft (placement (.inl j)) :=
    wordTapes_role graph hr placement distinct true vertex right afterLeft j h2 h3 h4 h7
  have bothFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4)
      (h6 : j ≠ 6) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = base (placement (.inl j)) :=
    (rightFrame j h2 h3 h4 h7).trans (leftFrame j h2 h3 h4 h6)
  have leftRun := PoweringMachineWord.wordTrace graph l
    (placement ∘ PoweringMachineTapes.wordPlacement hl false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hl false)) vertex left
    (fun q => labels (.inl q))
    (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) program
    (fun q => atLabels (.inl q)) base
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using tableWord)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using scratchEmpty)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using sourceWord)
    (ambient, false, none) none
  have rightTable : afterLeft (placement (.inl 0)) = PortTables.tableBits graph :=
    (leftFrame 0 (by decide) (by decide) (by decide) (by decide)).trans tableWord
  have rightScratch : afterLeft (placement (.inl 5)) = [] :=
    (leftFrame 5 (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have rightSource : afterLeft (placement (.inl 1)) = encodeWord vertex.val ++ suffix :=
    (leftFrame 1 (by decide) (by decide) (by decide) (by decide)).trans sourceWord
  have rightRun := PoweringMachineWord.wordTrace graph r
    (placement ∘ PoweringMachineTapes.wordPlacement hr true)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hr true)) vertex right
    (fun q => labels (.inr (.inl q))) (some (labels (.inr (.inr .seedLeft)))) program
    (fun q => atLabels (.inr (.inl q))) afterLeft
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using rightTable)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using rightScratch)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using rightSource)
    (ambient, false, none) none
  have leftEndpoint : afterBoth (placement (.inl 6)) =
      encodeWord (endpoint graph vertex left).val ++ base (placement (.inl 6)) := by
    rw [rightFrame 6 (by decide) (by decide) (by decide) (by decide)]
    dsimp only [afterLeft, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_false, PoweringMachineTapes.leftEndpoint,
      wordTapes, endpoint] using leftRun.2
  have rightEndpoint : afterBoth (placement (.inl 7)) =
      encodeWord (endpoint graph vertex right).val ++ afterLeft (placement (.inl 7)) := by
    dsimp only [afterBoth, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_true, PoweringMachineTapes.rightEndpoint,
      wordTapes, endpoint] using rightRun.2
  have copiesLeft : afterBoth (placement (.inl 8)) = [] :=
    (bothFrame 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans leftCopyEmpty
  have copiesRight : afterBoth (placement (.inl 9)) = [] :=
    (bothFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans rightCopyEmpty
  have scratchBoth : afterBoth (placement (.inl 5)) = [] :=
    (bothFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have equalityRun := MachineUnaryEqualityBit.equalityTrace
    (placement ∘ PoweringMachineTapes.equalityPlacement max)
    (distinct.comp (PoweringMachineTapes.equalityPlacement_injective max))
    (fun q => labels (.inr (.inr q))) exit program (fun q => atLabels (.inr (.inr q)))
    afterBoth (endpoint graph vertex left).val (endpoint graph vertex right).val
    (base (placement (.inl 6))) (afterLeft (placement (.inl 7)))
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_zero,
      PoweringMachineTapes.leftEndpoint] using leftEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_one,
      PoweringMachineTapes.rightEndpoint] using rightEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_two,
      PoweringMachineTapes.leftCopy] using copiesLeft)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_three,
      PoweringMachineTapes.rightCopy] using copiesRight)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_four,
      PoweringMachineTapes.scratch] using scratchBoth)
    ambient
  have joined := joinTrace (joinTrace leftRun.1 rightRun.1) equalityRun
  simpa only [steps, entry, MachineUnaryEqualityBit.clean, Function.comp_apply,
    PoweringMachineTapes.equalityPlacement_five, PoweringMachineTapes.rowOutput,
    finalTapes, resultBit, Fin.ext_iff,
    afterLeft, afterBoth, wordTapes] using joined

end BinPackingGames.Foundations.Complexity.PoweringMachineEqualityField

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

theorem headerTrace (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction n h placement ports direction labels exit l)
    (base : K → List Bool) (tableWord : base (placement (table max)) = PortTables.tableBits input)
    (scratchEmpty : base (placement (scratch max)) = []) (suffix : List Bool)
    (sourceWord : base (placement (start max)) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps input n vertex ports direction]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes input n h placement vertex ports direction base⟩ ∧
    finalTapes input n h placement vertex ports direction base (placement (rowOutput max)) =
      encodeWords (headerWords input n vertex ports direction) ++ base (placement (rowOutput max)) := by
  have hd (i j : Tape max) (hne : i ≠ j) : placement i ≠ placement j :=
    fun eq => hne (distinct eq)
  have hsourceOut : placement (start max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [start, rowOutput])
  have hscratchOut : placement (scratch max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [scratch, rowOutput])
  have htableOut : placement (table max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [table, rowOutput])
  let mid := afterReverse n placement vertex ports direction base
  have hrev := MachineUnaryAffineAt.seededAffineTrace
    (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
    (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut
    (blockSize d n) (reverseOffset d n ports direction)
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (tailEntry n direction))) program
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base vertex.val suffix sourceWord scratchEmpty ambient register
  have hreverseTrace : (advance (TM2.step program))^[2 * (vertex.val + 1) + 1]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨some (labels (tailEntry n direction)), (ambient, none), mid⟩ := by
    simpa only [entry, mid, afterReverse, reverseValue] using hrev
  have hmidSource : mid (placement (start max)) = encodeWord vertex.val ++ suffix := by
    simpa only [mid, afterReverse, Function.update_of_ne hsourceOut] using sourceWord
  have hmidScratch : mid (placement (scratch max)) = [] := by
    simpa only [mid, afterReverse, Function.update_of_ne hscratchOut] using scratchEmpty
  have hmidTable : mid (placement (table max)) = PortTables.tableBits input := by
    simpa only [mid, afterReverse, Function.update_of_ne htableOut] using tableWord
  cases direction with
  | false =>
    have hcopy := MachineUnaryAffineAt.seededAffineTrace
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut 1 0
      (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
      (labels (.inr (.inl .restore))) exit program
      (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
      (atLabels (.inr (.inl .restore))) mid vertex.val suffix hmidSource hmidScratch ambient none
    constructor
    · rw [steps, ite_eq_right Bool.false_ne_true, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, Bool.false_eq_true, ite_false, finalTapes, Nat.one_mul,
        Nat.add_zero] using hcopy
    · simp only [finalTapes, Bool.false_eq_true, ite_false, Function.update_self,
        afterReverse, headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc]
  | true =>
    have hword := PoweringMachineWord.wordTrace input (n + 1)
      (placement ∘ headerPlacement h) (distinct.comp (headerPlacement_injective h)) vertex ports
      (fun z => labels (.inr (.inr z))) exit program (fun z => atLabels (.inr (.inr z))) mid
      (by simpa only [Function.comp_apply, headerPlacement_table] using hmidTable)
      (by simpa only [Function.comp_apply, headerPlacement_scratch] using hmidScratch)
      suffix (by simpa only [Function.comp_apply, headerPlacement_start] using hmidSource) ambient none
    constructor
    · rw [steps, ite_eq_left rfl, Nat.add_comm, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, ite_true, if_true, finalTapes] using hword.1
    · have hout := hword.2
      simp only [Function.comp_apply, headerPlacement_output] at hout
      simpa only [finalTapes, ite_true, if_true, mid, afterReverse, Function.update_self,
        headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc] using hout

theorem steps_le (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps input n vertex ports direction ≤
      (14 * (n + 1) + 4) * (PortTables.tableBits input).length + 12 * (n + 1) + 6 := by
  have hv : vertex.val ≤ (PortTables.tableBits input).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length input)
  have hw := PoweringMachineWord.steps_le input (n + 1) vertex ports
  cases direction <;> simp only [steps, Bool.false_eq_true, ite_false, ite_true, if_true]
  · simp only [Nat.add_mul]
    omega
  · calc
      _ ≤ (2 * (PortTables.tableBits input).length + 3) +
          ((14 * (n + 1) + 2) * (PortTables.tableBits input).length + 12 * (n + 1) + 3) :=
        Nat.add_le_add (by omega) hw
      _ = _ := by simp only [Nat.add_mul]; omega

end BinPackingGames.Foundations.Complexity.PoweringMachineRowHeaders

namespace BinPackingGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

def instruction (placement : Tape max → K) : (op : Instruction d) → op.radius ≤ max →
    (Label op → Λ) → Option Λ → Label op → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .relation path port a b, bounded, labels, exit =>
      PoweringMachineRelationField.instruction placement path bounded port a b labels exit
  | .equal left right, bounded, labels, exit =>
      PoweringMachineEqualityField.instruction
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement left.get right.get labels exit

theorem fieldTrace (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max)
    (labels : Label op → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement op bounded labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex op]
      (some ⟨some (labels (entry op)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph placement vertex op bounded base⟩ := by
  cases op with
  | relation path port a b =>
      exact (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        labels exit program atLabels graph vertex base ready.table ready.scratch suffix
        ready.source ambient).1
  | equal left right =>
      exact PoweringMachineEqualityField.fieldTrace graph _ _ placement distinct
        vertex left.get right.get labels exit program atLabels base ready.table ready.scratch
        ready.leftCopy ready.rightCopy suffix ready.source ambient

theorem finalTapes_output (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex op bounded base (placement (.inl 10)) =
      PoweringMachineRow.encodeBit (evaluate graph vertex op) ++ base (placement (.inl 10)) := by
  cases op with
  | relation path port a b =>
      have h := (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        id none (PoweringMachineRelationField.instruction placement path bounded port a b id none)
        (fun _ => rfl) graph vertex base ready.table ready.scratch suffix ready.source ()).2
      have he : ∀ bit : Bool, encodeWord (GraphTables.bitWord bit) =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineRelationField.bit, PoweringMachineRelationField.endpoint,
        evaluate, he] using h
  | equal left right =>
      have h := PoweringMachineEqualityField.finalTapes_output graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded) placement distinct
        vertex left.get right.get base
      have he : ∀ bit : Bool, MachineUnaryEqualityBit.bitEncoding bit =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineEqualityField.resultBit, PoweringMachineEqualityField.endpoint,
        PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get, evaluate, he] using h

end BinPackingGames.Foundations.Complexity.PoweringMachineField

namespace BinPackingGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

def instruction (placement : PoweringMachineTapes.Tape max → K)
    (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A) :=
  MachineFiniteSequence.instruction LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    commands labels exit

theorem planTrace (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max))
    (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A))
    (atLabels : ∀ l, program (labels l) = instruction placement commands labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineField.Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph placement vertex commands base]
      (some ⟨entry commands labels exit, MachineUnaryEqualityBit.clean ambient, base⟩) =
    some ⟨exit, MachineUnaryEqualityBit.clean ambient,
      finalTapes graph placement vertex commands base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    (result graph placement vertex) (fun op _ => PoweringMachineField.steps graph vertex op.val)
    program (PoweringMachineField.Ready graph placement vertex suffix)
    (fun _ => MachineUnaryEqualityBit.clean ambient) id commands
  · intro op _ tapes good
    exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
      op.property tapes suffix good
  · intro op _ localLabels localExit atLocal tapes good
    exact PoweringMachineField.fieldTrace graph placement distinct vertex op.val op.property
      localLabels localExit program atLocal tapes suffix good ambient
  · exact atLabels
  · exact ready

theorem finalTapes_output (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex commands base (placement (.inl 10)) =
      PoweringMachineRow.encodeBits ((commands.map (fun op => evaluate graph vertex op.val)).reverse) ++
        base (placement (.inl 10)) := by
  induction commands generalizing base with
  | nil => rfl
  | cons op commands ih =>
      have nextReady := PoweringMachineField.ready_finalTapes graph placement distinct vertex
        op.val op.property base suffix ready
      change finalTapes graph placement vertex commands
        (result graph placement vertex op base) (placement (.inl 10)) = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineField.finalTapes_output graph placement distinct vertex
        op.val op.property base suffix ready]
      simp only [List.map_cons, List.reverse_cons, PoweringMachineRow.encodeBits_append,
        PoweringMachineRow.encodeBits, List.append_nil,
        List.append_assoc]

theorem rowPlan_output (graph : PortTables.Table vertices d)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (distinct : Function.Injective placement) (vertex : Fin vertices) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex (boundedRowPlan n ports direction).reverse base
      (placement (.inl 10)) =
      PoweringRowData.dataTape graph n (direction, vertex, ports) ++ base (placement (.inl 10)) := by
  rw [finalTapes_output graph placement distinct vertex _ base suffix ready]
  rw [List.map_reverse, List.reverse_reverse, PoweringFieldPlan.dataTape_eq_plan]
  have h := congrArg (List.map (evaluate graph vertex)) (boundedRowPlan_values n ports direction)
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun bits => PoweringMachineRow.encodeBits bits ++ base (placement (.inl 10))) h

end BinPackingGames.Foundations.Complexity.PoweringMachinePlan

namespace BinPackingGames.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

theorem field_steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (op : Instruction d) (bounded : op.radius ≤ max) :
    PoweringMachineField.steps graph vertex op ≤
      fieldBudget max (PortTables.tableBits graph).length := by
  cases op with
  | relation path port left right =>
      change path.length ≤ max at bounded
      have h := PoweringMachineRelationField.steps_le path port left right graph vertex
      have coefficient : 14 * path.length + 9 ≤ 28 * max + 10 := by omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineRelationField.steps path port left right graph vertex ≤ _
      unfold fieldBudget
      omega
  | equal left right =>
      change Nat.max left.length right.length ≤ max at bounded
      have hl : left.length ≤ max := (le_max_left _ _).trans bounded
      have hr : right.length ≤ max := (le_max_right _ _).trans bounded
      have h := PoweringMachineEqualityField.steps_le graph vertex left.get right.get
      have coefficient : 14 * (left.length + right.length) + 10 ≤ 28 * max + 10 := by
        omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineEqualityField.steps graph vertex left.get right.get ≤ _
      unfold fieldBudget
      omega

theorem plan_steps_le (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (commands : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex commands base ≤
      commands.length * fieldBudget max (PortTables.tableBits graph).length := by
  induction commands generalizing base with
  | nil => simp only [PoweringMachinePlan.steps, MachineFiniteSequence.steps,
      List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons op commands ih =>
      have first := field_steps_le graph vertex op.val op.property
      have rest := ih (PoweringMachinePlan.result graph placement vertex op base)
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex commands
          (PoweringMachinePlan.result graph placement vertex op base) ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add first rest

theorem rowPlan_steps_le (graph : PortTables.Table vertices d) (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (vertex : Fin vertices) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex
        (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base ≤
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
        ((28 * (2 * (n + 1)) + 10) * (PortTables.tableBits graph).length +
          24 * (2 * (n + 1)) + 15) := by
  have h := plan_steps_le graph placement vertex
    (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base
  simpa only [List.length_reverse, boundedRowPlan_length, fieldBudget] using h

end BinPackingGames.Foundations.Complexity.PoweringPlanBudget

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

def instruction (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K)
    (output : K) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ) :
    Label n ports direction → TM2.Stmt (fun _ : K => Bool) Λ (State d n)
  | .inl q => PoweringMachinePlan.instruction placement (commands n ports direction)
      (fun z => labels (.inl z)) (some (labels (.inr (.inl ())))) q
  | .inr (.inl _) => PoweringMasterState.rowAt (t := n + 1) (placement (.inl 10)) output
      (PoweringRowData.fixedLabelAt d n) (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n)))))
  | .inr (.inr q) => PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction (fun z => labels (.inr (.inr z))) exit q

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex ports direction base output =
      encodeWords (rowWords graph n vertex ports direction) ++ base output := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction id none
    (PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction id none) (fun _ => rfl)
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source) () none).2
  simp only [PoweringMachineTapes.rowOutput, headerPlacement_output] at hh
  calc
    finalTapes graph n placement output vertex ports direction base output =
        encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
          afterEmit graph n placement output vertex ports direction base output := hh
    _ = encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
        (rowRelation graph n vertex ports direction ++ base output) := by
      simp only [afterEmit, Function.update_self]
      rw [show afterPlan graph n placement vertex ports direction base output = base output from
        plan_other graph placement vertex _ base output outside]
    _ = _ := PoweringRowHeaderSemantics.header_relation_bits graph n vertex ports direction (base output)

theorem rowTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output ports direction labels exit l)
    (base : K → List Bool) (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n ports direction]
      (some ⟨some (labels (entry n ports direction)), PoweringMasterState.clean (bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (bufferSize d n),
        finalTapes graph n placement output vertex ports direction base⟩ := by
  have hp := PoweringMachinePlan.planTrace graph placement distinct vertex (commands n ports direction)
    (fun q => labels (.inl q)) (some (labels (.inr (.inl ())))) program
    (fun q => atLabels (.inl q)) base suffix ready.1 (emptyBuffer (bufferSize d n))
  rw [planSteps_eq, plan_entry_eq] at hp
  let mid := afterPlan graph n placement vertex ports direction base
  have hinput : mid (placement (.inl 10)) = PoweringMachineRow.encodeBits
      (List.ofFn (PoweringRowData.rowBits graph n (direction, vertex, ports))) ++ [] := by
    dsimp only [mid, afterPlan, commands]
    have h := PoweringMachinePlan.rowPlan_output graph n ports direction placement distinct vertex base suffix ready.1
    simpa only [ready.2, List.append_nil, PoweringRowData.dataTape_eq] using h
  have hr := PoweringMasterState.step_rowAt_clean (t := n + 1) (placement (.inl 10)) output
    (PoweringRowData.fixedLabelAt d n)
    (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n))))) program (labels (.inr (.inl ())))
    (atLabels (.inr (.inl ()))) (Ne.symm (outside _))
    (PoweringRowData.rowBits graph n (direction, vertex, ports))
    (emptyBuffer (bufferSize d n)) [] mid hinput
  rw [rowBlock_eq_rowRelation] at hr
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction (fun q => labels (.inr (.inr q))) exit program
    (fun q => atLabels (.inr (.inr q)))
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source)
    (emptyBuffer (bufferSize d n), false, none) none).1
  rw [steps, Nat.add_comm, Function.iterate_add_apply, Function.iterate_succ_apply']
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (advance (TM2.step program) ((advance (TM2.step program))^[planSteps graph vertex (commands n ports direction)]
      (some ⟨some (labels (planMain (commands n ports direction) (.inl ()))),
        MachineUnaryEqualityBit.clean (emptyBuffer (bufferSize d n)), base⟩))) = _
  rw [hp]
  simp only [advance_some]
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (TM2.step program ⟨some (labels (.inr (.inl ()))),
      PoweringMasterState.withBuffer (emptyBuffer (bufferSize d n)), mid⟩) = _
  rw [hr]
  exact hh

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps graph vertex n ports direction ≤ budget d n (PortTables.tableBits graph).length := by
  have hp := PoweringPlanBudget.rowPlan_steps_le graph n ports direction id vertex (fun _ => [])
  rw [planSteps_eq] at hp
  have hh := PoweringMachineRowHeaders.steps_le graph n vertex ports direction
  change planSteps graph vertex (commands n ports direction) ≤
    PoweringPlanBudget.rowBudget d n (PortTables.tableBits graph).length at hp
  unfold steps budget
  omega

end BinPackingGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

def sequenceInstruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : SequenceLabel ops → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  MachineFiniteSequence.instruction LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    ops labels exit

def instruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (labels : Label d n → Λ) (exit : Option Λ) :
    Label d n → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  sequenceInstruction n placement output (commands d n) labels exit

theorem costSum_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ops : List (Command d n)) :
    costSum graph vertex n ops ≤
      ops.length * PoweringMachineRowBody.budget d n (PortTables.tableBits graph).length := by
  induction ops with
  | nil => simp only [costSum, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons j ops ih =>
      have hfirst := PoweringMachineRowBody.steps_le graph vertex n (ports j) (direction j)
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        costSum graph vertex n ops ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add hfirst ih

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    steps graph vertex n ≤ budget d n (PortTables.tableBits graph).length := by
  simpa only [steps, budget, commands_length] using costSum_le graph vertex n (commands d n)

theorem sequenceTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n))
    (labels : SequenceLabel ops → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction n placement output ops labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[sequenceSteps graph n placement output vertex ops base]
      (some ⟨sequenceEntry ops labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        sequenceTapes graph n placement output vertex ops base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j))
    program (PoweringMachineRowBody.Ready graph n placement vertex suffix)
    (fun _ => PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)) id ops
  · intro j _ tapes good
    exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
      vertex (ports j) (direction j) tapes suffix good
  · intro j _ localLabels localExit atLocal tapes good
    exact PoweringMachineRowBody.rowTrace graph n placement distinct output outside vertex
      (ports j) (direction j) localLabels localExit program atLocal tapes suffix good
  · exact atLabels
  · exact ready

theorem vertexTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n]
      (some ⟨entry d n labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩ := by
  have h := sequenceTrace graph n placement distinct output outside vertex (commands d n)
    labels exit program atLabels base suffix ready
  rw [sequenceSteps_eq] at h
  exact h

theorem sequenceTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    sequenceTapes graph n placement output vertex ops base output =
      ops.reverse.flatMap (rowBits graph n vertex) ++ base output := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      have nextReady := PoweringMachineRowBody.finalTapes_ready graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) output = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineRowBody.finalTapes_output graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, rowBits]

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex base output =
      PoweringTableLayout.vertexRowBits graph n vertex ++ base output := by
  rw [finalTapes, sequenceTapes_output graph n placement distinct output outside vertex
    (commands d n) base suffix ready]
  simp only [commands, List.reverse_reverse, rows_eq_vertexRowBits]

end BinPackingGames.Foundations.Complexity.PoweringMachineVertex

namespace BinPackingGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

theorem steps_le (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    steps graph n remaining bounded ≤
      remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1 := by
  induction remaining with
  | zero => simp [steps]
  | succ r ih =>
      have hv := PoweringMachineVertex.steps_le graph (⟨r, by omega⟩ : Fin vertices) n
      have hi := ih (by omega)
      simp only [steps, Nat.add_mul, Nat.one_mul]
      omega

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    finalTapes graph n placement output remaining bounded base output =
      prefixRows graph n remaining ++ base output := by
  induction remaining generalizing base with
  | zero =>
      exact MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _)
        base 0 []
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      have vertexReady := ready_vertex graph n placement distinct base ready vertex
      have nextReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      change finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output vertex current) output = _
      rw [ih (by omega) _ (ready_of_vertex graph n placement _ vertex nextReady),
        PoweringMachineVertex.finalTapes_output graph n placement distinct output outside
          vertex current [] vertexReady]
      have hc : current output = base output :=
        MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _) base r []
      rw [hc, prefixRows, dite_eq_left vertex.isLt, List.append_assoc]

theorem loopTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    (advance (TM2.step program))^[steps graph n remaining bounded]
      (some ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩) =
      some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩ := by
  let initial := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  induction remaining generalizing base with
  | zero =>
      simpa only [steps, finalTapes, counter, initial, PoweringMasterState.clean,
        PoweringMasterState.withBuffer] using
        MachineUnaryCounter.guardTrace_zero (placement (.inl 1)) guardLabel bridgeLabel exitLabel
          program atGuard base [] initial.1 none
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      let next := PoweringMachineVertex.finalTapes graph n placement output vertex current
      have vertexReady : PoweringMachineRowBody.Ready graph n placement vertex [] current :=
        ready_vertex graph n placement distinct base ready vertex
      have nextVertexReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      have nextReady : Ready graph n placement next :=
        ready_of_vertex graph n placement next vertex nextVertexReady
      have sameCounter : counter placement next r = next := by
        have hs := nextVertexReady.1.source
        change next (placement (.inl 1)) = encodeWord r ++ [] at hs
        unfold counter MachineUnaryCounter.counterTapes
        rw [← hs]
        exact Function.update_eq_self _ _
      have tailRun := ih (by omega) next nextReady
      rw [sameCounter] at tailRun
      have guardRun : advance (TM2.step program)
          (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) =
          some ⟨some bridgeLabel, initial, current⟩ := by
        simpa only [advance_some, current, counter, initial, PoweringMasterState.clean,
          PoweringMasterState.withBuffer] using
          MachineUnaryCounter.guardStep_succ (placement (.inl 1)) guardLabel bridgeLabel exitLabel
            program atGuard base r [] initial.1 none
      have bridgeRun : advance (TM2.step program)
          (some ⟨some bridgeLabel, initial, current⟩) =
          some ⟨PoweringMachineVertex.entry d n labels (some guardLabel), initial, current⟩ := by
        change some (TM2.stepAux (program bridgeLabel) initial current) = _
        rw [atBridge, vertexEntry]
        rfl
      have vertexRun := PoweringMachineVertex.vertexTrace graph n placement distinct output outside
        vertex labels (some guardLabel) program atVertex current [] vertexReady
      change (advance (TM2.step program))^[2 + PoweringMachineVertex.steps graph vertex n +
          steps graph n r (by omega)]
        (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) = _
      rw [show 2 + PoweringMachineVertex.steps graph vertex n + steps graph n r (by omega) =
          (steps graph n r (by omega) + PoweringMachineVertex.steps graph vertex n) + 1 + 1 by omega,
        Function.iterate_succ_apply, guardRun, Function.iterate_succ_apply, bridgeRun,
        Function.iterate_add_apply, vertexRun]
      exact tailRun

def loopInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩
      (some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩)
      (remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1) where
  steps := steps graph n remaining bounded
  evals_in_steps := loopTrace graph n placement distinct output outside guardLabel bridgeLabel
    exitLabel labels program atGuard atBridge atVertex remaining bounded base ready
  steps_le_m := steps_le graph n remaining bounded

end BinPackingGames.Foundations.Complexity.PoweringMachineOuterLoop

namespace BinPackingGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

end BinPackingGames.Foundations.Complexity.PoweringMachineGlobal

namespace BinPackingGames.Foundations.Complexity.PoweringInitializeFrame

open Turing PCP

variable {vertices d : Nat}

def initialExtra (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n) → List Bool :=
  fun tape => if tape = .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))
    then PortTables.tableBits graph else []

@[simp] theorem initialExtra_table (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n (.inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) =
      PortTables.tableBits graph := by simp [initialExtra]

@[simp] theorem initialExtra_scratch (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n
      (.inl (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n))) = [] := by
  simp [initialExtra, PoweringMachineTapes.table, PoweringMachineTapes.scratch]

def preparedTapes (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineGlobal.Tape n → List Bool :=
  PoweringMachineInitialize.mergeTapes
    (PoweringMachineLoop.finalTapes (PoweringTableLayout.blockSize d n) vertices [])
    (initialExtra graph n)

theorem prepared_commonRole (graph : PortTables.Table vertices d) (n : Nat)
    (j : Fin 11) (hne : j ≠ 1) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl j)) =
      if j = 0 then PortTables.tableBits graph else [] := by
  simp [preparedTapes, PoweringMachineGlobal.placement,
    PoweringMachineInitialize.commonPlacement, PoweringMachineTapes.start,
    PoweringMachineInitialize.mergeTapes, initialExtra, PoweringMachineTapes.table, hne]

theorem prepared_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) := by
  constructor
  · simpa using prepared_commonRole graph n 0 (by decide)
  · simpa using prepared_commonRole graph n 5 (by decide)
  · simpa using prepared_commonRole graph n 8 (by decide)
  · simpa using prepared_commonRole graph n 9 (by decide)
  · simpa using prepared_commonRole graph n 10 (by decide)

@[simp] theorem prepared_start (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl 1)) =
      encodeWord vertices := by
  simpa only [preparedTapes, PoweringMachineGlobal.placement, PoweringMachineTapes.start] using
    PoweringMachineInitialize.final_counter (PoweringMachineRowBody.capacity n)
      (PoweringTableLayout.blockSize d n) vertices (initialExtra graph n)

theorem prepared_counter (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.counter (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) vertices = preparedTapes graph n := by
  unfold PoweringMachineOuterLoop.counter MachineUnaryCounter.counterTapes
  rw [List.append_nil, ← prepared_start graph n]
  simp only [Function.update_eq_self]

@[simp] theorem prepared_output (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.outputTape n) = [] := by
  simp [preparedTapes, PoweringMachineGlobal.outputTape, PoweringMachineInitialize.finalOutput,
    PoweringMachineInitialize.mergeTapes, initialExtra]

@[simp] theorem prepared_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerVertices n) = encodeWord vertices := rfl

@[simp] theorem prepared_darts (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := rfl

@[simp] theorem prepared_source (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (.inl PoweringMachineLoop.HeaderTape.source) = [] := rfl

def preparedCfg (graph : PortTables.Table vertices d) (n : Nat) :
    (PoweringMachineGlobal.machine d n).Cfg :=
  ⟨some (PoweringMachineGlobal.guardLabel d n),
    PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), preparedTapes graph n⟩

theorem initialGlobalTapes_eq (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n) =
      fun tape => if tape = PoweringMachineGlobal.inputTape n
        then PortTables.tableBits graph else [] := by
  funext tape
  cases tape with
  | inl field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table]
  | inr field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table, initialExtra]

theorem machine_initialStacks (d n : Nat) (input : List Bool) :
    (initList (PoweringMachineGlobal.machine d n) input).stk =
      fun tape => if tape = PoweringMachineGlobal.inputTape n then input else [] := by
  simp only [PoweringMachineGlobal.machine]
  rfl

theorem initList_eq (graph : PortTables.Table vertices d) (n : Nat) :
    initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph) =
      ⟨some (PoweringMachineGlobal.main d n),
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n)⟩ := by
  have ht := (machine_initialStacks d n (PortTables.tableBits graph)).trans
    (initialGlobalTapes_eq graph n).symm
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem tableBits_head (graph : PortTables.Table vertices d) :
    PortTables.tableBits graph = encodeWord vertices ++
      encodeWords (PortTables.tableWords graph).tail := rfl

def initializeInTime (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d n).step
      (initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph))
      (some (preparedCfg graph n)) (3 * vertices + 5) := by
  rw [initList_eq]
  exact PoweringMachineInitialize.initializeAtInTime
    (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
    (PoweringTableLayout.blockSize d n) vertices
    (PoweringMachineGlobal.initLabels d n) (some (PoweringMachineGlobal.guardLabel d n))
    (PoweringMachineGlobal.program d n) (PoweringMachineGlobal.atInit d n)
    (initialExtra graph n) (encodeWords (PortTables.tableWords graph).tail)
    (by rw [initialExtra_table, tableBits_head]) (initialExtra_scratch graph n)
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n))

end BinPackingGames.Foundations.Complexity.PoweringInitializeFrame

namespace BinPackingGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem headerVertices_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerVertices n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .vertices (by decide))

theorem headerDarts_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerDarts n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .darts (by decide))

theorem headerVertices_ne_output (n : Nat) : headerVertices n ≠ outputTape n := by
  simp [headerVertices, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerDarts_ne_output (n : Nat) : headerDarts n ≠ outputTape n := by
  simp [headerDarts, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerVertices_ne_scratch (n : Nat) :
    headerVertices n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerVertices_ne_placement n _

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

theorem haltList_tapes (d n : Nat) (output : List Bool) :
    (Turing.haltList (machine d n) output).stk =
      MachineDrainMany.haltTapes (outputTape n) output := by
  rfl

theorem haltList_eq (d n : Nat) (output : List Bool) :
    Turing.haltList (machine d n) output =
      (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        MachineDrainMany.haltTapes (outputTape n) output⟩ : (machine d n).Cfg) := by
  change (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      (Turing.haltList (machine d n) output).stk⟩ : (machine d n).Cfg) = _
  exact congrArg
    (fun tapes => (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      tapes⟩ : (machine d n).Cfg)) (haltList_tapes d n output)

end BinPackingGames.Foundations.Complexity.PoweringGlobalConfiguration

namespace BinPackingGames.Foundations.Complexity.PoweringRuntimeBudget

open Turing

abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

theorem finish_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3) := by
  exact PoweringMachineFinish.steps_le_uniform (PoweringMachineGlobal.enumeration radius)
    (PoweringMachineGlobal.outputTape radius) before.stk vertices darts
    (input.length + priorBudget * Runtime.programPushBound (PoweringMachineGlobal.machine d radius))
    (stackLength_le_from_input (PoweringMachineGlobal.machine d radius) input before priorBudget prior)

end BinPackingGames.Foundations.Complexity.PoweringRuntimeBudget

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

def beforeFinish (graph : PortTables.Table vertices d) (n : Nat) : Tape n → List Bool :=
  PoweringMachineOuterLoop.finalTapes graph n (placement n) (outputTape n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)

def finishConfiguration (graph : PortTables.Table vertices d) (n : Nat) : (machine d n).Cfg :=
  ⟨some (finishEntry d n), PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
    beforeFinish graph n⟩

def beforeFinishBudget (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  (3 * vertices + 5) + (vertices *
    (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)

theorem beforeFinish_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (placement n) (beforeFinish graph n) :=
  PoweringMachineOuterLoop.finalTapes_ready graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _)
    (outputTape n) (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)

theorem beforeFinish_output (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (outputTape n) =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_output graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n),
    PoweringMachineOuterLoop.prefixRows_all, PoweringInitializeFrame.prepared_output,
    List.append_nil]

theorem beforeFinish_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerVertices n) = encodeWord vertices := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerVertices n) (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .vertices (by decide)))]
  exact PoweringInitializeFrame.prepared_vertices graph n

theorem beforeFinish_darts (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerDarts n) (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .darts (by decide)))]
  exact PoweringInitializeFrame.prepared_darts graph n

theorem serialized_eq (graph : PortTables.Table vertices d) (n : Nat) :
    encodeWords [vertices, PoweringTableLayout.blockSize d n * vertices] ++
      beforeFinish graph n (outputTape n) = PoweringTables.outputBits graph n := by
  rw [beforeFinish_output, PoweringTableLayout.outputBits_vertexRows]
  congr 2
  rw [PoweringTableLayout.dartCount_eq_vertex_blocks, Nat.mul_comm]

def beforeFinishExecution (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (machine d n).step
      (initList (machine d n) (PortTables.tableBits graph))
      (some (finishConfiguration graph n)) (beforeFinishBudget graph n) := by
  have initialRun := PoweringInitializeFrame.initializeInTime graph n
  have loop := PoweringMachineOuterLoop.loopInTime graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    (guardLabel d n) (bridgeLabel d n) (finishEntry d n) (vertexLabels d n)
    (program d n) (atGuard d n) (atBridge d n) (atVertex d n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)
  rw [PoweringInitializeFrame.prepared_counter] at loop
  simpa only [beforeFinishBudget, Nat.add_comm] using
    (StateTransition.EvalsToInTime.trans (machine d n).step
    (3 * vertices + 5)
    (vertices * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)
    (initList (machine d n) (PortTables.tableBits graph))
    (PoweringInitializeFrame.preparedCfg graph n) (some (finishConfiguration graph n))
    initialRun loop)

def finishSteps (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  PoweringMachineFinish.steps (enumeration n) (outputTape n) (beforeFinish graph n)
    vertices (PoweringTableLayout.blockSize d n * vertices)

def finishExecution (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (machine d n).step (finishConfiguration graph n)
      (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
      (finishSteps graph n) := by
  have run := PoweringMachineFinish.traceAt (enumeration n)
    (headerVertices n) (headerDarts n) (outputTape n)
    (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
    (PoweringGlobalConfiguration.headerVertices_ne_scratch n)
    (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (PoweringGlobalConfiguration.headerDarts_ne_scratch n)
    (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ _)
    (finishLabels d n) (program d n) (atFinish d n)
    (beforeFinish graph n) vertices (PoweringTableLayout.blockSize d n * vertices) [] []
    (by simpa only [List.append_nil] using beforeFinish_vertices graph n)
    (by simpa only [List.append_nil] using beforeFinish_darts graph n)
    (beforeFinish_ready graph n).scratch
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)).1 none
  rw [serialized_eq] at run
  refine { steps := finishSteps graph n, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
  change (advance (TM2.step (program d n)))^[finishSteps graph n]
    (some (finishConfiguration graph n)) = _
  rw [PoweringGlobalConfiguration.haltList_eq]
  simpa only [finishConfiguration, finishEntry, finishSteps, PoweringMasterState.clean,
    PoweringMasterState.withBuffer] using! run

def execution (graph : PortTables.Table vertices d) (n : Nat) :
    TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
      (some (PoweringTables.outputBits graph n))
      (beforeFinishBudget graph n + finishSteps graph n) := by
  simpa only [TM2OutputsInTime, Option.map_some, Nat.add_comm] using!
    (StateTransition.EvalsToInTime.trans (machine d n).step
    (beforeFinishBudget graph n) (finishSteps graph n)
    (initList (machine d n) (PortTables.tableBits graph))
    (finishConfiguration graph n)
    (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
    (beforeFinishExecution graph n) (finishExecution graph n))

theorem finishSteps_le (graph : PortTables.Table vertices d) (n : Nat) :
    finishSteps graph n ≤
      2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
      PoweringRuntimeBudget.tapeCount n *
        ((PortTables.tableBits graph).length + beforeFinishBudget graph n *
          Runtime.programPushBound (machine d n) + vertices +
          PoweringTableLayout.blockSize d n * vertices + 3) :=
  PoweringRuntimeBudget.finish_steps_le_of_execution d n (PortTables.tableBits graph)
    (finishConfiguration graph n) (beforeFinishBudget graph n) vertices
    (PoweringTableLayout.blockSize d n * vertices) (beforeFinishExecution graph n)

theorem execution_budget_le (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinishBudget graph n + finishSteps graph n ≤
      (PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
        (PoweringRuntimeBudget.tapeCount n)).eval (PortTables.tableBits graph).length := by
  exact PoweringPolynomialBudget.execution_budget_le_time d n
    (Runtime.programPushBound (machine d n)) (PoweringRuntimeBudget.tapeCount n)
    vertices (PortTables.tableBits graph).length (PortTables.vertices_le_tableBits_length graph)
    (Nat.le_refl _) (finishSteps_le graph n)

noncomputable def computableInPolyTime (d n : Nat) :
    TM2ComputableInPolyTime (@PortTables.inputBits d) GenericGraphTables.tableBits
      (PoweringTables.transform d n) where
  tm := machine d n
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
    (PoweringRuntimeBudget.tapeCount n)
  outputsFun input := by
    rcases input with ⟨vertices, graph⟩
    have run := execution graph n
    let bounded : TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
        (some (PoweringTables.outputBits graph n))
        ((PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
          (PoweringRuntimeBudget.tapeCount n)).eval (PortTables.tableBits graph).length) :=
      ⟨run.toEvalsTo, run.steps_le_m.trans (execution_budget_le graph n)⟩
    change TM2OutputsInTime (machine d n) ((PortTables.tableBits graph).map id)
      (some ((PoweringTables.outputBits graph n).map id)) _
    have input_eq : @List.map ((machine d n).Γ (machine d n).k₀)
        ((machine d n).Γ (machine d n).k₀) id (PortTables.tableBits graph) =
          PortTables.tableBits graph := List.map_id _
    have output_eq : @List.map ((machine d n).Γ (machine d n).k₁)
        ((machine d n).Γ (machine d n).k₁) id (PoweringTables.outputBits graph n) =
          PoweringTables.outputBits graph n := List.map_id _
    simpa only [input_eq, output_eq, PortTables.inputBits] using bounded

end BinPackingGames.Foundations.Complexity.PoweringMachineRuntime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem prepared_count (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 3) = encodeWord 0 := by
  simp [prepared, copied, p.injective.eq_iff, ready.count, encodeWord]

theorem prepared_cursor (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 4) = encodeWord 0 := by
  simp [prepared, copied, p.injective.eq_iff, ready.cursor, encodeWord]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

open Turing

@[simp] theorem bootstrapPrepared_current (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (current V) =
      encodeWord (2 * V.witnessBound.eval input.length + 1) :=
  ProducerBootstrap.prepared_current (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

@[simp] theorem bootstrapPrepared_count (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (count V) = encodeWord 0 :=
  ProducerBootstrap.prepared_count (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

@[simp] theorem bootstrapPrepared_cursor (V : NPVerifier) (input : List Bool) :
    bootstrapPrepared V input (cursor V) = encodeWord 0 :=
  ProducerBootstrap.prepared_cursor (bootstrapPorts V) (frontendPrepared V input) _
    (bootstrapReady V input)

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs

open ProducerInvariant ProducerArena

def localBase (V : NPVerifier) (input : List Bool) : TransitionArena.Tape → List Bool :=
  fun t => bootstrapPrepared V input (transitionPorts V t)

def boundary (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) : Tape V → List Bool :=
  ForestPlacement.fill (transitionPorts V) (bootstrapPrepared V input)
    (TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length) remaining s)

def finished (V : NPVerifier) (input : List Bool) (s : Snapshot) : Tape V → List Bool :=
  ForestPlacement.fill (transitionPorts V) (bootstrapPrepared V input)
    (TransitionArena.finishTapes (localBase V input) (VerifierCircuit.capacity V input.length) s)

theorem finished_other (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (k : Tape V) (outside : ∀ t, transitionPorts V t ≠ k) :
    finished V input s k = bootstrapPrepared V input k :=
  ForestPlacement.fill_other _ _ _ k outside

@[simp] theorem boundary_current (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (current V) = s.currentBits := by
  change ForestPlacement.fill (transitionPorts V) _ _
    (transitionPorts V (.inl (.lower .current))) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem boundary_roots (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (roots V) = s.rootBits := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .rootTable)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem boundary_records (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (records V) = s.reversedRecords := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .records)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem boundary_countdown (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (countdown V) = encodeWord remaining := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .countdown)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_current (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (current V) = s.currentBits := by
  change ForestPlacement.fill (transitionPorts V) _ _
    (transitionPorts V (.inl (.lower .current))) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_roots (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (roots V) = s.rootBits := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .rootTable)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_records (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (records V) = s.reversedRecords := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inl .records)) = _
  rw [ForestPlacement.fill_at]
  rfl

@[simp] theorem finished_countdown (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (countdown V) = [] := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .countdown)) = _
  rw [ForestPlacement.fill_at]
  simp [TransitionArena.finishTapes]

theorem bootstrap_clock (V : NPVerifier) (input : List Bool) (c : ClockPreparation.Clock) :
    bootstrapPrepared V input (clock V c) = encodeWord (ClockPreparation.clockValue V input.length c) := by
  change bootstrapPrepared V input (frontPorts V (VerifierFront.clockTape V c)) = _
  rw [bootstrapPrepared_front]
  exact VerifierFront.prepared_clock V input c

@[simp] theorem boundary_q (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (q V) = encodeWord (V.witnessBound.eval input.length) := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .q)) = _
  rw [ForestPlacement.fill_at]
  exact bootstrap_clock V input .witness

@[simp] theorem boundary_capacity (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    boundary V input remaining s (capacity V) = encodeWord (VerifierCircuit.capacity V input.length) := by
  change ForestPlacement.fill (transitionPorts V) _ _ (transitionPorts V (.inr .capacity)) = _
  rw [ForestPlacement.fill_at]
  rfl

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Initialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | _ => []

end BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSourceHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing BinPackingGames.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def computableInPolyTime (H : PreprocessingTables.BaseTable)
    (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * (d + internalDegree))) (finish H d) := by
  change TM2ComputableInPolyTime _ _
    (fun input => PreprocessingStageMaps.lazy (d + internalDegree)
      (PreprocessingStageMaps.paddedOverlay H d input))
  exact MachineSequential.composeBits (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))

end BinPackingGames.Foundations.PCP.PreprocessingFinishRuntime

namespace BinPackingGames.Foundations.PCP.PreprocessingRuntime
open Turing BinPackingGames.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def tablePolynomialTime (H : PreprocessingTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingTables.degree))
      (PreprocessingTables.output H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := 2 * ((internalDegree + 1) + internalDegree)))
    (fun t => PreprocessingFinishRuntime.finish H (internalDegree + 1)
      (PreprocessingStageMaps.regular H t))
  exact MachineSequential.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end BinPackingGames.Foundations.PCP.PreprocessingRuntime

namespace BinPackingCompleteness.PreprocessingMachine

open Turing BinPackingGames.Foundations
open Complexity PCP Target

def preprocessing : RoundComputation.PreprocessingCertificate PCPSource.baseTable :=
  PreprocessingRuntime.tablePolynomialTime PCPSource.baseTable

end BinPackingCompleteness.PreprocessingMachine

end

end OAI
end


